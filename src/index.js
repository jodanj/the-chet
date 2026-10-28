/**
 * The Chet - Cloudflare Worker + Durable Object chat server.
 *
 * Secrets (set with `npx wrangler secret put NAME`, or in .dev.vars for local dev):
 *   OWNER_PASSWORD, ADMIN_PASSWORD, VIP_PASSWORD, GIPHY_API_KEY
 * A role is granted when the password typed into the login form matches one of them.
 * If a secret is not set, that role simply cannot be obtained.
 * GIPHY_API_KEY (free at developers.giphy.com) powers the GIF button.
 *
 * Custom rooms: any channel named "room:<code>" is a private room. Only sockets that
 * have sent `joinRoom` for that code can read it, post in it, or receive its events.
 */

const CHANNELS = ['general', 'gaming', 'memes', 'proxy'];
const VOICE_CHANNELS = ['general', 'chill', 'gaming'];
const COLORS = ['default', 'red', 'orange', 'yellow', 'green', 'blue', 'purple', 'pink'];
const EFFECTS = new Set([
  'spinScreen', 'shakeScreen', 'flipScreen', 'invertColors', 'rainbow',
  'blur', 'matrix', 'emojiSpam', 'confetti', 'rickRoll'
]);

const MAX_CHANNEL_HISTORY = 100;
const MAX_DM_HISTORY = 200;
const MAX_TEXT = 2000;
const MAX_IMAGE_CHARS = 700000;  // ~500 KB image as base64 (SQLite-backed objects store values up to 2 MB)
const MAX_FRAME_CHARS = 1000000; // WebSocket messages are capped at 1 MiB

// Only GIPHY links (from the GIF picker) are accepted as remote images.
const GIF_URL_RE = /^https:\/\/(?:media\d*|i)\.giphy\.com\/[\w\-./%]+(?:\?[\w\-=&%.]*)?$/;

// Auto slow mode: 9+ messages in 3 seconds -> one message per 3 seconds for 5 minutes.
const SPAM_MESSAGES = 9, SPAM_WINDOW_MS = 3000;
const AUTO_SLOW_MS = 5 * 60 * 1000, AUTO_SLOW_GAP_MS = 3000;

const MAX_BLOCKS = 100;
const BAN_MODES = ['full', 'mute', 'dm'];

const ROOM_RE = /^room:[a-z0-9-]{3,20}$/;
const MAX_ROOMS_PER_USER = 10;
const MAX_ROOMS_TOTAL = 200;

const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const EMOJI_RE = /^\P{ASCII}{1,10}$/u;

// ---------- helpers ----------

const send = (ws, data) => {
  try { ws.send(JSON.stringify(data)); } catch { /* socket already closed */ }
};
const bg = (promise) => promise.catch((err) => console.error('storage error:', err));
const lc = (s) => String(s).toLowerCase();
const pad = (n) => String(n).padStart(15, '0');
const chKey = (m) => `ch:${m.channel}:${pad(m.timestamp)}-${m.id}`;
const dmKey = (m) => `dm:${m.chatId}:${pad(m.timestamp)}-${m.id}`;

const clamp = (n, lo, hi, fallback) => {
  n = Number(n);
  if (!Number.isFinite(n)) return fallback;
  return Math.min(hi, Math.max(lo, Math.floor(n)));
};

function cleanName(v) {
  return String(v ?? '')
    .replace(/[\u0000-\u001f\u007f<>]/g, '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 30);
}

function cleanReason(v) {
  return typeof v === 'string' ? v.replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, 200) : '';
}

// Room codes: lowercase letters, digits and dashes, 3-20 long (anything else is stripped).
const normRoom = (v) => String(v ?? '').toLowerCase().replace(/[^a-z0-9-]/g, '').slice(0, 20);
const isRoomChannel = (c) => typeof c === 'string' && ROOM_RE.test(c);
const validChannel = (c) => typeof c === 'string' && (CHANNELS.includes(c) || ROOM_RE.test(c));

// Constant-time string comparison. An unset/empty secret never matches.
function safeEqual(input, secret) {
  if (typeof input !== 'string' || typeof secret !== 'string' || !secret) return false;
  const enc = new TextEncoder();
  const a = enc.encode(input);
  const b = enc.encode(secret);
  let diff = a.length ^ b.length;
  const n = Math.max(a.length, b.length);
  for (let i = 0; i < n; i++) diff |= (a[i] ?? 0) ^ (b[i] ?? 0);
  return diff === 0;
}

const roleOf = (u) => (u.isOwner ? 'owner' : u.isAdmin ? 'admin' : u.isVIP ? 'vip' : null);
const isStaff = (u) => !!(u && (u.isAdmin || u.isOwner));

// ---------- Durable Object ----------

export class ChatRoom {
  constructor(ctx, env) {
    this.ctx = ctx;
    this.env = env;

    this.channels = Object.fromEntries(CHANNELS.map((c) => [c, []])); // also holds "room:<code>" lists
    this.privateChats = new Map();    // chatId -> message[]
    this.dmParticipants = new Map();  // chatId -> [{ uuid, username }, { uuid, username }]
    this.bannedUsers = new Set();     // lowercase usernames
    this.bannedIPs = new Set();
    this.userWarnings = new Map();    // lowercase username -> count
    this.userProfiles = new Map();    // lowercase username -> { color }
    this.slowMode = { enabled: false, duration: 5 };
    this.restrictedIPs = new Map();   // ip -> 'mute' | 'dm'
    this.restrictedUsers = new Map(); // lowercase username -> 'mute' | 'dm'
    this.blocks = new Map();          // blocker uuid -> Map(blocked uuid -> username)

    // Short-lived state: fine to lose when the object hibernates.
    this.lastMessageAt = new Map();   // lowercase username -> ms
    this.mutedUntil = new Map();      // lowercase username -> ms
    this.recentMsgs = new Map();      // lowercase username -> [timestamps]
    this.autoSlowUntil = new Map();   // lowercase username -> ms
    this.lastTs = 0;

    // Load persisted state before any request is handled.
    ctx.blockConcurrencyWhile(() => this.load());
  }

  // ----- persistence -----

  async load() {
    const meta = await this.ctx.storage.get('meta');
    if (meta) {
      this.bannedUsers = new Set(meta.bannedUsers || []);
      this.bannedIPs = new Set(meta.bannedIPs || []);
      this.userWarnings = new Map(Object.entries(meta.userWarnings || {}));
      this.userProfiles = new Map(Object.entries(meta.userProfiles || {}));
      this.dmParticipants = new Map(Object.entries(meta.dmParticipants || {}));
      this.restrictedIPs = new Map(Object.entries(meta.restrictedIPs || {}));
      this.restrictedUsers = new Map(Object.entries(meta.restrictedUsers || {}));
      this.blocks = new Map(Object.entries(meta.blocks || {}).map(([k, o]) => [k, new Map(Object.entries(o))]));
      if (meta.slowMode) this.slowMode = meta.slowMode;
    }

    // list() returns keys in ascending order, and keys embed a zero-padded timestamp.
    for (const m of (await this.ctx.storage.list({ prefix: 'ch:' })).values()) {
      const list = this.chanList(m.channel, true);
      if (list) list.push(m);
    }
    for (const m of (await this.ctx.storage.list({ prefix: 'dm:' })).values()) {
      if (!this.privateChats.has(m.chatId)) this.privateChats.set(m.chatId, []);
      this.privateChats.get(m.chatId).push(m);
    }
  }

  saveMeta() {
    bg(this.ctx.storage.put('meta', {
      bannedUsers: [...this.bannedUsers],
      bannedIPs: [...this.bannedIPs],
      userWarnings: Object.fromEntries(this.userWarnings),
      userProfiles: Object.fromEntries(this.userProfiles),
      dmParticipants: Object.fromEntries(this.dmParticipants),
      restrictedIPs: Object.fromEntries(this.restrictedIPs),
      restrictedUsers: Object.fromEntries(this.restrictedUsers),
      blocks: Object.fromEntries([...this.blocks].map(([k, m]) => [k, Object.fromEntries(m)])),
      slowMode: this.slowMode
    }));
  }

  nextTimestamp() {
    this.lastTs = Math.max(Date.now(), this.lastTs + 1);
    return this.lastTs;
  }

  // ----- channel / room helpers -----

  // Message list for a channel. Rooms are created on demand when `create` is true.
  chanList(channel, create = false) {
    if (!validChannel(channel)) return null;
    if (!this.channels[channel] && create && isRoomChannel(channel)) this.channels[channel] = [];
    return this.channels[channel] || null;
  }

  // Built-in channels are open to everyone; rooms only to sockets that joined them.
  canAccessChannel(user, channel) {
    if (CHANNELS.includes(channel)) return true;
    return isRoomChannel(channel) && (user.rooms || []).includes(channel.slice(5));
  }

  roomUsers(code) {
    return this.joinedSockets().filter(([, u]) => (u.rooms || []).includes(code)).map(([, u]) => u.username);
  }

  roomCount() {
    return Object.keys(this.channels).filter((k) => k.startsWith('room:')).length;
  }

  // Drop rooms that are empty and have nobody in them (they hold no stored data).
  pruneRooms() {
    for (const [k, list] of Object.entries(this.channels)) {
      if (k.startsWith('room:') && !list.length && !this.roomUsers(k.slice(5)).length) delete this.channels[k];
    }
  }

  // Sends to everyone for built-in channels, or only to room members for rooms.
  broadcastChannel(channel, data, exceptWs = null) {
    if (!isRoomChannel(channel)) return this.broadcast(data, exceptWs);
    const code = channel.slice(5);
    const payload = JSON.stringify(data);
    for (const [ws, u] of this.joinedSockets()) {
      if (ws === exceptWs || !(u.rooms || []).includes(code)) continue;
      try { ws.send(payload); } catch { /* ignore */ }
    }
  }

  broadcastRoomUsers(code) {
    this.broadcastChannel('room:' + code, { type: 'roomUsers', code, users: this.roomUsers(code) });
  }

  // ----- WebSocket entry points -----

  async fetch(request) {
    if (request.headers.get('Upgrade') !== 'websocket') {
      return new Response('Expected WebSocket request', { status: 426 });
    }

    const ip = request.headers.get('cf-connecting-ip') || 'unknown';
    const [client, server] = Object.values(new WebSocketPair());

    if (this.bannedIPs.has(ip)) {
      // Short-lived socket: tell the client why, then hang up.
      server.accept();
      server.send(JSON.stringify({ type: 'banned', message: 'You are banned from this server (IP ban)' }));
      server.close(4003, 'banned');
      return new Response(null, { status: 101, webSocket: client });
    }

    // Hibernatable socket: the object can be evicted while connections stay open.
    this.ctx.acceptWebSocket(server);
    server.serializeAttachment({ ip });
    return new Response(null, { status: 101, webSocket: client });
  }

  async webSocketMessage(ws, raw) {
    if (typeof raw !== 'string' || raw.length > MAX_FRAME_CHARS) return;
    let data;
    try { data = JSON.parse(raw); } catch { return; }
    if (!data || typeof data !== 'object' || typeof data.type !== 'string') return;
    try {
      this.dispatch(ws, data);
    } catch (err) {
      console.error('Error handling', data.type, err);
    }
  }

  async webSocketClose(ws, code) {
    const user = ws.deserializeAttachment();
    const closeCode = code >= 1000 && code < 5000 && ![1005, 1006, 1015].includes(code) ? code : 1000;
    try { ws.close(closeCode, 'closing'); } catch { /* already closed */ }

    if (user && user.username) {
      if (user.voice) {
        this.broadcast({ type: 'voiceUserLeft', username: user.username, channel: user.voice });
        this.broadcast({ type: 'voiceUsers', channel: user.voice, users: this.voiceUsers(user.voice) });
      }
      for (const code of user.rooms || []) this.broadcastRoomUsers(code);
      this.broadcast({ type: 'userList', users: this.getUserList() });
    }
  }

  async webSocketError(ws, error) {
    console.error('WebSocket error:', error);
  }

  // ----- socket helpers -----

  openSockets() {
    return this.ctx.getWebSockets().filter((ws) => ws.readyState === 1);
  }

  // [ws, attachment] for every socket that has completed the join handshake.
  joinedSockets() {
    const out = [];
    for (const ws of this.openSockets()) {
      const u = ws.deserializeAttachment();
      if (u && u.username) out.push([ws, u]);
    }
    return out;
  }

  broadcast(data, exceptWs = null) {
    const payload = JSON.stringify(data);
    for (const [ws] of this.joinedSockets()) {
      if (ws === exceptWs) continue;
      try { ws.send(payload); } catch { /* ignore */ }
    }
  }

  sendToUuids(uuids, data) {
    const payload = JSON.stringify(data);
    for (const [ws, u] of this.joinedSockets()) {
      if (uuids.includes(u.uuid)) {
        try { ws.send(payload); } catch { /* ignore */ }
      }
    }
  }

  findUser(username) {
    const name = lc(username ?? '');
    for (const [ws, user] of this.joinedSockets()) {
      if (lc(user.username) === name) return { ws, user };
    }
    return null;
  }

  getUserList() {
    return this.joinedSockets()
      .map(([, u]) => ({ username: u.username, isOwner: !!u.isOwner, isAdmin: !!u.isAdmin, isVIP: !!u.isVIP }))
      .sort((a, b) => a.username.localeCompare(b.username));
  }

  voiceUsers(channel) {
    return this.joinedSockets().filter(([, u]) => u.voice === channel).map(([, u]) => u.username);
  }

  isParticipant(chatId, uuid) {
    const parts = typeof chatId === 'string' ? this.dmParticipants.get(chatId) : null;
    return !!parts && parts.some((p) => p.uuid === uuid);
  }

  canModerate(moderator, target) {
    if (target.isOwner) return false;
    if (moderator.isOwner) return true;
    return !!(moderator.isAdmin && !target.isAdmin);
  }

  // Returns the online target if `admin` is allowed to act on them, else tells the admin why.
  modTarget(ws, admin, username) {
    const t = this.findUser(username);
    if (!t) {
      send(ws, { type: 'error', message: 'User not online' });
      return null;
    }
    if (!this.canModerate(admin, t.user)) {
      send(ws, { type: 'error', message: 'Cannot moderate this user' });
      return null;
    }
    return t;
  }

  // ----- dispatch -----

  dispatch(ws, data) {
    const user = ws.deserializeAttachment() || {};

    if (data.type === 'join') return this.onJoin(ws, data, user);
    if (!user.username) return; // everything else requires a completed join

    if (data.type.startsWith('admin') && !isStaff(user)) return;

    switch (data.type) {
      case 'message': return this.onMessage(ws, data, user);
      case 'privateMessage': return this.onPrivateMessage(ws, data, user);
      case 'privateChatRequest': return this.onPrivateChatRequest(ws, data, user);
      case 'privateChatResponse': return this.onPrivateChatResponse(ws, data, user);
      case 'getHistory': return this.onGetHistory(ws, data, user);
      case 'getPrivateHistory': return this.onGetPrivateHistory(ws, data, user);
      case 'toggleReaction': return this.onToggleReaction(data, user);
      case 'typing': return this.onTyping(ws, data, user);
      case 'updateProfile': return this.onUpdateProfile(data, user);
      case 'deleteMessage': return this.onDeleteMessage(ws, data, user);
      case 'blockUser': return this.onBlockUser(ws, data, user);
      case 'unblockUser': return this.onUnblockUser(ws, data, user);

      case 'joinRoom': return this.onJoinRoom(ws, data, user);
      case 'leaveRoom': return this.onLeaveRoom(ws, data, user);

      case 'joinVoice': return this.onJoinVoice(ws, data, user);
      case 'leaveVoice': return this.leaveVoice(ws, user);
      case 'voiceOffer': return this.relayVoice(user, data, 'voiceOffer', 'offer');
      case 'voiceAnswer': return this.relayVoice(user, data, 'voiceAnswer', 'answer');
      case 'voiceIceCandidate': return this.relayVoice(user, data, 'voiceIceCandidate', 'candidate');

      case 'adminKick': return this.onAdminKick(ws, data, user);
      case 'adminTimeout': return this.onAdminTimeout(ws, data, user, 'timedOut');
      case 'adminForceMute': return this.onAdminTimeout(ws, data, user, 'forceMute');
      case 'adminBan': return this.onAdminBan(ws, data, user);
      case 'adminUnban': return this.onAdminUnban(ws, data);
      case 'adminUnbanIP': return this.onAdminUnbanIP(ws, data);
      case 'adminUnrestrict': return this.onAdminUnrestrict(ws, data);
      case 'adminWarning': return this.onAdminWarning(ws, data, user);
      case 'adminDeleteMessage': return this.onAdminDeleteMessage(ws, data, user);
      case 'adminGetBanList': return this.onAdminGetBanList(ws);
      case 'adminBroadcast': return this.onAdminBroadcast(ws, data);
      case 'adminSlowMode': return this.onAdminSlowMode(ws, data);
      case 'adminClearChat': return this.onAdminClearChat(ws, data);
      case 'adminEffect': return this.onAdminEffect(ws, data, user);
      case 'adminConfetti': return this.onAdminConfettiAll(ws);
      case 'adminForceDisconnect': return this.onAdminForceDisconnect(ws, data, user);
    }
  }

  // ----- join -----

  reject(ws, type, message, code = 4001) {
    send(ws, { type, message });
    try { ws.close(code, type); } catch { /* ignore */ }
  }

  onJoin(ws, data, att) {
    if (att.username) return; // already joined on this socket

    const ip = att.ip || 'unknown';
    const name = cleanName(data.username);
    if (!name) return this.reject(ws, 'joinError', 'Choose a username');

    // Work out the role first: staff are immune to username bans.
    let isOwner = false;
    let isAdmin = false;
    let isVIP = false;
    const password = typeof data.password === 'string' ? data.password : '';
    if (password) {
      if (safeEqual(password, this.env.OWNER_PASSWORD)) { isOwner = true; isAdmin = true; }
      else if (safeEqual(password, this.env.ADMIN_PASSWORD)) isAdmin = true;
      else if (safeEqual(password, this.env.VIP_PASSWORD)) isVIP = true;
      else return this.reject(ws, 'joinError', 'Incorrect password');
    }

    if (!isAdmin && this.bannedUsers.has(lc(name))) {
      return this.reject(ws, 'banned', 'You are banned from this server', 4003);
    }

    // uuid is a secret the client keeps in localStorage; it identifies you across reconnects and DMs.
    const uuid = typeof data.uuid === 'string' && UUID_RE.test(data.uuid) ? data.uuid : crypto.randomUUID();

    let finalName = name;
    let staleVoice = null;
    let staleRooms = [];
    const clash = this.findUser(name);
    if (clash) {
      if (clash.user.uuid === uuid) {
        // Same person reconnecting before the old socket was noticed as dead: replace it.
        staleVoice = clash.user.voice;
        staleRooms = clash.user.rooms || [];
        clash.ws.serializeAttachment({ ip: clash.user.ip });
        try { clash.ws.close(4000, 'Replaced by a new connection'); } catch { /* ignore */ }
      } else if (/^guest$/i.test(name)) {
        do {
          finalName = `Guest${1000 + Math.floor(Math.random() * 9000)}`;
        } while (this.findUser(finalName));
      } else {
        return this.reject(ws, 'joinError', 'That username is already in use');
      }
    }

    ws.serializeAttachment({
      ip, uuid, username: finalName, isOwner, isAdmin, isVIP, voice: null, pending: [], rooms: []
    });

    send(ws, { type: 'joined', uuid, username: finalName, isOwner, isAdmin, isVIP });
    send(ws, { type: 'dmList', chats: this.dmListFor(uuid) });
    send(ws, { type: 'blockList', users: [...(this.blocks.get(uuid)?.values() || [])] });
    for (const ch of VOICE_CHANNELS) {
      send(ws, { type: 'voiceUsers', channel: ch, users: this.voiceUsers(ch) });
    }
    this.broadcast({ type: 'userList', users: this.getUserList() });
    if (staleVoice) {
      this.broadcast({ type: 'voiceUserLeft', username: finalName, channel: staleVoice });
      this.broadcast({ type: 'voiceUsers', channel: staleVoice, users: this.voiceUsers(staleVoice) });
    }
    for (const code of staleRooms) this.broadcastRoomUsers(code);
  }

  dmListFor(uuid) {
    const chats = [];
    for (const [chatId, parts] of this.dmParticipants) {
      if (!parts.some((p) => p.uuid === uuid)) continue;
      const other = parts.find((p) => p.uuid !== uuid);
      if (other) chats.push({ chatId, with: other.username });
    }
    return chats;
  }

  // ----- custom rooms -----

  onJoinRoom(ws, data, user) {
    const code = normRoom(data.code);
    if (code.length < 3) {
      send(ws, { type: 'error', message: 'Room codes need 3-20 letters, numbers or dashes' });
      return;
    }
    const restore = !!data.restore;
    const rooms = user.rooms || [];
    if (rooms.includes(code)) {
      send(ws, { type: 'roomJoined', code, restore });
      send(ws, { type: 'roomUsers', code, users: this.roomUsers(code) });
      return;
    }
    if (rooms.length >= MAX_ROOMS_PER_USER) {
      send(ws, { type: 'error', message: `You can be in at most ${MAX_ROOMS_PER_USER} rooms` });
      return;
    }

    const channel = 'room:' + code;
    if (!this.channels[channel]) {
      if (this.roomCount() >= MAX_ROOMS_TOTAL) this.pruneRooms();
      if (this.roomCount() >= MAX_ROOMS_TOTAL) {
        send(ws, { type: 'error', message: 'Too many rooms right now, try again later' });
        return;
      }
      this.channels[channel] = [];
    }

    user.rooms = [...rooms, code];
    ws.serializeAttachment(user);
    send(ws, { type: 'roomJoined', code, restore });
    this.broadcastRoomUsers(code);
  }

  onLeaveRoom(ws, data, user) {
    const code = normRoom(data.code);
    if (!(user.rooms || []).includes(code)) return;
    user.rooms = user.rooms.filter((r) => r !== code);
    ws.serializeAttachment(user);
    send(ws, { type: 'roomLeft', code });
    this.broadcastRoomUsers(code);
  }

  // ----- messages -----

  buildMessage(user, data, text, imageUrl) {
    const profile = this.userProfiles.get(lc(user.username));
    return {
      id: crypto.randomUUID(),
      author: user.username,
      text,
      timestamp: this.nextTimestamp(),
      role: roleOf(user),
      color: profile?.color || 'default',
      replyTo: typeof data.replyTo === 'string' ? data.replyTo.slice(0, 64) : null,
      reactions: {},
      imageUrl
    };
  }

  // Validates text + image. Returns { text, imageUrl } or null (after telling the sender why).
  // Images are either uploaded files (data: URLs) or GIPHY links from the GIF picker.
  readContent(ws, data) {
    const text = typeof data.text === 'string' ? data.text.slice(0, MAX_TEXT) : '';
    let imageUrl = null;
    if (data.imageUrl != null) {
      const u = data.imageUrl;
      const okData = typeof u === 'string' && u.startsWith('data:image/') && u.length <= MAX_IMAGE_CHARS;
      const okGif = typeof u === 'string' && u.length <= 500 && GIF_URL_RE.test(u);
      if (!okData && !okGif) {
        send(ws, { type: 'error', message: 'Image is invalid or too large' });
        return null;
      }
      imageUrl = u;
    }
    if (!text.trim() && !imageUrl) return null;
    return { text, imageUrl };
  }

  // True if the user may speak right now (not muted / timed out).
  checkMuted(ws, user) {
    const until = this.mutedUntil.get(lc(user.username));
    if (until && until > Date.now()) {
      send(ws, { type: 'error', message: `You are muted for another ${Math.ceil((until - Date.now()) / 1000)}s` });
      return false;
    }
    return true;
  }

  // 'mute' | 'dm' | null (checks both the user's IP and username).
  restrictionOf(user) {
    const a = this.restrictedIPs.get(user.ip);
    const b = this.restrictedUsers.get(lc(user.username));
    return a === 'mute' || b === 'mute' ? 'mute' : a || b || null;
  }

  // 'mute' blocks everything; 'dm' blocks channels/rooms but allows DMs.
  checkRestricted(ws, user, isDM) {
    const r = this.restrictionOf(user);
    if (r === 'mute' || (r === 'dm' && !isDM)) {
      send(ws, { type: 'error', message: r === 'mute' ? 'You are muted and cannot send messages' : 'You can only send direct messages' });
      return false;
    }
    return true;
  }

  // Auto slow mode for people who flood the chat. Staff and VIPs are exempt.
  checkSpam(ws, user) {
    if (isStaff(user) || user.isVIP) return true;
    const key = lc(user.username);
    const now = Date.now();
    const recent = (this.recentMsgs.get(key) || []).filter((t) => now - t < SPAM_WINDOW_MS);
    const until = this.autoSlowUntil.get(key) || 0;
    if (until > now && recent.length && now - recent[recent.length - 1] < AUTO_SLOW_GAP_MS) {
      const wait = Math.ceil((AUTO_SLOW_GAP_MS - (now - recent[recent.length - 1])) / 1000);
      send(ws, { type: 'error', message: `Slow mode: wait ${wait}s between messages` });
      return false;
    }
    recent.push(now);
    this.recentMsgs.set(key, recent);
    if (recent.length >= SPAM_MESSAGES && until <= now) {
      this.autoSlowUntil.set(key, now + AUTO_SLOW_MS);
      send(ws, { type: 'error', message: 'You were sending messages too fast. Slow mode is on for 5 minutes.' });
    }
    return true;
  }

  onMessage(ws, data, user) {
    if (!validChannel(data.channel) || !this.canAccessChannel(user, data.channel)) return;
    const content = this.readContent(ws, data);
    if (!content) return;
    if (!this.checkMuted(ws, user)) return;
    if (!this.checkRestricted(ws, user, false)) return;

    const key = lc(user.username);
    if (this.slowMode.enabled && !isStaff(user)) {
      const last = this.lastMessageAt.get(key);
      if (last && Date.now() - last < this.slowMode.duration * 1000) {
        send(ws, { type: 'error', message: `Slow mode: wait ${this.slowMode.duration}s between messages` });
        return;
      }
    }
    if (!this.checkSpam(ws, user)) return;
    this.lastMessageAt.set(key, Date.now());

    const message = this.buildMessage(user, data, content.text, content.imageUrl);
    message.channel = data.channel;

    const list = this.chanList(data.channel, true);
    if (!list) return;
    list.push(message);
    bg(this.ctx.storage.put(chKey(message), message));
    while (list.length > MAX_CHANNEL_HISTORY) {
      bg(this.ctx.storage.delete(chKey(list.shift())));
    }

    this.broadcastChannel(data.channel, { type: 'message', message });
  }

  onPrivateMessage(ws, data, user) {
    if (!this.isParticipant(data.chatId, user.uuid)) return;
    const content = this.readContent(ws, data);
    if (!content) return;
    if (!this.checkMuted(ws, user)) return;
    if (!this.checkRestricted(ws, user, true)) return;

    // Blocking works both ways: neither person can send while a block exists.
    const other = this.dmParticipants.get(data.chatId).find((p) => p.uuid !== user.uuid);
    if (other) {
      if (this.isBlockedBy(other.uuid, user.uuid)) {
        send(ws, { type: 'error', message: "You can't send messages to this user" });
        return;
      }
      if (this.isBlockedBy(user.uuid, other.uuid)) {
        send(ws, { type: 'error', message: 'You blocked this user. Unblock them to send messages.' });
        return;
      }
    }
    if (!this.checkSpam(ws, user)) return;

    const message = this.buildMessage(user, data, content.text, content.imageUrl);
    message.chatId = data.chatId;

    if (!this.privateChats.has(data.chatId)) this.privateChats.set(data.chatId, []);
    const list = this.privateChats.get(data.chatId);
    list.push(message);
    bg(this.ctx.storage.put(dmKey(message), message));
    while (list.length > MAX_DM_HISTORY) {
      bg(this.ctx.storage.delete(dmKey(list.shift())));
    }

    const uuids = this.dmParticipants.get(data.chatId).map((p) => p.uuid);
    this.sendToUuids(uuids, { type: 'privateMessage', message });
  }

  // Anyone can delete their own messages (channels, rooms and DMs).
  onDeleteMessage(ws, data, user) {
    const mine = (m) => m && lc(m.author) === lc(user.username);
    if (data.isPrivate) {
      if (!this.isParticipant(data.chatId, user.uuid)) return;
      const list = this.privateChats.get(data.chatId) || [];
      const i = list.findIndex((m) => m.id === data.messageId);
      if (i === -1 || !mine(list[i])) return;
      const [removed] = list.splice(i, 1);
      bg(this.ctx.storage.delete(dmKey(removed)));
      this.sendToUuids(this.dmParticipants.get(data.chatId).map((p) => p.uuid),
        { type: 'privateMessageDeleted', chatId: data.chatId, messageId: removed.id });
      return;
    }
    if (!validChannel(data.channel) || !this.canAccessChannel(user, data.channel)) return;
    const list = this.chanList(data.channel) || [];
    const i = list.findIndex((m) => m.id === data.messageId);
    if (i === -1 || !mine(list[i])) return;
    const [removed] = list.splice(i, 1);
    bg(this.ctx.storage.delete(chKey(removed)));
    this.broadcastChannel(data.channel, { type: 'messageDeleted', messageId: removed.id, channel: data.channel });
  }

  onGetHistory(ws, data, user) {
    if (!validChannel(data.channel) || !this.canAccessChannel(user, data.channel)) return;
    send(ws, { type: 'history', channel: data.channel, messages: this.chanList(data.channel) || [] });
  }

  onGetPrivateHistory(ws, data, user) {
    if (!this.isParticipant(data.chatId, user.uuid)) return;
    send(ws, { type: 'privateHistory', chatId: data.chatId, messages: this.privateChats.get(data.chatId) || [] });
  }

  onToggleReaction(data, user) {
    if (typeof data.emoji !== 'string' || !EMOJI_RE.test(data.emoji)) return;

    let message;
    let recipients = null; // null = everyone who can see the channel
    if (data.isPrivate) {
      if (!this.isParticipant(data.chatId, user.uuid)) return;
      message = (this.privateChats.get(data.chatId) || []).find((m) => m.id === data.messageId);
      recipients = this.dmParticipants.get(data.chatId).map((p) => p.uuid);
    } else {
      if (!validChannel(data.channel) || !this.canAccessChannel(user, data.channel)) return;
      message = (this.chanList(data.channel) || []).find((m) => m.id === data.messageId);
    }
    if (!message) return;

    const users = message.reactions[data.emoji] || [];
    const i = users.indexOf(user.username);
    if (i === -1) users.push(user.username);
    else users.splice(i, 1);
    if (users.length) message.reactions[data.emoji] = users;
    else delete message.reactions[data.emoji];

    bg(this.ctx.storage.put(data.isPrivate ? dmKey(message) : chKey(message), message));

    const update = {
      type: 'reactionUpdate',
      messageId: message.id,
      reactions: message.reactions,
      isPrivate: !!data.isPrivate,
      channel: message.channel,
      chatId: message.chatId
    };
    if (recipients) this.sendToUuids(recipients, update);
    else this.broadcastChannel(message.channel, update);
  }

  onTyping(ws, data, user) {
    const isTyping = !!data.isTyping;
    if (data.isPrivate) {
      if (!this.isParticipant(data.chatId, user.uuid)) return;
      const others = this.dmParticipants.get(data.chatId).map((p) => p.uuid).filter((u) => u !== user.uuid);
      this.sendToUuids(others, { type: 'typing', username: user.username, isTyping, isPrivate: true, chatId: data.chatId });
    } else if (validChannel(data.channel) && this.canAccessChannel(user, data.channel)) {
      this.broadcastChannel(data.channel, { type: 'typing', username: user.username, isTyping, isPrivate: false, channel: data.channel }, ws);
    }
  }

  onUpdateProfile(data, user) {
    const color = COLORS.includes(data.profileColor) ? data.profileColor : 'default';
    this.userProfiles.set(lc(user.username), { color });
    this.saveMeta();
  }

  // ----- blocking -----

  isBlockedBy(blockerUuid, otherUuid) {
    return !!this.blocks.get(blockerUuid)?.has(otherUuid);
  }

  sendBlockList(ws, user) {
    send(ws, { type: 'blockList', users: [...(this.blocks.get(user.uuid)?.values() || [])] });
  }

  onBlockUser(ws, data, user) {
    const t = this.findUser(data.targetUsername);
    if (!t || t.user.uuid === user.uuid) {
      send(ws, { type: 'error', message: 'User not online' });
      return;
    }
    const mine = this.blocks.get(user.uuid) || new Map();
    if (mine.size >= MAX_BLOCKS && !mine.has(t.user.uuid)) {
      send(ws, { type: 'error', message: 'Your block list is full' });
      return;
    }
    mine.set(t.user.uuid, t.user.username);
    this.blocks.set(user.uuid, mine);
    this.saveMeta();
    this.sendBlockList(ws, user);
  }

  onUnblockUser(ws, data, user) {
    const mine = this.blocks.get(user.uuid);
    if (!mine) return;
    const name = lc(data.username ?? '');
    for (const [id, n] of mine) if (lc(n) === name) mine.delete(id);
    if (!mine.size) this.blocks.delete(user.uuid);
    this.saveMeta();
    this.sendBlockList(ws, user);
  }

  // ----- direct message requests -----

  onPrivateChatRequest(ws, data, user) {
    const target = this.findUser(data.targetUsername);
    if (!target || target.user.uuid === user.uuid) {
      send(ws, { type: 'error', message: 'User not online' });
      return;
    }
    if (this.isBlockedBy(target.user.uuid, user.uuid)) {
      send(ws, { type: 'error', message: "You can't message this user" });
      return;
    }
    if (this.isBlockedBy(user.uuid, target.user.uuid)) {
      send(ws, { type: 'error', message: 'You blocked this user. Unblock them first.' });
      return;
    }

    const existing = this.findChat(user.uuid, target.user.uuid);
    if (existing) {
      // Chat already exists: just open it for the requester.
      send(ws, { type: 'privateChatAccepted', chatId: existing, with: target.user.username });
      return;
    }

    // Remember the request on the target's socket so it survives hibernation.
    const pending = [...(target.user.pending || []).filter((u) => u !== user.uuid), user.uuid].slice(-10);
    target.ws.serializeAttachment({ ...target.user, pending });
    send(target.ws, { type: 'privateChatRequest', from: user.username });
  }

  onPrivateChatResponse(ws, data, user) {
    const requester = this.findUser(data.from);
    if (!requester) return;

    // Only honour responses to a real, pending request.
    const pending = user.pending || [];
    if (!pending.includes(requester.user.uuid)) return;
    ws.serializeAttachment({ ...user, pending: pending.filter((u) => u !== requester.user.uuid) });

    if (!data.accepted) {
      send(requester.ws, { type: 'privateChatRejected', by: user.username });
      return;
    }

    let chatId = this.findChat(user.uuid, requester.user.uuid);
    if (!chatId) {
      chatId = crypto.randomUUID();
      this.dmParticipants.set(chatId, [
        { uuid: user.uuid, username: user.username },
        { uuid: requester.user.uuid, username: requester.user.username }
      ]);
      this.privateChats.set(chatId, []);
      this.saveMeta();
    }
    send(ws, { type: 'privateChatAccepted', chatId, with: requester.user.username });
    send(requester.ws, { type: 'privateChatAccepted', chatId, with: user.username });
  }

  findChat(uuidA, uuidB) {
    for (const [chatId, parts] of this.dmParticipants) {
      if (parts.some((p) => p.uuid === uuidA) && parts.some((p) => p.uuid === uuidB)) return chatId;
    }
    return null;
  }

  // ----- voice (signalling only; audio flows peer-to-peer over WebRTC) -----

  onJoinVoice(ws, data, user) {
    const channel = data.channel;
    if (!VOICE_CHANNELS.includes(channel) || user.voice === channel) return;
    if (user.voice) this.leaveVoice(ws, user);

    const peers = this.voiceUsers(channel); // everyone already there (not including us)
    user.voice = channel;
    ws.serializeAttachment(user);

    // The newcomer is told who to call; existing members just wait for offers.
    send(ws, { type: 'voiceJoined', channel, peers });
    this.broadcast({ type: 'voiceUsers', channel, users: this.voiceUsers(channel) });
  }

  leaveVoice(ws, user) {
    const channel = user.voice;
    if (!channel) return;
    user.voice = null;
    ws.serializeAttachment(user);
    this.broadcast({ type: 'voiceUserLeft', username: user.username, channel });
    this.broadcast({ type: 'voiceUsers', channel, users: this.voiceUsers(channel) });
  }

  relayVoice(user, data, type, key) {
    if (!user.voice || data[key] == null) return;
    if (JSON.stringify(data[key]).length > 20000) return;
    const target = this.findUser(data.to);
    if (!target || target.user.voice !== user.voice) return;
    send(target.ws, { type, from: user.username, channel: user.voice, [key]: data[key] });
  }

  // ----- admin actions -----

  ok(ws, message) {
    send(ws, { type: 'adminActionSuccess', message });
  }

  onAdminKick(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.targetUsername);
    if (!t) return;
    const reason = cleanReason(data.reason);
    send(t.ws, {
      type: 'kicked',
      message: `You have been kicked${reason ? ': ' + reason : ''}`,
      redirectUrl: 'https://google.com'
    });
    try { t.ws.close(4002, 'kicked'); } catch { /* ignore */ }
    this.ok(ws, `Kicked ${t.user.username}`);
  }

  // Shared by "timeout" and "mute": the server enforces it, the client also locks its input box.
  onAdminTimeout(ws, data, admin, eventType) {
    const t = this.modTarget(ws, admin, data.targetUsername);
    if (!t) return;
    const duration = clamp(data.duration, 1, 86400, 60);
    const reason = cleanReason(data.reason);
    this.mutedUntil.set(lc(t.user.username), Date.now() + duration * 1000);
    const verb = eventType === 'timedOut' ? 'timed out' : 'muted';
    send(t.ws, {
      type: eventType,
      duration,
      message: `You have been ${verb} for ${duration}s${reason ? ': ' + reason : ''}`
    });
    this.ok(ws, `${verb[0].toUpperCase()}${verb.slice(1)} ${t.user.username} for ${duration}s`);
  }

  // Ban modes:
  //   full = kicked now and can't rejoin (the original behaviour)
  //   mute = infinite mute: can't send anything, including DMs
  //   dm   = can't type in channels/rooms, but DMs still work
  onAdminBan(ws, data, admin) {
    const name = cleanName(data.targetUsername);
    if (!name) return;
    const banType = ['username', 'ip', 'both'].includes(data.banType) ? data.banType : 'ip';
    const mode = BAN_MODES.includes(data.mode) ? data.mode : 'full';
    const banName = banType !== 'ip';
    const banIp = banType !== 'username';

    const t = this.findUser(name);
    if (t && !this.canModerate(admin, t.user)) {
      send(ws, { type: 'error', message: 'Cannot moderate this user' });
      return;
    }
    if (!t && !banName) {
      send(ws, { type: 'error', message: 'User is not online (an IP ban needs an online user)' });
      return;
    }

    const reason = cleanReason(data.reason);
    const ip = t && t.user.ip && t.user.ip !== 'unknown' ? t.user.ip : null;

    if (mode === 'full') {
      if (banName) this.bannedUsers.add(lc(name));
      if (banIp && ip) this.bannedIPs.add(ip);
      this.saveMeta();
      if (t) {
        send(t.ws, { type: 'banned', message: `You have been banned${reason ? ': ' + reason : ''}` });
        try { t.ws.close(4003, 'banned'); } catch { /* ignore */ }
      }
      this.ok(ws, `Banned ${name}`);
      return;
    }

    if (banName) this.restrictedUsers.set(lc(name), mode);
    if (banIp && ip) this.restrictedIPs.set(ip, mode);
    this.saveMeta();
    if (t) {
      send(t.ws, {
        type: 'restricted',
        message: (mode === 'mute'
          ? 'You have been muted and can no longer send messages'
          : 'You can no longer chat in channels or rooms, but you can still send DMs') + (reason ? ': ' + reason : '')
      });
    }
    this.ok(ws, `${mode === 'mute' ? 'Muted' : 'Chat-blocked'} ${name} (until removed in the Bans tab)`);
  }

  onAdminUnban(ws, data) {
    this.bannedUsers.delete(lc(data.username ?? ''));
    this.saveMeta();
    this.ok(ws, `Unbanned ${data.username}`);
    this.onAdminGetBanList(ws);
  }

  onAdminUnbanIP(ws, data) {
    this.bannedIPs.delete(data.ip);
    this.saveMeta();
    this.ok(ws, `Unbanned IP ${data.ip}`);
    this.onAdminGetBanList(ws);
  }

  onAdminUnrestrict(ws, data) {
    if (data.kind === 'ip') this.restrictedIPs.delete(data.value);
    else if (data.kind === 'user') this.restrictedUsers.delete(lc(data.value ?? ''));
    else return;
    this.saveMeta();
    this.ok(ws, `Removed restriction on ${data.value}`);
    this.onAdminGetBanList(ws);
  }

  onAdminWarning(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.targetUsername);
    if (!t) return;
    const key = lc(t.user.username);
    const count = (this.userWarnings.get(key) || 0) + 1;
    this.userWarnings.set(key, count);
    this.saveMeta();
    send(t.ws, { type: 'warning', message: cleanReason(data.reason) || 'You have been warned', count });
    this.ok(ws, `Warned ${t.user.username} (warning #${count})`);
  }

  onAdminDeleteMessage(ws, data, user) {
    if (!validChannel(data.channel) || !this.canAccessChannel(user, data.channel)) return;
    const list = this.chanList(data.channel);
    if (!list) return;
    const i = list.findIndex((m) => m.id === data.messageId);
    if (i === -1) return;
    const [removed] = list.splice(i, 1);
    bg(this.ctx.storage.delete(chKey(removed)));
    this.broadcastChannel(data.channel, { type: 'messageDeleted', messageId: removed.id, channel: data.channel });
    this.ok(ws, 'Message deleted');
  }

  onAdminGetBanList(ws) {
    const restricted = [
      ...[...this.restrictedUsers].map(([value, mode]) => ({ kind: 'user', value, mode })),
      ...[...this.restrictedIPs].map(([value, mode]) => ({ kind: 'ip', value, mode }))
    ];
    send(ws, { type: 'banList', bannedUsers: [...this.bannedUsers], bannedIPs: [...this.bannedIPs], restricted });
  }

  onAdminBroadcast(ws, data) {
    const message = typeof data.message === 'string' ? data.message.trim().slice(0, 500) : '';
    if (!message) return;
    this.broadcast({ type: 'broadcast', message });
    this.ok(ws, 'Broadcast sent');
  }

  onAdminSlowMode(ws, data) {
    this.slowMode = { enabled: !!data.enabled, duration: clamp(data.duration, 1, 3600, 5) };
    this.saveMeta();
    this.ok(ws, this.slowMode.enabled ? `Slow mode on (${this.slowMode.duration}s)` : 'Slow mode off');
  }

  onAdminClearChat(ws, data) {
    if (!CHANNELS.includes(data.channel)) return;
    const keys = this.channels[data.channel].map(chKey);
    this.channels[data.channel] = [];
    if (keys.length) bg(this.ctx.storage.delete(keys));
    this.broadcast({ type: 'chatCleared', channel: data.channel });
    this.ok(ws, `Cleared #${data.channel}`);
  }

  onAdminEffect(ws, data, admin) {
    if (!EFFECTS.has(data.effect)) return;
    const t = this.modTarget(ws, admin, data.targetUsername);
    if (!t) return;
    send(t.ws, { type: data.effect });
    this.ok(ws, `Sent ${data.effect} to ${t.user.username}`);
  }

  onAdminConfettiAll(ws) {
    this.broadcast({ type: 'confetti' });
    this.ok(ws, 'Confetti sent to everyone');
  }

  onAdminForceDisconnect(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.targetUsername);
    if (!t) return;
    send(t.ws, { type: 'forceDisconnect' });
    try { t.ws.close(4004, 'disconnected by admin'); } catch { /* ignore */ }
    this.ok(ws, `Disconnected ${t.user.username}`);
  }
}

// ---------- GIF search (the GIPHY key stays on the server) ----------

const json = (body, status = 200) => new Response(JSON.stringify(body), {
  status,
  headers: {
    'Content-Type': 'application/json',
    'Access-Control-Allow-Origin': '*',
    'Cache-Control': 'public, max-age=300'
  }
});

async function searchGifs(url, env) {
  if (!env.GIPHY_API_KEY) return json({ error: 'GIF search is not set up yet' }, 503);
  const q = (url.searchParams.get('q') || '').trim().slice(0, 50);
  const api = new URL('https://api.giphy.com/v1/gifs/' + (q ? 'search' : 'trending'));
  api.searchParams.set('api_key', env.GIPHY_API_KEY);
  api.searchParams.set('limit', '24');
  api.searchParams.set('rating', 'pg-13');
  if (q) api.searchParams.set('q', q);
  try {
    const r = await fetch(api);
    if (!r.ok) return json({ error: 'GIF service unavailable' }, 502);
    const body = await r.json();
    const results = (body.data || []).map((g) => ({
      id: g.id,
      title: g.title || '',
      preview: g.images?.fixed_width_small?.url || g.images?.fixed_width?.url,
      url: g.images?.fixed_height?.url || g.images?.original?.url
    })).filter((g) => g.preview && g.url);
    return json({ results });
  } catch {
    return json({ error: 'GIF service unavailable' }, 502);
  }
}

// ---------- Worker entry point ----------

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const wantsSocket = request.headers.get('Upgrade') === 'websocket';

    if (url.pathname === '/api/gifs') return searchGifs(url, env);

    // The page connects to /ws. (A plain "/" request is served by static assets, so it
    // can never be used for the upgrade.)
    if (wantsSocket || url.pathname === '/ws') {
      if (!wantsSocket) return new Response('Expected WebSocket request', { status: 426 });
      const room = env.CHAT_ROOM.get(env.CHAT_ROOM.idFromName('global'));
      return room.fetch(request);
    }

    return env.ASSETS.fetch(request);
  }
};
