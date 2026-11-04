/**
 * Hub - Cloudflare Worker + Durable Object realtime server.
 *
 * Accounts live in a D1 (SQLite) database bound as DB (see wrangler.jsonc). The tables are
 * created automatically on first use. Guests can join without an account, but cannot use a
 * username that belongs to an account.
 *
 * Secrets (set with `npx wrangler secret put NAME`, or in .dev.vars for local dev):
 *   OWNER_PASSWORD  - typing it in the "Admin login" box while logged in to an account makes
 *                     that account an owner (saved in the database).
 *   ADMIN_PASSWORD, VIP_PASSWORD - optional extra passwords that grant a role for one session.
 * Owners can give other accounts VIP or Mod (admin) from the Owner tab of the admin panel.
 *
 * Messages are deleted automatically after 3 days.
 *
 * Rooms: any channel named "space:<code>" is private. Only sockets that
 * have entered that code can read it, post in it, or receive its events.
 */

const BOARDS = ['general', 'gaming', 'memes'];
const AV_BOARDS = ['general', 'chill', 'gaming'];
const COLORS = ['default', 'red', 'orange', 'yellow', 'green', 'blue', 'purple', 'pink'];
const EFFECTS = new Set([
  'spinScreen', 'shakeScreen', 'flipScreen', 'invertColors', 'rainbow',
  'blur', 'matrix', 'emojiSpam', 'confetti', 'rickRoll'
]);

const MAX_BOARD_LOG = 100;
const MAX_LINK_LOG = 200;
const MAX_TEXT = 2000;
const MAX_MEDIA_CHARS = 1000000;   // the page shrinks big pictures to fit this
const MAX_FRAME_CHARS = 1040000;   // WebSocket frames stay just under 1 MiB

const MAX_AGE_MS = 3 * 24 * 60 * 60 * 1000;   // messages are deleted after 3 days
const PURGE_EVERY_MS = 60 * 60 * 1000;        // ...checked once an hour

const PBKDF2_ITERS = 100000;                  // the most Workers allows
const SESSION_TTL_MS = 30 * 24 * 60 * 60 * 1000;
const ACCOUNT_NAME_RE = /^[A-Za-z0-9_.-]{3,20}$/;
const GUEST_NAME_RE = /^guest\d*$/i;           // reserved for guests
const DUMMY_SALT = '00000000000000000000000000000000';

const BURST_COUNT = 9, BURST_WINDOW_MS = 3000;
const AUTO_PACE_MS = 5 * 60 * 1000, AUTO_PACE_GAP_MS = 3000;

const MAX_HIDDEN = 100;
const BAR_MODES = ['full', 'mute', 'dm'];

const SPACE_RE = /^space:[a-z0-9-]{3,20}$/;
const MAX_SPACES_PER_USER = 10;
const MAX_SPACES_TOTAL = 200;

const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const EMOJI_RE = /^\P{ASCII}{1,10}$/u;

// ---------- helpers ----------

const send = (ws, data) => {
  try { ws.send(JSON.stringify(data)); } catch { /* socket closed */ }
};
const bg = (promise) => promise.catch((err) => console.error('storage error:', err));
const lc = (s) => String(s).toLowerCase();
const pad = (n) => String(n).padStart(15, '0');
const bKey = (m) => `b:${m.board}:${pad(m.ts)}-${m.id}`;
const tKey = (m) => `t:${m.thread}:${pad(m.ts)}-${m.id}`;

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

const normSpace = (v) => String(v ?? '').toLowerCase().replace(/[^a-z0-9-]/g, '').slice(0, 20);
const isSpaceBoard = (c) => typeof c === 'string' && SPACE_RE.test(c);
const validBoard = (c) => typeof c === 'string' && (BOARDS.includes(c) || SPACE_RE.test(c));

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

const toHex = (bytes) => [...bytes].map((b) => b.toString(16).padStart(2, '0')).join('');
const fromHex = (hex) => Uint8Array.from(hex.match(/../g).map((h) => parseInt(h, 16)));
const randomHex = (n) => toHex(crypto.getRandomValues(new Uint8Array(n)));
async function sha256Hex(text) {
  return toHex(new Uint8Array(await crypto.subtle.digest('SHA-256', new TextEncoder().encode(text))));
}
async function hashPassword(password, saltHex) {
  const key = await crypto.subtle.importKey('raw', new TextEncoder().encode(password), 'PBKDF2', false, ['deriveBits']);
  const bits = await crypto.subtle.deriveBits(
    { name: 'PBKDF2', hash: 'SHA-256', salt: fromHex(saltHex), iterations: PBKDF2_ITERS }, key, 256);
  return toHex(new Uint8Array(bits));
}
// Always does the same work, even for names that don't exist.
async function verifyPassword(password, account) {
  const h = await hashPassword(password, account ? account.salt : DUMMY_SALT);
  return !!account && safeEqual(h, account.hash);
}

const roleOf = (u) => (u.isOwner ? 'owner' : u.isAdmin ? 'admin' : u.isVIP ? 'vip' : null);
const isStaff = (u) => !!(u && (u.isAdmin || u.isOwner));

// ---------- Durable Object ----------

export class Hub {
  constructor(ctx, env) {
    this.ctx = ctx;
    this.env = env;

    this.boards = Object.fromEntries(BOARDS.map((c) => [c, []]));
    this.links = new Map();           // thread id -> item[]
    this.linkMembers = new Map();     // thread id -> [{ uuid, name }, { uuid, name }]
    this.barredNames = new Set();
    this.barredIPs = new Set();
    this.notices = new Map();
    this.profiles = new Map();
    this.pace = { enabled: false, duration: 5 };
    this.limitedIPs = new Map();
    this.limitedNames = new Map();
    this.hidden = new Map();          // uuid -> Map(uuid -> name)

    this.lastPostAt = new Map();
    this.pausedUntil = new Map();
    this.recentPosts = new Map();
    this.autoPaceUntil = new Map();
    this.lastTs = 0;

    this.opening = new WeakSet();     // sockets in the middle of signing in
    this.authFails = new Map();       // ip -> { n, t }
    this.signups = new Map();         // ip -> [timestamps]
    this.schemaReady = null;

    ctx.blockConcurrencyWhile(async () => {
      await this.load();
      await this.purgeOld();
      if (!(await ctx.storage.getAlarm())) await ctx.storage.setAlarm(Date.now() + PURGE_EVERY_MS);
    });
  }

  // ----- persistence -----

  async load() {
    const meta = await this.ctx.storage.get('meta');
    if (meta) {
      this.barredNames = new Set(meta.bannedUsers || []);
      this.barredIPs = new Set(meta.bannedIPs || []);
      this.notices = new Map(Object.entries(meta.userWarnings || {}));
      this.profiles = new Map(Object.entries(meta.userProfiles || {}));
      this.linkMembers = new Map(Object.entries(meta.dmParticipants || {}));
      this.limitedIPs = new Map(Object.entries(meta.restrictedIPs || {}));
      this.limitedNames = new Map(Object.entries(meta.restrictedUsers || {}));
      this.hidden = new Map(Object.entries(meta.blocks || {}).map(([k, o]) => [k, new Map(Object.entries(o))]));
      if (meta.slowMode) this.pace = meta.slowMode;
    }

    for (const m of (await this.ctx.storage.list({ prefix: 'b:' })).values()) {
      const list = this.boardList(m.board, true);
      if (list) list.push(m);
    }
    for (const m of (await this.ctx.storage.list({ prefix: 't:' })).values()) {
      if (!this.links.has(m.thread)) this.links.set(m.thread, []);
      this.links.get(m.thread).push(m);
    }
  }

  saveMeta() {
    bg(this.ctx.storage.put('meta', {
      bannedUsers: [...this.barredNames],
      bannedIPs: [...this.barredIPs],
      userWarnings: Object.fromEntries(this.notices),
      userProfiles: Object.fromEntries(this.profiles),
      dmParticipants: Object.fromEntries(this.linkMembers),
      restrictedIPs: Object.fromEntries(this.limitedIPs),
      restrictedUsers: Object.fromEntries(this.limitedNames),
      blocks: Object.fromEntries([...this.hidden].map(([k, m]) => [k, Object.fromEntries(m)])),
      slowMode: this.pace
    }));
  }

  nextTimestamp() {
    this.lastTs = Math.max(Date.now(), this.lastTs + 1);
    return this.lastTs;
  }

  // ----- 3-day cleanup -----

  async purgeOld() {
    const cutoff = Date.now() - MAX_AGE_MS;
    for (const list of Object.values(this.boards)) while (list.length && list[0].ts < cutoff) list.shift();
    for (const list of this.links.values()) while (list.length && list[0].ts < cutoff) list.shift();

    const stale = [];
    for (const prefix of ['b:', 't:']) {
      for (const [key, m] of await this.ctx.storage.list({ prefix })) {
        if (m && m.ts < cutoff) stale.push(key);
      }
    }
    for (let i = 0; i < stale.length; i += 128) await this.ctx.storage.delete(stale.slice(i, i + 128));
    this.pruneSpaces();
  }

  async alarm() {
    try { await this.purgeOld(); } catch (err) { console.error('purge failed:', err); }
    await this.ctx.storage.setAlarm(Date.now() + PURGE_EVERY_MS);
  }

  // ----- board / space helpers -----

  boardList(board, create = false) {
    if (!validBoard(board)) return null;
    if (!this.boards[board] && create && isSpaceBoard(board)) this.boards[board] = [];
    return this.boards[board] || null;
  }

  canAccessBoard(user, board) {
    if (BOARDS.includes(board)) return true;
    return isSpaceBoard(board) && (user.spaces || []).includes(board.slice(6));
  }

  spaceMembers(code) {
    return this.joinedSockets().filter(([, u]) => (u.spaces || []).includes(code)).map(([, u]) => u.name);
  }

  spaceCount() {
    return Object.keys(this.boards).filter((k) => k.startsWith('space:')).length;
  }

  pruneSpaces() {
    for (const [k, list] of Object.entries(this.boards)) {
      if (k.startsWith('space:') && !list.length && !this.spaceMembers(k.slice(6)).length) delete this.boards[k];
    }
  }

  broadcastBoard(board, data, exceptWs = null) {
    if (!isSpaceBoard(board)) return this.broadcast(data, exceptWs);
    const code = board.slice(6);
    const payload = JSON.stringify(data);
    for (const [ws, u] of this.joinedSockets()) {
      if (ws === exceptWs || !(u.spaces || []).includes(code)) continue;
      try { ws.send(payload); } catch { /* ignore */ }
    }
  }

  broadcastSpaceMembers(code) {
    this.broadcastBoard('space:' + code, { type: 'spaceMembers', code, members: this.spaceMembers(code) });
  }

  // ----- socket entry points -----

  async fetch(request) {
    if (request.headers.get('Upgrade') !== 'websocket') {
      return new Response('Not found', { status: 426 });
    }

    const ip = request.headers.get('cf-connecting-ip') || 'unknown';
    const [client, server] = Object.values(new WebSocketPair());

    if (this.barredIPs.has(ip)) {
      server.accept();
      server.send(JSON.stringify({ type: 'barred', message: 'You are banned from this server (IP ban)' }));
      server.close(4003, 'barred');
      return new Response(null, { status: 101, webSocket: client });
    }

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
      await this.dispatch(ws, data);
    } catch (err) {
      console.error('Error handling', data.type, err);
    }
  }

  async webSocketClose(ws, code) {
    const user = ws.deserializeAttachment();
    const closeCode = code >= 1000 && code < 5000 && ![1005, 1006, 1015].includes(code) ? code : 1000;
    try { ws.close(closeCode, 'closing'); } catch { /* already closed */ }

    if (user && user.name) {
      if (user.av) {
        this.broadcast({ type: 'avLeft', name: user.name, board: user.av });
        this.broadcast({ type: 'avMembers', board: user.av, members: this.avMembers(user.av) });
      }
      for (const code of user.spaces || []) this.broadcastSpaceMembers(code);
      this.broadcast({ type: 'roster', members: this.getRoster() });
    }
  }

  async webSocketError(ws, error) {
    console.error('Socket error:', error);
  }

  // ----- socket helpers -----

  openSockets() {
    return this.ctx.getWebSockets().filter((ws) => ws.readyState === 1);
  }

  joinedSockets() {
    const out = [];
    for (const ws of this.openSockets()) {
      const u = ws.deserializeAttachment();
      if (u && u.name) out.push([ws, u]);
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

  findMember(name) {
    const n = lc(name ?? '');
    for (const [ws, user] of this.joinedSockets()) {
      if (lc(user.name) === n) return { ws, user };
    }
    return null;
  }

  getRoster() {
    return this.joinedSockets()
      .map(([, u]) => ({ name: u.name, isOwner: !!u.isOwner, isAdmin: !!u.isAdmin, isVIP: !!u.isVIP }))
      .sort((a, b) => a.name.localeCompare(b.name));
  }

  avMembers(board) {
    return this.joinedSockets().filter(([, u]) => u.av === board).map(([, u]) => u.name);
  }

  isLinkMember(thread, uuid) {
    const parts = typeof thread === 'string' ? this.linkMembers.get(thread) : null;
    return !!parts && parts.some((p) => p.uuid === uuid);
  }

  canModerate(moderator, target) {
    if (target.isOwner) return false;
    if (moderator.isOwner) return true;
    return !!(moderator.isAdmin && !target.isAdmin);
  }

  modTarget(ws, admin, name) {
    const t = this.findMember(name);
    if (!t) {
      send(ws, { type: 'fault', message: 'User not online' });
      return null;
    }
    if (!this.canModerate(admin, t.user)) {
      send(ws, { type: 'fault', message: 'Cannot moderate this user' });
      return null;
    }
    return t;
  }

  // ----- dispatch -----

  dispatch(ws, data) {
    const user = ws.deserializeAttachment() || {};

    if (data.type === 'open') return this.onOpen(ws, data, user);
    if (!user.name) return;

    if (data.type.startsWith('ctl') && !isStaff(user)) return;

    switch (data.type) {
      case 'entry': return this.onEntry(ws, data, user);
      case 'note': return this.onNote(ws, data, user);
      case 'linkReq': return this.onLinkReq(ws, data, user);
      case 'linkRes': return this.onLinkRes(ws, data, user);
      case 'fetchLog': return this.onFetchLog(ws, data, user);
      case 'fetchNoteLog': return this.onFetchNoteLog(ws, data, user);
      case 'mark': return this.onMark(data, user);
      case 'activity': return this.onActivity(ws, data, user);
      case 'setProfile': return this.onSetProfile(data, user);
      case 'drop': return this.onDrop(ws, data, user);
      case 'hide': return this.onHide(ws, data, user);
      case 'unhide': return this.onUnhide(ws, data, user);

      case 'enterSpace': return this.onEnterSpace(ws, data, user);
      case 'exitSpace': return this.onExitSpace(ws, data, user);

      case 'avOn': return this.onAvOn(ws, data, user);
      case 'avOff': return this.avOff(ws, user);
      case 'logout': return this.onLogout(user);
      case 'avOffer': return this.relayAv(user, data, 'avOffer', 'offer');
      case 'avAnswer': return this.relayAv(user, data, 'avAnswer', 'answer');
      case 'avCand': return this.relayAv(user, data, 'avCand', 'candidate');

      case 'ctlEject': return this.onCtlEject(ws, data, user);
      case 'ctlPause': return this.onCtlPause(ws, data, user, 'paused');
      case 'ctlSilence': return this.onCtlPause(ws, data, user, 'silenced');
      case 'ctlBar': return this.onCtlBar(ws, data, user);
      case 'ctlUnbar': return this.onCtlUnbar(ws, data);
      case 'ctlUnbarIp': return this.onCtlUnbarIp(ws, data);
      case 'ctlLift': return this.onCtlLift(ws, data);
      case 'ctlNotice': return this.onCtlNotice(ws, data, user);
      case 'ctlDrop': return this.onCtlDrop(ws, data, user);
      case 'ctlList': return this.onCtlList(ws);
      case 'ctlAnnounce': return this.onCtlAnnounce(ws, data);
      case 'ctlPace': return this.onCtlPace(ws, data);
      case 'ctlClear': return this.onCtlClear(ws, data);
      case 'ctlFx': return this.onCtlFx(ws, data, user);
      case 'ctlFxAll': return this.onCtlFxAll(ws);
      case 'ctlCut': return this.onCtlCut(ws, data, user);
      case 'ctlAccounts': return this.onCtlAccounts(ws, user);
      case 'ctlSetRole': return this.onCtlSetRole(ws, data, user);
    }
  }

  // ----- open -----

  reject(ws, type, message, code = 4001) {
    send(ws, { type, message });
    try { ws.close(code, type); } catch { /* ignore */ }
  }

  // ----- accounts (D1) -----

  ensureSchema() {
    if (!this.schemaReady) {
      const db = this.env.DB;
      this.schemaReady = db.batch([
        db.prepare('CREATE TABLE IF NOT EXISTS accounts (id TEXT PRIMARY KEY, username TEXT NOT NULL, username_lc TEXT NOT NULL UNIQUE, salt TEXT NOT NULL, hash TEXT NOT NULL, role TEXT, created INTEGER NOT NULL)'),
        db.prepare('CREATE TABLE IF NOT EXISTS sessions (token_hash TEXT PRIMARY KEY, account_id TEXT NOT NULL, created INTEGER NOT NULL)'),
        db.prepare('CREATE INDEX IF NOT EXISTS idx_sessions_account ON sessions(account_id)')
      ]).catch((err) => { this.schemaReady = null; throw err; });
    }
    return this.schemaReady;
  }

  accountByName(name) {
    return this.env.DB.prepare('SELECT id, username, role, salt, hash FROM accounts WHERE username_lc = ?').bind(lc(name)).first();
  }

  accountByToken(tokenHash) {
    return this.env.DB.prepare(
      'SELECT a.id, a.username, a.role FROM sessions s JOIN accounts a ON a.id = s.account_id WHERE s.token_hash = ? AND s.created > ?'
    ).bind(tokenHash, Date.now() - SESSION_TTL_MS).first();
  }

  async accountIdExists(id) {
    return !!(await this.env.DB.prepare('SELECT 1 AS x FROM accounts WHERE id = ?').bind(id).first());
  }

  // Slows down password guessing and account spam from one address.
  authBlocked(ip) {
    const e = this.authFails.get(ip);
    return !!e && e.n >= 8 && Date.now() - e.t < 10 * 60 * 1000;
  }

  authFail(ip) {
    const now = Date.now();
    let e = this.authFails.get(ip);
    if (!e || now - e.t >= 10 * 60 * 1000) e = { n: 0, t: now };
    e.n++;
    this.authFails.set(ip, e);
  }

  signupBlocked(ip) {
    const recent = (this.signups.get(ip) || []).filter((t) => Date.now() - t < 60 * 60 * 1000);
    this.signups.set(ip, recent);
    return recent.length >= 5;
  }

  // ----- open (sign in as guest, log in, sign up, or resume a saved session) -----

  async onOpen(ws, data, att) {
    if (att.name || this.opening.has(ws)) return;
    this.opening.add(ws);
    try {
      await this.doOpen(ws, data, att);
    } catch (err) {
      console.error('open failed:', err);
      this.reject(ws, 'denied', 'Something went wrong. Please try again.');
    } finally {
      this.opening.delete(ws);
    }
  }

  async doOpen(ws, data, att) {
    const ip = att.ip || 'unknown';
    const db = this.env.DB;
    const mode = ['guest', 'login', 'signup', 'resume'].includes(data.mode) ? data.mode : 'guest';
    const password = typeof data.password === 'string' ? data.password : '';
    let name = cleanName(data.name);
    let account = null;   // { id, username, role, ... }
    let tokenHash = null;

    // 1. Who is this?
    if (mode !== 'guest') {
      if (!db) return this.reject(ws, 'denied', 'Accounts are not set up on this server yet');
      if (this.authBlocked(ip)) return this.reject(ws, 'denied', 'Too many attempts. Try again in a few minutes.');
      await this.ensureSchema();

      if (mode === 'resume') {
        const th = typeof data.token === 'string' && data.token ? await sha256Hex(data.token) : '';
        account = th ? await this.accountByToken(th) : null;
        if (!account) return this.reject(ws, 'denied', 'Session expired. Please log in again.');
        tokenHash = th;
      } else if (mode === 'login') {
        const found = name ? await this.accountByName(name) : null;
        if (!(await verifyPassword(password, found))) {
          this.authFail(ip);
          return this.reject(ws, 'denied', 'Wrong username or password');
        }
        account = found;
      } else {
        if (!ACCOUNT_NAME_RE.test(name) || GUEST_NAME_RE.test(name)) {
          return this.reject(ws, 'denied', 'Usernames are 3-20 letters, numbers, _ . or - (and cannot look like "Guest1234")');
        }
        if (password.length < 6 || password.length > 128) {
          return this.reject(ws, 'denied', 'Password must be 6-128 characters');
        }
        if (this.signupBlocked(ip)) return this.reject(ws, 'denied', 'Too many accounts created from this connection. Try again later.');
        if (await this.accountByName(name)) return this.reject(ws, 'denied', 'That username is taken');
      }
      if (account) name = account.username;
    }
    if (!name) return this.reject(ws, 'denied', 'Choose a username');

    // 2. Role: saved on the account, plus any password typed in the Admin login box.
    let isOwner = false;
    let isAdmin = false;
    let isVIP = false;
    const saved = account ? account.role : null;
    if (saved === 'owner') { isOwner = true; isAdmin = true; }
    else if (saved === 'admin') isAdmin = true;
    else if (saved === 'vip') isVIP = true;

    const key = typeof data.key === 'string' ? data.key : '';
    let promoteOwner = false;
    if (key) {
      if (safeEqual(key, this.env.OWNER_PASSWORD)) { isOwner = true; isAdmin = true; promoteOwner = saved !== 'owner'; }
      else if (safeEqual(key, this.env.ADMIN_PASSWORD)) isAdmin = true;
      else if (safeEqual(key, this.env.VIP_PASSWORD)) isVIP = true;
      else return this.reject(ws, 'denied', 'Incorrect password');
    }

    if (!isAdmin && this.barredNames.has(lc(name))) {
      return this.reject(ws, 'banned', 'You are banned from this server', 4003);
    }

    // 3. Guests may not take a name that belongs to an account.
    let guestUuid = null;
    if (mode === 'guest') {
      if (db) {
        await this.ensureSchema();
        if (await this.accountByName(name)) {
          return this.reject(ws, 'denied', 'That username belongs to an account. Log in, or choose another name.');
        }
      }
      const wanted = typeof data.uuid === 'string' && UUID_RE.test(data.uuid) ? data.uuid : null;
      guestUuid = wanted && !(db && await this.accountIdExists(wanted)) ? wanted : crypto.randomUUID();
    }

    // 4. Create / update the account and issue a session.
    let token = null;
    if (mode === 'signup') {
      const salt = randomHex(16);
      const hash = await hashPassword(password, salt);
      const id = crypto.randomUUID();
      try {
        await db.prepare('INSERT INTO accounts (id, username, username_lc, salt, hash, role, created) VALUES (?, ?, ?, ?, ?, NULL, ?)')
          .bind(id, name, lc(name), salt, hash, Date.now()).run();
      } catch {
        return this.reject(ws, 'denied', 'That username is taken');
      }
      account = { id, username: name, role: null };
      this.signups.get(ip).push(Date.now());
    }
    if (promoteOwner && account) {
      await db.prepare('UPDATE accounts SET role = ? WHERE id = ?').bind('owner', account.id).run();
      account.role = 'owner';
    }
    if (mode === 'login' || mode === 'signup') {
      token = randomHex(32);
      tokenHash = await sha256Hex(token);
      await db.prepare('INSERT INTO sessions (token_hash, account_id, created) VALUES (?, ?, ?)').bind(tokenHash, account.id, Date.now()).run();
      await db.prepare('DELETE FROM sessions WHERE created < ?').bind(Date.now() - SESSION_TTL_MS).run();
    }

    // Accounts use their account id as the member id, so DMs follow them across devices.
    const uuid = account ? account.id : guestUuid;

    let finalName = name;
    let staleAv = null;
    let staleSpaces = [];
    const clash = this.findMember(name);
    if (clash) {
      if (clash.user.uuid === uuid || account) {
        // Same person reconnecting, or the account owner taking their name back from a guest.
        staleAv = clash.user.av;
        staleSpaces = clash.user.spaces || [];
        clash.ws.serializeAttachment({ ip: clash.user.ip });
        if (clash.user.uuid !== uuid) send(clash.ws, { type: 'denied', message: 'That username was claimed by its account owner' });
        try { clash.ws.close(clash.user.uuid === uuid ? 4000 : 4001, 'Replaced'); } catch { /* ignore */ }
      } else if (/^guest$/i.test(name)) {
        do {
          finalName = `Guest${1000 + Math.floor(Math.random() * 9000)}`;
        } while (this.findMember(finalName));
      } else {
        return this.reject(ws, 'denied', 'That username is already in use');
      }
    }

    ws.serializeAttachment({
      ip, uuid, name: finalName, isOwner, isAdmin, isVIP, av: null, pending: [], spaces: [],
      acct: !!account, th: tokenHash || undefined
    });

    send(ws, { type: 'ready', uuid, name: finalName, isOwner, isAdmin, isVIP, account: !!account, token: token || undefined });
    send(ws, { type: 'linkList', links: this.linkListFor(uuid) });
    send(ws, { type: 'hiddenList', members: [...(this.hidden.get(uuid)?.values() || [])] });
    for (const b of AV_BOARDS) {
      send(ws, { type: 'avMembers', board: b, members: this.avMembers(b) });
    }
    this.broadcast({ type: 'roster', members: this.getRoster() });
    if (staleAv) {
      this.broadcast({ type: 'avLeft', name: finalName, board: staleAv });
      this.broadcast({ type: 'avMembers', board: staleAv, members: this.avMembers(staleAv) });
    }
    for (const code of staleSpaces) this.broadcastSpaceMembers(code);
  }

  async onLogout(user) {
    if (!user.th || !this.env.DB) return;
    try {
      await this.env.DB.prepare('DELETE FROM sessions WHERE token_hash = ?').bind(user.th).run();
    } catch (err) { console.error('logout failed:', err); }
  }

  linkListFor(uuid) {
    const out = [];
    for (const [thread, parts] of this.linkMembers) {
      if (!parts.some((p) => p.uuid === uuid)) continue;
      const other = parts.find((p) => p.uuid !== uuid);
      if (other) out.push({ thread, with: other.name });
    }
    return out;
  }

  // ----- spaces -----

  onEnterSpace(ws, data, user) {
    const code = normSpace(data.code);
    if (code.length < 3) {
      send(ws, { type: 'fault', message: 'Room codes need 3-20 letters, numbers or dashes' });
      return;
    }
    const restore = !!data.restore;
    const spaces = user.spaces || [];
    if (spaces.includes(code)) {
      send(ws, { type: 'spaceIn', code, restore });
      send(ws, { type: 'spaceMembers', code, members: this.spaceMembers(code) });
      return;
    }
    if (spaces.length >= MAX_SPACES_PER_USER) {
      send(ws, { type: 'fault', message: `You can be in at most ${MAX_SPACES_PER_USER} rooms` });
      return;
    }

    const board = 'space:' + code;
    if (!this.boards[board]) {
      if (this.spaceCount() >= MAX_SPACES_TOTAL) this.pruneSpaces();
      if (this.spaceCount() >= MAX_SPACES_TOTAL) {
        send(ws, { type: 'fault', message: 'Too many rooms right now, try again later' });
        return;
      }
      this.boards[board] = [];
    }

    user.spaces = [...spaces, code];
    ws.serializeAttachment(user);
    send(ws, { type: 'spaceIn', code, restore });
    this.broadcastSpaceMembers(code);
  }

  onExitSpace(ws, data, user) {
    const code = normSpace(data.code);
    if (!(user.spaces || []).includes(code)) return;
    user.spaces = user.spaces.filter((r) => r !== code);
    ws.serializeAttachment(user);
    send(ws, { type: 'spaceOut', code });
    this.broadcastSpaceMembers(code);
  }

  // ----- entries -----

  buildItem(user, data, body, media) {
    const profile = this.profiles.get(lc(user.name));
    return {
      id: crypto.randomUUID(),
      by: user.name,
      body,
      ts: this.nextTimestamp(),
      role: roleOf(user),
      color: profile?.color || 'default',
      ref: typeof data.ref === 'string' ? data.ref.slice(0, 64) : null,
      marks: {},
      media
    };
  }

  readContent(ws, data) {
    const body = typeof data.body === 'string' ? data.body.slice(0, MAX_TEXT) : '';
    let media = null;
    if (data.media != null) {
      const u = data.media;
      const okData = typeof u === 'string' && u.startsWith('data:image/') && u.length <= MAX_MEDIA_CHARS;
      if (!okData) {
        send(ws, { type: 'fault', message: 'Image is invalid or too large' });
        return null;
      }
      media = u;
    }
    if (!body.trim() && !media) return null;
    return { body, media };
  }

  checkPaused(ws, user) {
    const until = this.pausedUntil.get(lc(user.name));
    if (until && until > Date.now()) {
      send(ws, { type: 'fault', message: `You are muted for another ${Math.ceil((until - Date.now()) / 1000)}s` });
      return false;
    }
    return true;
  }

  limitOf(user) {
    const a = this.limitedIPs.get(user.ip);
    const b = this.limitedNames.get(lc(user.name));
    return a === 'mute' || b === 'mute' ? 'mute' : a || b || null;
  }

  checkLimited(ws, user, isLink) {
    const r = this.limitOf(user);
    if (r === 'mute' || (r === 'dm' && !isLink)) {
      send(ws, { type: 'fault', message: r === 'mute' ? 'You are muted and cannot send messages' : 'You can only send direct messages' });
      return false;
    }
    return true;
  }

  checkBurst(ws, user) {
    if (isStaff(user) || user.isVIP) return true;
    const key = lc(user.name);
    const now = Date.now();
    const recent = (this.recentPosts.get(key) || []).filter((t) => now - t < BURST_WINDOW_MS);
    const until = this.autoPaceUntil.get(key) || 0;
    if (until > now && recent.length && now - recent[recent.length - 1] < AUTO_PACE_GAP_MS) {
      const wait = Math.ceil((AUTO_PACE_GAP_MS - (now - recent[recent.length - 1])) / 1000);
      send(ws, { type: 'fault', message: `Slow mode: wait ${wait}s between messages` });
      return false;
    }
    recent.push(now);
    this.recentPosts.set(key, recent);
    if (recent.length >= BURST_COUNT && until <= now) {
      this.autoPaceUntil.set(key, now + AUTO_PACE_MS);
      send(ws, { type: 'fault', message: 'You were sending messages too fast. Slow mode is on for 5 minutes.' });
    }
    return true;
  }

  onEntry(ws, data, user) {
    if (!validBoard(data.board) || !this.canAccessBoard(user, data.board)) return;
    const content = this.readContent(ws, data);
    if (!content) return;
    if (!this.checkPaused(ws, user)) return;
    if (!this.checkLimited(ws, user, false)) return;

    const key = lc(user.name);
    if (this.pace.enabled && !isStaff(user)) {
      const last = this.lastPostAt.get(key);
      if (last && Date.now() - last < this.pace.duration * 1000) {
        send(ws, { type: 'fault', message: `Slow mode: wait ${this.pace.duration}s between messages` });
        return;
      }
    }
    if (!this.checkBurst(ws, user)) return;
    this.lastPostAt.set(key, Date.now());

    const item = this.buildItem(user, data, content.body, content.media);
    item.board = data.board;

    const list = this.boardList(data.board, true);
    if (!list) return;
    list.push(item);
    bg(this.ctx.storage.put(bKey(item), item));
    while (list.length > MAX_BOARD_LOG) {
      bg(this.ctx.storage.delete(bKey(list.shift())));
    }

    this.broadcastBoard(data.board, { type: 'entry', item });
  }

  onNote(ws, data, user) {
    if (!this.isLinkMember(data.thread, user.uuid)) return;
    const content = this.readContent(ws, data);
    if (!content) return;
    if (!this.checkPaused(ws, user)) return;
    if (!this.checkLimited(ws, user, true)) return;

    const other = this.linkMembers.get(data.thread).find((p) => p.uuid !== user.uuid);
    if (other) {
      if (this.isHiddenBy(other.uuid, user.uuid)) {
        send(ws, { type: 'fault', message: "You can't send messages to this user" });
        return;
      }
      if (this.isHiddenBy(user.uuid, other.uuid)) {
        send(ws, { type: 'fault', message: 'You blocked this user. Unblock them to send messages.' });
        return;
      }
    }
    if (!this.checkBurst(ws, user)) return;

    const item = this.buildItem(user, data, content.body, content.media);
    item.thread = data.thread;

    if (!this.links.has(data.thread)) this.links.set(data.thread, []);
    const list = this.links.get(data.thread);
    list.push(item);
    bg(this.ctx.storage.put(tKey(item), item));
    while (list.length > MAX_LINK_LOG) {
      bg(this.ctx.storage.delete(tKey(list.shift())));
    }

    const uuids = this.linkMembers.get(data.thread).map((p) => p.uuid);
    this.sendToUuids(uuids, { type: 'note', item });
  }

  onDrop(ws, data, user) {
    const mine = (m) => m && lc(m.by) === lc(user.name);
    if (data.priv) {
      if (!this.isLinkMember(data.thread, user.uuid)) return;
      const list = this.links.get(data.thread) || [];
      const i = list.findIndex((m) => m.id === data.id);
      if (i === -1 || !mine(list[i])) return;
      const [removed] = list.splice(i, 1);
      bg(this.ctx.storage.delete(tKey(removed)));
      this.sendToUuids(this.linkMembers.get(data.thread).map((p) => p.uuid),
        { type: 'noteDropped', thread: data.thread, id: removed.id });
      return;
    }
    if (!validBoard(data.board) || !this.canAccessBoard(user, data.board)) return;
    const list = this.boardList(data.board) || [];
    const i = list.findIndex((m) => m.id === data.id);
    if (i === -1 || !mine(list[i])) return;
    const [removed] = list.splice(i, 1);
    bg(this.ctx.storage.delete(bKey(removed)));
    this.broadcastBoard(data.board, { type: 'dropped', id: removed.id, board: data.board });
  }

  onFetchLog(ws, data, user) {
    if (!validBoard(data.board) || !this.canAccessBoard(user, data.board)) return;
    send(ws, { type: 'log', board: data.board, items: this.boardList(data.board) || [] });
  }

  onFetchNoteLog(ws, data, user) {
    if (!this.isLinkMember(data.thread, user.uuid)) return;
    send(ws, { type: 'noteLog', thread: data.thread, items: this.links.get(data.thread) || [] });
  }

  onMark(data, user) {
    if (typeof data.emoji !== 'string' || !EMOJI_RE.test(data.emoji)) return;

    let item;
    let recipients = null;
    if (data.priv) {
      if (!this.isLinkMember(data.thread, user.uuid)) return;
      item = (this.links.get(data.thread) || []).find((m) => m.id === data.id);
      recipients = this.linkMembers.get(data.thread).map((p) => p.uuid);
    } else {
      if (!validBoard(data.board) || !this.canAccessBoard(user, data.board)) return;
      item = (this.boardList(data.board) || []).find((m) => m.id === data.id);
    }
    if (!item) return;

    const who = item.marks[data.emoji] || [];
    const i = who.indexOf(user.name);
    if (i === -1) who.push(user.name);
    else who.splice(i, 1);
    if (who.length) item.marks[data.emoji] = who;
    else delete item.marks[data.emoji];

    bg(this.ctx.storage.put(data.priv ? tKey(item) : bKey(item), item));

    const update = {
      type: 'markUpdate',
      id: item.id,
      marks: item.marks,
      priv: !!data.priv,
      board: item.board,
      thread: item.thread
    };
    if (recipients) this.sendToUuids(recipients, update);
    else this.broadcastBoard(item.board, update);
  }

  onActivity(ws, data, user) {
    const active = !!data.active;
    if (data.priv) {
      if (!this.isLinkMember(data.thread, user.uuid)) return;
      const others = this.linkMembers.get(data.thread).map((p) => p.uuid).filter((u) => u !== user.uuid);
      this.sendToUuids(others, { type: 'activity', name: user.name, active, priv: true, thread: data.thread });
    } else if (validBoard(data.board) && this.canAccessBoard(user, data.board)) {
      this.broadcastBoard(data.board, { type: 'activity', name: user.name, active, priv: false, board: data.board }, ws);
    }
  }

  onSetProfile(data, user) {
    const color = COLORS.includes(data.color) ? data.color : 'default';
    this.profiles.set(lc(user.name), { color });
    this.saveMeta();
  }

  // ----- hiding members -----

  isHiddenBy(hiderUuid, otherUuid) {
    return !!this.hidden.get(hiderUuid)?.has(otherUuid);
  }

  sendHiddenList(ws, user) {
    send(ws, { type: 'hiddenList', members: [...(this.hidden.get(user.uuid)?.values() || [])] });
  }

  onHide(ws, data, user) {
    const t = this.findMember(data.target);
    if (!t || t.user.uuid === user.uuid) {
      send(ws, { type: 'fault', message: 'User not online' });
      return;
    }
    const mine = this.hidden.get(user.uuid) || new Map();
    if (mine.size >= MAX_HIDDEN && !mine.has(t.user.uuid)) {
      send(ws, { type: 'fault', message: 'Your block list is full' });
      return;
    }
    mine.set(t.user.uuid, t.user.name);
    this.hidden.set(user.uuid, mine);
    this.saveMeta();
    this.sendHiddenList(ws, user);
  }

  onUnhide(ws, data, user) {
    const mine = this.hidden.get(user.uuid);
    if (!mine) return;
    const name = lc(data.name ?? '');
    for (const [id, n] of mine) if (lc(n) === name) mine.delete(id);
    if (!mine.size) this.hidden.delete(user.uuid);
    this.saveMeta();
    this.sendHiddenList(ws, user);
  }

  // ----- private threads -----

  onLinkReq(ws, data, user) {
    const target = this.findMember(data.target);
    if (!target || target.user.uuid === user.uuid) {
      send(ws, { type: 'fault', message: 'User not online' });
      return;
    }
    if (this.isHiddenBy(target.user.uuid, user.uuid)) {
      send(ws, { type: 'fault', message: "You can't message this user" });
      return;
    }
    if (this.isHiddenBy(user.uuid, target.user.uuid)) {
      send(ws, { type: 'fault', message: 'You blocked this user. Unblock them first.' });
      return;
    }

    const existing = this.findLink(user.uuid, target.user.uuid);
    if (existing) {
      send(ws, { type: 'linkOk', thread: existing, with: target.user.name });
      return;
    }

    const pending = [...(target.user.pending || []).filter((u) => u !== user.uuid), user.uuid].slice(-10);
    target.ws.serializeAttachment({ ...target.user, pending });
    send(target.ws, { type: 'linkReq', from: user.name });
  }

  onLinkRes(ws, data, user) {
    const requester = this.findMember(data.from);
    if (!requester) return;

    const pending = user.pending || [];
    if (!pending.includes(requester.user.uuid)) return;
    ws.serializeAttachment({ ...user, pending: pending.filter((u) => u !== requester.user.uuid) });

    if (!data.accepted) {
      send(requester.ws, { type: 'linkNo', by: user.name });
      return;
    }

    let thread = this.findLink(user.uuid, requester.user.uuid);
    if (!thread) {
      thread = crypto.randomUUID();
      this.linkMembers.set(thread, [
        { uuid: user.uuid, name: user.name },
        { uuid: requester.user.uuid, name: requester.user.name }
      ]);
      this.links.set(thread, []);
      this.saveMeta();
    }
    send(ws, { type: 'linkOk', thread, with: requester.user.name });
    send(requester.ws, { type: 'linkOk', thread, with: user.name });
  }

  findLink(uuidA, uuidB) {
    for (const [thread, parts] of this.linkMembers) {
      if (parts.some((p) => p.uuid === uuidA) && parts.some((p) => p.uuid === uuidB)) return thread;
    }
    return null;
  }

  // ----- audio (signalling only) -----

  onAvOn(ws, data, user) {
    const board = data.board;
    if (!AV_BOARDS.includes(board) || user.av === board) return;
    if (user.av) this.avOff(ws, user);

    const peers = this.avMembers(board);
    user.av = board;
    ws.serializeAttachment(user);

    send(ws, { type: 'avJoined', board, peers });
    this.broadcast({ type: 'avMembers', board, members: this.avMembers(board) });
  }

  avOff(ws, user) {
    const board = user.av;
    if (!board) return;
    user.av = null;
    ws.serializeAttachment(user);
    this.broadcast({ type: 'avLeft', name: user.name, board });
    this.broadcast({ type: 'avMembers', board, members: this.avMembers(board) });
  }

  relayAv(user, data, type, key) {
    if (!user.av || data[key] == null) return;
    if (JSON.stringify(data[key]).length > 20000) return;
    const target = this.findMember(data.to);
    if (!target || target.user.av !== user.av) return;
    send(target.ws, { type, from: user.name, board: user.av, [key]: data[key] });
  }

  // ----- control actions -----

  ok(ws, message) {
    send(ws, { type: 'ctlOk', message });
  }

  onCtlEject(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.target);
    if (!t) return;
    const reason = cleanReason(data.reason);
    send(t.ws, {
      type: 'ejected',
      message: `You have been kicked${reason ? ': ' + reason : ''}`,
      redirectUrl: 'https://google.com'
    });
    try { t.ws.close(4002, 'ejected'); } catch { /* ignore */ }
    this.ok(ws, `Kicked ${t.user.name}`);
  }

  onCtlPause(ws, data, admin, eventType) {
    const t = this.modTarget(ws, admin, data.target);
    if (!t) return;
    const duration = clamp(data.duration, 1, 86400, 60);
    const reason = cleanReason(data.reason);
    this.pausedUntil.set(lc(t.user.name), Date.now() + duration * 1000);
    const verb = eventType === 'paused' ? 'timed out' : 'muted';
    send(t.ws, {
      type: eventType,
      duration,
      message: `You have been ${verb} for ${duration}s${reason ? ': ' + reason : ''}`
    });
    this.ok(ws, `${verb[0].toUpperCase()}${verb.slice(1)} ${t.user.name} for ${duration}s`);
  }

  onCtlBar(ws, data, admin) {
    const name = cleanName(data.target);
    if (!name) return;
    const banType = ['username', 'ip', 'both'].includes(data.banType) ? data.banType : 'ip';
    const mode = BAR_MODES.includes(data.mode) ? data.mode : 'full';
    const barName = banType !== 'ip';
    const barIp = banType !== 'username';

    const t = this.findMember(name);
    if (t && !this.canModerate(admin, t.user)) {
      send(ws, { type: 'fault', message: 'Cannot moderate this user' });
      return;
    }
    if (!t && !barName) {
      send(ws, { type: 'fault', message: 'User is not online (an IP ban needs an online user)' });
      return;
    }

    const reason = cleanReason(data.reason);
    const ip = t && t.user.ip && t.user.ip !== 'unknown' ? t.user.ip : null;

    if (mode === 'full') {
      if (barName) this.barredNames.add(lc(name));
      if (barIp && ip) this.barredIPs.add(ip);
      this.saveMeta();
      if (t) {
        send(t.ws, { type: 'barred', message: `You have been banned${reason ? ': ' + reason : ''}` });
        try { t.ws.close(4003, 'barred'); } catch { /* ignore */ }
      }
      this.ok(ws, `Banned ${name}`);
      return;
    }

    if (barName) this.limitedNames.set(lc(name), mode);
    if (barIp && ip) this.limitedIPs.set(ip, mode);
    this.saveMeta();
    if (t) {
      send(t.ws, {
        type: 'limited',
        message: (mode === 'mute'
          ? 'You have been muted and can no longer send messages'
          : 'You can no longer chat in channels or rooms, but you can still send DMs') + (reason ? ': ' + reason : '')
      });
    }
    this.ok(ws, `${mode === 'mute' ? 'Muted' : 'Chat-blocked'} ${name} (until removed in the Bans tab)`);
  }

  onCtlUnbar(ws, data) {
    this.barredNames.delete(lc(data.name ?? ''));
    this.saveMeta();
    this.ok(ws, `Unbanned ${data.name}`);
    this.onCtlList(ws);
  }

  onCtlUnbarIp(ws, data) {
    this.barredIPs.delete(data.ip);
    this.saveMeta();
    this.ok(ws, `Unbanned IP ${data.ip}`);
    this.onCtlList(ws);
  }

  onCtlLift(ws, data) {
    if (data.kind === 'ip') this.limitedIPs.delete(data.value);
    else if (data.kind === 'user') this.limitedNames.delete(lc(data.value ?? ''));
    else return;
    this.saveMeta();
    this.ok(ws, `Removed restriction on ${data.value}`);
    this.onCtlList(ws);
  }

  onCtlNotice(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.target);
    if (!t) return;
    const key = lc(t.user.name);
    const count = (this.notices.get(key) || 0) + 1;
    this.notices.set(key, count);
    this.saveMeta();
    send(t.ws, { type: 'notice', message: cleanReason(data.reason) || 'You have been warned', count });
    this.ok(ws, `Warned ${t.user.name} (warning #${count})`);
  }

  onCtlDrop(ws, data, user) {
    if (!validBoard(data.board) || !this.canAccessBoard(user, data.board)) return;
    const list = this.boardList(data.board);
    if (!list) return;
    const i = list.findIndex((m) => m.id === data.id);
    if (i === -1) return;
    const [removed] = list.splice(i, 1);
    bg(this.ctx.storage.delete(bKey(removed)));
    this.broadcastBoard(data.board, { type: 'dropped', id: removed.id, board: data.board });
    this.ok(ws, 'Message deleted');
  }

  onCtlList(ws) {
    const restricted = [
      ...[...this.limitedNames].map(([value, mode]) => ({ kind: 'user', value, mode })),
      ...[...this.limitedIPs].map(([value, mode]) => ({ kind: 'ip', value, mode }))
    ];
    send(ws, { type: 'barList', names: [...this.barredNames], ips: [...this.barredIPs], restricted });
  }

  onCtlAnnounce(ws, data) {
    const message = typeof data.message === 'string' ? data.message.trim().slice(0, 500) : '';
    if (!message) return;
    this.broadcast({ type: 'announce', message });
    this.ok(ws, 'Broadcast sent');
  }

  onCtlPace(ws, data) {
    this.pace = { enabled: !!data.enabled, duration: clamp(data.duration, 1, 3600, 5) };
    this.saveMeta();
    this.ok(ws, this.pace.enabled ? `Slow mode on (${this.pace.duration}s)` : 'Slow mode off');
  }

  onCtlClear(ws, data) {
    if (!BOARDS.includes(data.board)) return;
    const keys = this.boards[data.board].map(bKey);
    this.boards[data.board] = [];
    if (keys.length) bg(this.ctx.storage.delete(keys));
    this.broadcast({ type: 'cleared', board: data.board });
    this.ok(ws, `Cleared #${data.board}`);
  }

  onCtlFx(ws, data, admin) {
    if (!EFFECTS.has(data.effect)) return;
    const t = this.modTarget(ws, admin, data.target);
    if (!t) return;
    send(t.ws, { type: data.effect });
    this.ok(ws, `Sent ${data.effect} to ${t.user.name}`);
  }

  onCtlFxAll(ws) {
    this.broadcast({ type: 'confetti' });
    this.ok(ws, 'Confetti sent to everyone');
  }

  onCtlCut(ws, data, admin) {
    const t = this.modTarget(ws, admin, data.target);
    if (!t) return;
    send(t.ws, { type: 'forceDisconnect' });
    try { t.ws.close(4004, 'cut'); } catch { /* ignore */ }
    this.ok(ws, `Disconnected ${t.user.name}`);
  }

  // ----- owner: manage accounts -----

  async onCtlAccounts(ws, user) {
    if (!user.isOwner) return;
    if (!this.env.DB) { send(ws, { type: 'fault', message: 'Accounts are not set up on this server yet' }); return; }
    await this.ensureSchema();
    const { results } = await this.env.DB.prepare('SELECT username, role FROM accounts ORDER BY username_lc LIMIT 1000').all();
    send(ws, { type: 'acctList', accounts: results || [] });
  }

  async onCtlSetRole(ws, data, user) {
    if (!user.isOwner || !this.env.DB) return;
    const role = ['admin', 'vip', 'none'].includes(data.role) ? data.role : null;
    if (!role) return;
    await this.ensureSchema();
    const acct = await this.accountByName(cleanName(data.target));
    if (!acct) { send(ws, { type: 'fault', message: 'No such account' }); return; }
    if (acct.role === 'owner') { send(ws, { type: 'fault', message: 'Owner accounts cannot be changed here' }); return; }

    await this.env.DB.prepare('UPDATE accounts SET role = ? WHERE id = ?').bind(role === 'none' ? null : role, acct.id).run();

    const label = role === 'admin' ? 'a Mod (admin)' : role === 'vip' ? 'a VIP' : 'a regular member';
    const t = this.findMember(acct.username);
    if (t && t.user.acct) {
      const u = { ...t.user, isOwner: false, isAdmin: role === 'admin', isVIP: role === 'vip' };
      t.ws.serializeAttachment(u);
      send(t.ws, { type: 'role', isOwner: false, isAdmin: u.isAdmin, isVIP: u.isVIP, message: `You are now ${label}` });
      this.broadcast({ type: 'roster', members: this.getRoster() });
    }
    this.ok(ws, `${acct.username} is now ${label}`);
    await this.onCtlAccounts(ws, user);
  }
}

// ---------- Worker entry point ----------

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const wantsSocket = request.headers.get('Upgrade') === 'websocket';

    if (wantsSocket || url.pathname === '/s') {
      if (!wantsSocket) return new Response('Not found', { status: 426 });
      const hub = env.HUB.get(env.HUB.idFromName('global'));
      return hub.fetch(request);
    }

    return env.ASSETS.fetch(request);
  }
};
