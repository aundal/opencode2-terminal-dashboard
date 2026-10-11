import http from 'http';
import path from 'path';
import fs from 'fs';
import os from 'os';
import net from 'net';
import crypto from 'crypto';
import { spawn } from 'child_process';
import { fileURLToPath } from 'url';
import process from 'process';

const DASHBOARD_PORT = 31337;
const LEASE_PORT = 31338;
const HEARTBEAT_URL = `http://127.0.0.1:${DASHBOARD_PORT}/api/heartbeat`;
const RUNNING_DECAY_MS = 10 * 60 * 1000;
const STALE_SUBAGENT_PRUNE_MS = 30000;
const STALE_HEARTBEAT_PURGE_MS = 15000;
const TOOL_CALL_STALE_MS = 5 * 60 * 1000;
const TURN_QUIET_MS = 15000;
const ACTIVE_POLL_MS = 5000;
const SESSION_POLL_MS = 10000;
const INTERACTION_POLL_MS = 4000;
// Hvor lÃ¦nge et vindue holder den session det viser Ã¥ben, regnet fra sidste
// presence. Vinduerne pulser hver 5. sekund. 90 sekunder overlever tung
// timer-throttling og en dvale uden at flÃ¥ kortene, men betyder ogsÃ¥ at et
// lukket vindue forsvinder hurtigt i stedet for at blive hÃ¦ngende i timevis.
const VIEWED_OPEN_MS = 90 * 1000;
const MSG_COUNT_TTL_MS = 120000;
const SESSION_LIST_LIMIT = 200;
const CLOSED_SESSION_RETENTION_MS = 15000;
const COLD_CACHE_MS = 5 * 60 * 1000;
const PLUGIN_VERSION = '1.2.0';

// Module-level global rate limiter shared across all plugin listeners
const globalSessionThrottles = new Map();
const globalSessionLastState = new Map();

// Debug log helper (writes to C:\Users\<User>\opencode-debug.log only if DEBUG=1 or DEBUG=true)
const debugLogFile = path.join(os.homedir(), 'opencode-debug.log');
function pluginLog(msg) {
  if (process.env.DEBUG !== '1' && process.env.DEBUG !== 'true' && !process.env.OPENCODE_DEBUG) return;
  const time = new Date().toLocaleTimeString();
  try {
    fs.appendFileSync(debugLogFile, `[${time}] ${msg}\n`);
  } catch(e) {}
}

// Short ID helper: Extract the last 6 characters for debug visibility
function shortId(id) {
  if (!id || typeof id !== 'string') return 'none';
  return id.length > 6 ? `...${id.slice(-6)}` : id;
}

// Strict Session ID validation: Must start with 'ses_' to prevent Message IDs (msg_...) from leaking
function isSessionId(str) {
  if (typeof str !== 'string' || !str) return false;
  if (str.startsWith('msg_') || str.startsWith('prt_') || str.startsWith('part_') || str.startsWith('msg')) return false;
  return str.startsWith('ses_');
}

function findSessionId(event, session, ctx) {
  if (event?.properties) {
    if (typeof event.properties.sessionID === 'string' && isSessionId(event.properties.sessionID)) return event.properties.sessionID;
    if (typeof event.properties.sessionId === 'string' && isSessionId(event.properties.sessionId)) return event.properties.sessionId;
    if (typeof event.properties.session_id === 'string' && isSessionId(event.properties.session_id)) return event.properties.session_id;
    if (typeof event.properties.info?.sessionID === 'string' && isSessionId(event.properties.info.sessionID)) return event.properties.info.sessionID;
    if (typeof event.properties.part?.sessionID === 'string' && isSessionId(event.properties.part.sessionID)) return event.properties.part.sessionID;
  }
  if (event) {
    if (typeof event.sessionId === 'string' && isSessionId(event.sessionId)) return event.sessionId;
    if (typeof event.session_id === 'string' && isSessionId(event.session_id)) return event.session_id;
    if (typeof event.sessionID === 'string' && isSessionId(event.sessionID)) return event.sessionID;
    if (typeof event.part?.sessionID === 'string' && isSessionId(event.part.sessionID)) return event.part.sessionID;
  }
  if (session) {
    if (typeof session === 'string' && isSessionId(session)) return session;
    if (typeof session.id === 'string' && isSessionId(session.id)) return session.id;
  }
  return null;
}

function findParentId(event, session) {
  let parentId = null;
  if (event?.properties) {
    if (typeof event.properties.parentID === 'string') parentId = event.properties.parentID;
    else if (typeof event.properties.parentId === 'string') parentId = event.properties.parentId;
    else if (typeof event.properties.parent_id === 'string') parentId = event.properties.parent_id;
    else if (typeof event.properties.parentSessionID === 'string') parentId = event.properties.parentSessionID;
    else if (typeof event.properties.parent_session_id === 'string') parentId = event.properties.parent_session_id;
    else if (typeof event.properties.info?.parentID === 'string') parentId = event.properties.info.parentID;
    else if (typeof event.properties.info?.parentId === 'string') parentId = event.properties.info.parentId;
    else if (typeof event.properties.session?.parentID === 'string') parentId = event.properties.session.parentID;
  }
  if (!parentId && event) {
    if (typeof event.parentID === 'string') parentId = event.parentID;
    else if (typeof event.parentId === 'string') parentId = event.parentId;
    else if (typeof event.parent_id === 'string') parentId = event.parent_id;
  }
  if (!parentId && session) {
    if (typeof session.parentID === 'string') parentId = session.parentID;
    else if (typeof session.parentId === 'string') parentId = session.parentId;
    else if (typeof session.info?.parentID === 'string') parentId = session.info.parentID;
  }

  if (parentId && isSessionId(parentId)) {
    return parentId;
  }
  return null;
}

function findRawSessionTitle(event, session) {
  if (event?.properties) {
    if (typeof event.properties.title === 'string' && event.properties.title) {
      return event.properties.title;
    }
    if (event.properties.info && typeof event.properties.info.title === 'string' && event.properties.info.title) {
      return event.properties.info.title;
    }
    if (event.properties.task && typeof event.properties.task.title === 'string' && event.properties.task.title) {
      return event.properties.task.title;
    }
    if (event.properties.task && typeof event.properties.task.description === 'string' && event.properties.task.description) {
      return event.properties.task.description;
    }
  }
  if (session && typeof session.title === 'string' && session.title) return session.title;
  if (event && typeof event.title === 'string' && event.title) return event.title;
  return null;
}

// Fork detection: forks have title like "Something (fork #1)" and must never be nested as sub-agents
function isForkTitle(title) {
  return typeof title === 'string' && /\(fork #\d+\)/.test(title);
}

// Working directory: forward slashes so Windows and POSIX paths sort together,
// no case folding - the path is shown to the user as written.
function normalizeDirectory(value) {
  if (typeof value !== 'string' || !value.trim()) return null;
  return value.trim().replace(/\\/g, '/').replace(/\/+$/, '') || null;
}

// Clean title: remove "(@general subagent)" or similar suffixes
function cleanTitle(rawTitle) {
  if (!rawTitle) return null;
  let t = rawTitle.trim();
  t = t.replace(/\s*\(@[^)]*subagent[^)]*\)/gi, '');
  t = t.replace(/\s*\(@subagent\)/gi, '');
  t = t.replace(/\s*\(@general\)/gi, '');
  return t.trim();
}

function tokenTotal(tokens) {
  const normalized = normalizeTokens(tokens);
  if (!normalized) return 0;
  return normalized.input + normalized.output + normalized.reasoning + normalized.cache.read + normalized.cache.write;
}

function normalizeTokens(tokens) {
  if (!tokens || typeof tokens !== 'object') return undefined;
  const cache = tokens.cache && typeof tokens.cache === 'object' ? tokens.cache : {};
  const normalized = {
    input: typeof tokens.input === 'number' && isFinite(tokens.input) ? tokens.input : 0,
    output: typeof tokens.output === 'number' && isFinite(tokens.output) ? tokens.output : 0,
    reasoning: typeof tokens.reasoning === 'number' && isFinite(tokens.reasoning) ? tokens.reasoning : 0,
    cache: {
      read: typeof cache.read === 'number' && isFinite(cache.read) ? cache.read : 0,
      write: typeof cache.write === 'number' && isFinite(cache.write) ? cache.write : 0,
    }
  };
  return tokenTotalWithoutGuard(normalized) > 0 ? normalized : normalized;
}

function tokenTotalWithoutGuard(tokens) {
  return tokens.input + tokens.output + tokens.reasoning + tokens.cache.read + tokens.cache.write;
}

function tokenFingerprint(tokens) {
  const normalized = normalizeTokens(tokens);
  if (!normalized) return 'none';
  return [normalized.input, normalized.output, normalized.reasoning, normalized.cache.read, normalized.cache.write].join(':');
}

function preferSessionTokens(currentTokens, nextTokens) {
  if (!nextTokens || typeof nextTokens !== 'object') return currentTokens;
  if (!currentTokens || typeof currentTokens !== 'object') return nextTokens;
  return tokenTotal(nextTokens) >= tokenTotal(currentTokens) ? nextTokens : currentTokens;
}

function zeroTokensLike(tokens) {
  const normalized = normalizeTokens(tokens);
  if (!normalized) return { input: 0, output: 0, reasoning: 0, cache: { read: 0, write: 0 } };
  return {
    input: 0,
    output: 0,
    reasoning: 0,
    cache: { read: 0, write: 0 }
  };
}

function subtractTokens(totalTokens, baseTokens) {
  const total = normalizeTokens(totalTokens);
  if (!total) return undefined;
  const base = normalizeTokens(baseTokens) || zeroTokensLike(total);
  return {
    input: Math.max(0, total.input - base.input),
    output: Math.max(0, total.output - base.output),
    reasoning: Math.max(0, total.reasoning - base.reasoning),
    cache: {
      read: Math.max(0, total.cache.read - base.cache.read),
      write: Math.max(0, total.cache.write - base.cache.write),
    }
  };
}

function addTokens(a, b) {
  const left = normalizeTokens(a);
  const right = normalizeTokens(b);
  if (!left && !right) return undefined;
  const lhs = left || zeroTokensLike(right);
  const rhs = right || zeroTokensLike(left);
  return {
    input: lhs.input + rhs.input,
    output: lhs.output + rhs.output,
    reasoning: lhs.reasoning + rhs.reasoning,
    cache: {
      read: lhs.cache.read + rhs.cache.read,
      write: lhs.cache.write + rhs.cache.write,
    }
  };
}

function findActiveSubAgent(sessionId, sessionMap) {
  let best = null;
  for (const session of sessionMap.values()) {
    if (session.parentId === sessionId && (session.status === 'running' || session.status === 'asking_parent')) {
      if (!best || (session.lastActivityTime || 0) > (best.lastActivityTime || 0)) best = session;
    }
  }
  return best;
}

function isInterruptedError(value) {
  if (!value) return false;
  const text = String(value).toLowerCase();
  return text.includes('abort') || text.includes('cancel') || text.includes('interrupt');
}

function findAgentName(event, session) {
  if (event?.properties) {
    if (typeof event.properties.agent === 'string' && event.properties.agent) return event.properties.agent;
    if (event.properties.info && typeof event.properties.info.agent === 'string' && event.properties.info.agent) return event.properties.info.agent;
    if (event.properties.task && typeof event.properties.task.agent === 'string' && event.properties.task.agent) return event.properties.task.agent;
  }
  if (session && typeof session.agent === 'string' && session.agent) return session.agent;
  if (event && typeof event.agent === 'string' && event.agent) return event.agent;
  return null;
}

function modelToString(value) {
  // V2 carries models as objects ({ id, providerID }); V1 as plain strings.
  if (typeof value === 'string' && value) return value;
  if (value && typeof value === 'object') {
    const id = value.id || value.modelID || value.model;
    if (typeof id === 'string' && id) {
      const pid = value.providerID || value.provider;
      return typeof pid === 'string' && pid ? `${pid}/${id}` : id;
    }
  }
  return null;
}

function findModelName(event, session) {
  if (event?.properties) {
    const p = event.properties;
    const info = p.info && typeof p.info === 'object' ? p.info : null;
    const nested = info && info.info && typeof info.info === 'object' ? info.info : null;
    const direct = modelToString(p.model) || modelToString(p.modelID) ||
      (info ? modelToString(info.model) || modelToString(info.modelID) : null) ||
      (nested ? modelToString(nested.model) || modelToString(nested.modelID) : null);
    if (direct) return direct;
    // V2 AssistantMessage: flat { modelID, providerID }.
    // V2 UserMessage: { model: { providerID, modelID } }.
    if (info && typeof info.modelID === 'string' && info.modelID) {
      const pid = typeof info.providerID === 'string' && info.providerID ? info.providerID : null;
      return pid ? `${pid}/${info.modelID}` : info.modelID;
    }
    if (info && info.model && typeof info.model === 'object') {
      const mm = info.model;
      if (typeof mm.modelID === 'string' && mm.modelID) {
        return typeof mm.providerID === 'string' && mm.providerID ? `${mm.providerID}/${mm.modelID}` : mm.modelID;
      }
    }
  }
  if (session) {
    const fromSession = modelToString(session.model) ||
      (session.info && typeof session.info === 'object' ? modelToString(session.info.model) : null);
    if (fromSession) return fromSession;
  }
  if (event) {
    const fromEvent = modelToString(event.model);
    if (fromEvent) return fromEvent;
  }
  return null;
}

function formatModelName(rawModel) {
  if (!rawModel) return 'Claude Haiku 4.5';
  let m = rawModel.trim();
  if (m.includes('/')) m = m.split('/').pop();
  m = m.replace(/\(latest\)/gi, '').trim();
  
  if (m.toLowerCase().includes('claude')) {
    m = m.replace(/claude/i, 'Claude');
    m = m.replace(/haiku/i, 'Haiku');
    m = m.replace(/sonnet/i, 'Sonnet');
    m = m.replace(/opus/i, 'Opus');
  } else if (m.toLowerCase().includes('chatgpt')) {
    m = m.replace(/chatgpt/i, 'ChatGPT');
  } else if (m.toLowerCase().includes('gpt')) {
    m = m.replace(/gpt/i, 'GPT');
  } else if (m.toLowerCase().includes('deepseek')) {
    m = m.replace(/deepseek/i, 'DeepSeek');
  } else if (m.toLowerCase().includes('muse')) {
    m = m.replace(/muse[-\s]?spark/i, 'Muse Spark');
  }
  return m;
}

function formatAgentName(rawAgent, isSubAgent) {
  if (rawAgent && rawAgent !== 'Main' && rawAgent !== 'SubAgent') {
    if (rawAgent.toLowerCase() === 'build') return 'Build';
    if (rawAgent.toLowerCase() === 'plan') return 'Plan';
    return rawAgent;
  }
  return isSubAgent ? 'General Task' : 'Build';
}

function isQuestionOrPermissionEvent(event) {
  if (!event) return false;
  try {
    const type = (event.type || event.event || event.name || '').toLowerCase();
    
    // Explicit question or permission event types ONLY
    if (
      type === 'question.ask' || type === 'question.asked' || type === 'question.created' ||
      type === 'permission.ask' || type === 'permission.asked' || type === 'permission.request' ||
      type === 'permission.created'
    ) {
      return true;
    }

    const props = event.properties || {};
    if (props.question?.options || props.questions || props.info?.question?.options) {
      return true;
    }
  } catch(e) {}
  return false;
}

// ====================================================================
// SECTION 1: OpenCode Plugin Client Engine
// ====================================================================
function setupPlugin(ctx) {
  const sessions = new Map();
const knownParents = new Map();
  const activeToolCalls = new Map();
  const pendingInteractions = new Map();
  let hiddenAgents = new Set(['compaction', 'title']);
  let hiddenAgentsLastRefresh = 0;
  let rootSessionId = null;
  let activeTopLevelSessionId = null;
  let heartbeatTimer = null;
  let hiddenRefreshTimer = null;
  let disposed = false;

  function isHiddenAgent(name) {
    if (typeof name !== 'string' || !name) return false;
    return hiddenAgents.has(name.trim().toLowerCase());
  }

  async function refreshHiddenAgents(force = false) {
    const now = Date.now();
    if (!force && now - hiddenAgentsLastRefresh < 5 * 60 * 1000) return;
    hiddenAgentsLastRefresh = now;
    try {
      const client = ctx?.client;
      let res = null;
      if (client?.app?.agents) res = await client.app.agents();
      else if (client?.app?.listAgents) res = await client.app.listAgents();
      else if (typeof client?.request === 'function') res = await client.request({ url: '/agent', method: 'GET' });
      const list = res?.data ?? res ?? [];
      if (Array.isArray(list) && list.length) {
        const next = new Set();
        for (const a of list) if (a && typeof a.name === 'string' && a.hidden) next.add(a.name.toLowerCase());
        if (next.size) hiddenAgents = next;
      }
    } catch {}
  }

  function completedMessageKey(info) {
    if (info && typeof info.id === 'string' && info.id) return info.id;
    return null;
  }

  // ---- Dashboard server auto-management: start if missing, lease while alive ----
  let leaseSocket = null;
  let serverEnsureInFlight = false;

  function connectLease() {
    return new Promise((resolve, reject) => {
      const sock = net.createConnection({ host: '127.0.0.1', port: LEASE_PORT });
      sock.once('connect', () => resolve(sock));
      sock.once('error', (e) => { sock.destroy(); reject(e); });
    });
  }

  // Returns an executable that can run this .mjs file as a script.
  // In opencode the plugin runs inside the Bun runtime, where process.execPath
  // points at opencode.exe/bun.exe - NOT a script runner for our imports.
  function getServerRuntime() {
    const exe = (process.execPath || '').toLowerCase();
    const base = path.basename(exe);
    if (base.includes('node')) return process.execPath;
    if (base.includes('bun')) return process.execPath;
    return 'node'; // opencode.exe etc -> resolve node from PATH
  }

  function spawnServer() {
    try {
      const child = spawn(getServerRuntime(), [fileURLToPath(import.meta.url)], {
        detached: true,
        stdio: 'ignore',
        windowsHide: true
      });
      child.on('error', (e) => { console.log(`[agent-dashboard] server spawn failed: ${(e && e.message) || e}`); });
      child.unref();
      pluginLog('SPAWN Dashboard server process started with ' + getServerRuntime());
    } catch (e) {
      console.log(`[agent-dashboard] server spawn failed: ${(e && e.message) || e}`);
      pluginLog('SPAWN-FAIL ' + (e && e.message));
    }
  }

  async function ensureServer() {
    if (disposed) return;
    if (serverEnsureInFlight) return;
    serverEnsureInFlight = true;
    try {
      if (leaseSocket && !leaseSocket.destroyed) return;

      // 1. Try to lease an already-running server
      let sock = await connectLease().catch(() => null);
      if (disposed) {
        if (sock && !sock.destroyed) sock.destroy();
        return;
      }
      if (sock) {
        leaseSocket = sock;
        attachLeaseHandlers();
        // Server was already up (or just restarted) -> push all known sessions immediately
        sendAllReports(true).catch(() => {});
        return;
      }

      // 2. HTTP port already serving (e.g. manually started old server) -> do not spawn a second
      try {
        const up = await fetch(`http://127.0.0.1:${DASHBOARD_PORT}/`, { method: 'GET', signal: AbortSignal.timeout(500) });
        if (up.ok) return;
      } catch (e) {}

      // 3. No server at all -> spawn it, then poll for the lease port (up to 5s)
      spawnServer();
      let polled = null;
      for (let i = 0; i < 50 && !polled; i++) {
        await new Promise(r => setTimeout(r, 100));
        polled = await connectLease().catch(() => null);
      }
      if (disposed) {
        if (polled && !polled.destroyed) polled.destroy();
        return;
      }
      if (polled) {
        leaseSocket = polled;
        attachLeaseHandlers();
        // Freshly spawned server -> push all known sessions immediately
        sendAllReports(true).catch(() => {});
      }
    } finally {
      serverEnsureInFlight = false;
    }
  }

  function attachLeaseHandlers() {
    const sock = leaseSocket;
    if (!sock) return;
    sock.on('error', () => { try { sock.destroy(); } catch (e) {} });
    sock.on('close', () => {
      if (leaseSocket === sock) leaseSocket = null;
      if (disposed) return;
      // Self-heal: server died while this terminal is still alive -> respawn
      setTimeout(() => ensureServer().catch(() => {}), 2000);
    });
  }

  async function sendReportForSession(s, now, force = false) {
    if (!s || !s.sessionId) return;

    const lastTime = globalSessionThrottles.get(s.sessionId) || 0;
    const lastState = globalSessionLastState.get(s.sessionId) || {};
    let reportStatus = s.status;
    if (hasPendingInteraction(s.sessionId)) {
      reportStatus = s.parentId ? 'asking_parent' : 'user_response';
    } else if (s.compacting) {
      reportStatus = 'compacting';
    } else if (hasActiveToolCalls(s.sessionId)) {
      reportStatus = 'running';
    }

    const statusChanged = reportStatus !== lastState.status;
    const titleChanged = s.title !== lastState.title;
    const tokensChanged = tokenFingerprint(s.tokens) !== lastState.tokens;
    const timeElapsed = now - lastTime;

    // RULE 1: Module-level hard rate limit Ã¢â‚¬â€ Never send more than 1 report per 1000ms for the same session across all instances
    if (!force && !statusChanged && !tokensChanged && timeElapsed < 1000) {
      return;
    }

    // RULE 2: Heartbeat interval Ã¢â‚¬â€ If < 5 seconds elapsed, only send if status or title actually changed
    if (!force && !statusChanged && !titleChanged && !tokensChanged && timeElapsed < 5000) {
      return;
    }

    globalSessionThrottles.set(s.sessionId, now);
globalSessionLastState.set(s.sessionId, { status: reportStatus, title: s.title, tokens: tokenFingerprint(s.tokens) });

    try {
      const headers = { 'Content-Type': 'application/json' };
      if (process.env.DASHBOARD_TOKEN) headers['Authorization'] = 'Bearer ' + process.env.DASHBOARD_TOKEN;
      await fetch(HEARTBEAT_URL, {
        method: 'POST',
        headers: headers,
        body: JSON.stringify({
          sessionId: s.sessionId,
          parentId: s.parentId,
remove: s.remove === true,
          status: reportStatus,
          alarmEligible: s.alarmEligible === true,
          title: s.title,
          agent: s.agent,
          model: s.model,
          cost: s.cost,
          tokens: s.tokens,
          error: s.error,
          retryInfo: s.retryInfo,
          msgCount: s.msgCount,
          compactionCount: s.compactionCount,
          todos: s.todos,
          observedUsage: true,
          timestamp: now
        })
      });
    } catch (e) {}
  }

  async function closeSessionLocally(id, now) {
    const old = sessions.get(id);
    if (!old) return;
    old.status = 'closed';
    old.remove = true;
    old.waitingForUser = false;
    old.lastActivityTime = now;
    await sendReportForSession(old, now, true);
    knownParents.delete(id);
    pendingInteractions.delete(id);
    sessions.delete(id);
  }

  async function sendAllReports(force = false) {
    const now = Date.now();
    for (const [id, s] of sessions.entries()) {
      const inactiveMs = now - s.lastActivityTime;

      // Every known top-level session heartbeats so multiple open sessions
      // stay visible. Quiet ones decay to idle but keep heartbeating while
      // open â€” close events remove them; deleting here dropped open tabs.
      if (!s.parentId && inactiveMs > RUNNING_DECAY_MS && !hasActiveToolCalls(id) && !hasPendingInteraction(id) && s.status !== 'user_response' && s.status !== 'waiting') {
        s.status = 'waiting';
      }

// Long-running shell/tool calls can be silent for minutes; only decay quiet sub-agents.
      if (!hasActiveToolCalls(id) && s.parentId && s.status === 'running' && inactiveMs > RUNNING_DECAY_MS) {
        s.status = s.waitingForUser ? 'user_response' : 'waiting';
      }

      // Quiet sub-agents should fade out of reporting instead of bouncing CLOSED -> RUNNING.
      if (s.parentId && !s.waitingForUser && s.status !== 'asking_parent' && inactiveMs > STALE_SUBAGENT_PRUNE_MS) {
        sessions.delete(id);
        continue;
      }

      // Quiet top-level sessions must not stick on running: without recent
      // events and no live tool calls they are idle (V2 often misses the transition).
      if (!s.parentId && s.status === 'running' && !hasActiveToolCalls(id) && inactiveMs > RUNNING_DECAY_MS) {
        s.status = 'waiting';
      }

      await sendReportForSession(s, now, force);

      // Delete closed session from plugin map so heartbeats stop
      if (s.status === 'closed') {
        sessions.delete(id);
      }
    }
  }

  const eventHandler = async (arg1, arg2) => {
    let event = arg1 && arg1.event ? arg1.event : arg1;
    let session = arg1 && arg1.session ? arg1.session : arg2;

    // V2 sync envelope: { type: "sync", name: "session.updated.1", data: {...} }.
    // Unwrap to the classic { type, properties } shape the finders expect.
    if (event && event.type === 'sync' && event.data && typeof event.data === 'object') {
      const rawName = typeof event.name === 'string' ? event.name : '';
      const baseName = rawName.replace(/\.\d+$/, '');
      if (baseName) event = { type: baseName, properties: event.data };
    }

    let foundId = findSessionId(event, session, ctx);
    
    // Fallback to rootSessionId if event doesn't carry explicit session ID (e.g. question/permission events).
    // If sub-agents are active, anonymous prompts belong to the parent/sub-agent handoff and should not alarm the user.
    if (!foundId && rootSessionId) {
      if (isQuestionOrPermissionEvent(event)) {
        const activeSubAgent = findActiveSubAgent(rootSessionId, sessions);
        if (activeSubAgent) {
          const now = Date.now();
          activeSubAgent.status = 'asking_parent';
          activeSubAgent.waitingForUser = false;
          activeSubAgent.alarmEligible = false;
          activeSubAgent.lastActivityTime = now;
          await sendReportForSession(activeSubAgent, now, true);
          return;
        }
      }
      foundId = rootSessionId;
    }
    if (!foundId) return;

    const rawTitle = findRawSessionTitle(event, session);
    const foundTitle = cleanTitle(rawTitle);
    const foundAgent = findAgentName(event, session);
    const foundModel = findModelName(event, session);
    const type = (event?.type || event?.event || event?.name || '').toLowerCase();
    const isFork = isForkTitle(foundTitle) || isForkTitle(rawTitle);

    let explicitParentId = findParentId(event, session);
    // Forks must never be nested - clear any stale parent and ignore explicit parent
    if (isFork && explicitParentId) {
      knownParents.delete(foundId);
      explicitParentId = null;
    }
    if (explicitParentId) {
      knownParents.set(foundId, explicitParentId);
    } else if (isFork) {
      knownParents.delete(foundId);
    }

    if (!rootSessionId) {
      if (!explicitParentId) {
        rootSessionId = foundId;
      }
    }

    let effectiveParentId = explicitParentId || knownParents.get(foundId) || null;
    if (isFork) {
      effectiveParentId = null;
      knownParents.delete(foundId);
    } else if (effectiveParentId === foundId) {
      knownParents.delete(foundId);
      effectiveParentId = null;
    }

    const isSubAgent = !!effectiveParentId && !isFork;
    const rawStatus = event?.properties?.status || event?.properties?.info?.status || session?.status || '';
    const coreStatus = (typeof rawStatus === 'string' ? rawStatus : (rawStatus && typeof rawStatus.type === 'string' ? rawStatus.type : '')).toLowerCase();

    const now = Date.now();
    let s = sessions.get(foundId);

    const hiddenAgent = isHiddenAgent(foundAgent);
    const isHiddenCompaction = hiddenAgent && foundAgent && foundAgent.trim().toLowerCase() === 'compaction';

    const isAskEvent = type.endsWith('.asked') && (type.includes('question') || type.includes('permission'));
    const isReplyEvent = (type.endsWith('.replied') || type.endsWith('.rejected')) && (type.includes('question') || type.includes('permission'));
    const isUserPrompt = isAskEvent || isQuestionOrPermissionEvent(event);
    const shouldTriggerUserAlarm = isUserPrompt && !isSubAgent && !(s && s.waitingForUser);
    const isInterrupt = type.includes('interrupt') || type.includes('cancel') || type.includes('abort') || coreStatus === 'interrupted' || coreStatus === 'canceled' || coreStatus === 'aborted';

    // Track hidden-agent activity: compaction should be status, not identity
    if (isHiddenCompaction) {
      if (s) s.compacting = true;
      else {
        const placeholder = sessions.get(foundId);
        if (placeholder) placeholder.compacting = true;
      }
    } else if (foundAgent && !hiddenAgent && s && s.compacting) {
      // Visible agent message while compacting flag set -> compaction finished
      // Keep flag until idle/busy confirms transition; do not clear on every part.delta
      if (type === 'message.updated' && event?.properties?.info?.role === 'assistant') {
        // Will be cleared on idle; keep running until then
      }
    }

    // State machine: track pending user interactions separately from tool lifetime.
    // A tool can be alive (tool.execute.before seen, after not yet) while blocked on question/permission.
    if (isAskEvent) {
      const reqId = event?.properties?.id || event?.properties?.requestID || event?.id || `${foundId}:pending`;
      addPendingInteraction(foundId, reqId);
    } else if (isReplyEvent) {
      const reqId = event?.properties?.requestID || event?.properties?.requestId || event?.properties?.id || event?.id;
      if (reqId) {
        if (!removePendingByRequestId(reqId)) removePendingInteraction(foundId, reqId);
      } else {
        removePendingInteraction(foundId);
      }
    }

    // DIRECT OPENCODE CORE STATE MAPPING
    let status = s ? s.status : 'waiting';

    if (type === 'session.deleted' || type === 'session.closed' || type.includes('delete') || type.includes('close') || type.includes('end')) {
      status = 'closed';
      if (s) s.waitingForUser = false;
      pendingInteractions.delete(foundId);
    } else if (isInterrupt && !isFork) {
      status = 'interrupted';
      if (s) s.waitingForUser = false;
      pendingInteractions.delete(foundId);
    } else if (coreStatus === 'retry' || type.includes('retry')) {
      status = 'retrying';
      if (s) s.waitingForUser = false;
    } else if (isUserPrompt) {
      status = isSubAgent ? 'asking_parent' : 'user_response';
      if (s) s.waitingForUser = !isSubAgent;
    } else if (isReplyEvent) {
      if (hasPendingInteraction(foundId)) {
        status = isSubAgent ? 'asking_parent' : 'user_response';
        if (s) s.waitingForUser = !isSubAgent;
      } else if (hasActiveToolCalls(foundId) || coreStatus === 'busy' || type.includes('busy') || type.includes('tool') || type.includes('execut') || type.includes('running') || type.includes('delta')) {
        status = s && s.compacting ? 'compacting' : 'running';
        if (s) s.waitingForUser = false;
        if (s) s.error = null;
      } else {
        status = s && (s.status === 'interrupted' || isInterruptedError(s.error)) && !isFork ? 'interrupted' : 'waiting';
        if (s) s.waitingForUser = false;
      }
    } else if (s && s.compacting && (coreStatus === 'busy' || type.includes('busy') || type.includes('tool') || type.includes('execut') || type.includes('running') || type.includes('delta'))) {
      status = 'compacting';
      if (s) s.waitingForUser = false;
      if (s) s.error = null;
    } else if (coreStatus === 'busy' || type.includes('busy') || type.includes('tool') || type.includes('execut') || type.includes('running') || type.includes('delta')) {
      status = s && s.compacting ? 'compacting' : 'running';
      if (s) s.waitingForUser = false;
      if (s) s.error = null;
    } else if (type === 'session.prompt' || type === 'session.run' || type === 'session.background') {
      // Turn start: latch running until the turn goes quiet (session.idle + quiet period).
      status = s && s.compacting ? 'compacting' : 'running';
      if (s) s.waitingForUser = false;
      if (s) s.error = null;
    } else if (coreStatus === 'idle' || type === 'session.idle' || type === 'idle') {
      // Turn end wins only after quiet: recent tool/prompt/delta activity
      // means the turn is still alive (short tools look idle between calls).
      const recentActivity = s && (now - s.lastActivityTime) < TURN_QUIET_MS;
      if ((!isFork && s && (s.status === 'interrupted' || isInterruptedError(s.error)))) {
        status = 'interrupted';
        if (s) s.waitingForUser = false;
      } else if (hasActiveToolCalls(foundId) || recentActivity) {
        status = s && s.compacting ? 'compacting' : 'running';
        if (s) s.waitingForUser = false;
      } else {
        status = 'waiting';
        if (s) { s.waitingForUser = false; s.compacting = false; }
      }
    } else if (type.includes('error') || type.includes('fail') || type.includes('exception')) {
      status = 'failed';
      if (s) { s.waitingForUser = false; s.compacting = false; }
    } else if (s && s.waitingForUser) {
      status = 'user_response';
    }
    // Derive waiting state from pending set to avoid drift
    if (hasPendingInteraction(foundId) && status !== 'closed' && status !== 'interrupted' && status !== 'failed' && status !== 'retrying') {
      status = isSubAgent ? 'asking_parent' : 'user_response';
      if (s) s.waitingForUser = !isSubAgent;
    }
    // Hidden compaction is status, not identity
    if (s && s.compacting && status !== 'closed' && status !== 'interrupted' && status !== 'failed' && status !== 'user_response' && status !== 'asking_parent' && status !== 'retrying') {
      if (status === 'running' || status === 'waiting' || type.includes('delta') || type.includes('compaction') || coreStatus === 'busy') {
        status = 'compacting';
      } else if (type === 'message.updated' && !hiddenAgent && foundAgent) {
        s.compacting = false;
      }
    }
    if (status === 'compacting' && s) s.waitingForUser = false;

    const isSessionCreate = type.startsWith('session.created') || type.startsWith('session.create');

    if (!isSubAgent && status !== 'closed') {
      activeTopLevelSessionId = foundId;
      rootSessionId = foundId;
    }

    const hiddenForIdentity = isHiddenAgent(foundAgent);
    if (!s) {
      s = {
        sessionId: foundId,
        parentId: effectiveParentId,
        title: foundTitle || (effectiveParentId ? 'Sub-Agent Task' : 'Active Terminal'),
        agent: hiddenForIdentity ? (isSubAgent ? 'General Task' : 'Build') : formatAgentName(foundAgent, isSubAgent),
        model: hiddenForIdentity ? 'Claude Haiku 4.5' : formatModelName(foundModel),
        status: status,
        waitingForUser: hasPendingInteraction(foundId) ? !isSubAgent : (isUserPrompt && !isSubAgent),
        compacting: isHiddenCompaction,
        alarmEligible: status === 'user_response' && shouldTriggerUserAlarm,
        baseCost: isSessionCreate ? 0 : undefined,
        rawCost: undefined,
        completedMessageIDs: new Set(),
        lastActivityTime: now
      };
      sessions.set(foundId, s);
    } else {
      s.parentId = effectiveParentId;
      if (foundTitle && foundTitle !== 'Active Terminal' && foundTitle !== 'Sub-Agent Task') {
        s.title = foundTitle;
      }
      if (foundAgent && !hiddenForIdentity) s.agent = formatAgentName(foundAgent, isSubAgent);
      if (foundModel && !hiddenForIdentity) s.model = formatModelName(foundModel);

      s.lastActivityTime = now;
      s.status = status;
      s.alarmEligible = status === 'user_response' ? shouldTriggerUserAlarm : false;
    }

    // ================== Extended telemetry capture ==================
    const props = event?.properties || {};
    const info = props.info || {};
    const part = props.part || {};

    // 1. Cost: show usage observed in this dashboard session, not persisted totals.
    if (typeof info.cost === 'number') {
      s.rawCost = typeof s.rawCost === 'number' ? Math.max(s.rawCost, info.cost) : info.cost;
      if (typeof s.baseCost !== 'number') s.baseCost = isSessionCreate ? 0 : s.rawCost;
      s.cost = Math.max(0, s.rawCost - s.baseCost);
    }
    if (
      type === 'message.updated' &&
      info &&
      info.role === 'assistant' &&
      info.tokens &&
      typeof info.tokens === 'object' &&
      info.time &&
      typeof info.time.completed === 'number'
    ) {
      const messageKey = completedMessageKey(info);
      if (messageKey && !s.completedMessageIDs.has(messageKey)) {
        s.completedMessageIDs.add(messageKey);
        s.tokens = addTokens(s.tokens, info.tokens);
        // Turn end is decided by session.idle + quiet period (and decay
        // backstops), not by a single completed reply mid-turn.
      }
    }

    // 2. Error: from session.error / message error
    const err = props.error || info.error || {};
    if (err && typeof err === 'object' && (err.message || err.name || (err.data && err.data.message))) {
      s.error = (err.data && err.data.message) || err.message || err.name;
    }

    // 3. Retry info: from session.status (type=retry) or RetryPart
    const st = props.status || props.info?.status || {};
    if (st && st.type === 'retry') {
      s.retryInfo = { attempt: st.attempt, next: st.next, message: st.message };
    } else if (part.type === 'retry' && part.error) {
      s.retryInfo = { attempt: part.attempt, message: (part.error && part.error.message) || '' };
    }

    // 4. Message count: new messages only
    if (type === 'message.updated') {
      s.msgCount = (s.msgCount || 0) + 1;
      // Any message means someone actually used the session. This is what the
      // 72 hour broom-closet rule measures against - lastHeartbeat would be
      // useless, because a session that is merely open in a tab keeps beating
      // forever without anyone touching it.
      s.lastActivityAt = now;
    }

    // 5. Compaction count: compaction parts / events
    if (part.type === 'compaction' || type.includes('compaction')) s.compactionCount = (s.compactionCount || 0) + 1;

    // 6. Todos: todo.updated events carry the full array
    if (type === 'todo.updated' && Array.isArray(props.todos)) s.todos = props.todos;

    // Send report immediately if status or title changed
    await sendReportForSession(s, now);

    if (status === 'closed') {
      knownParents.delete(foundId);
      pendingInteractions.delete(foundId);
      sessions.delete(foundId);
      if (activeTopLevelSessionId === foundId) activeTopLevelSessionId = null;
      return;
    }

    if (!heartbeatTimer) {
      heartbeatTimer = setInterval(() => sendAllReports(), 2500);
    }
  };

  function hasActiveToolCalls(sessionId) {
    const calls = activeToolCalls.get(sessionId);
    if (!calls || calls.size === 0) return false;
    // Bound leak: before/after with mismatched IDs (V2 guesses) must not pin
    // a session green forever. Calls older than the stale horizon are dead.
    const now = Date.now();
    for (const [callId, startedAt] of calls.entries()) {
      if (now - startedAt > TOOL_CALL_STALE_MS) calls.delete(callId);
    }
    if (calls.size === 0) activeToolCalls.delete(sessionId);
    return calls.size > 0;
  }

  function getPendingSet(sessionId) {
    let set = pendingInteractions.get(sessionId);
    if (!set) { set = new Set(); pendingInteractions.set(sessionId, set); }
    return set;
  }
  function hasPendingInteraction(sessionId) {
    return pendingInteractions.get(sessionId)?.size > 0;
  }
  function addPendingInteraction(sessionId, requestId) {
    if (!isSessionId(sessionId) || !requestId) return;
    getPendingSet(sessionId).add(requestId);
  }
  function removePendingInteraction(sessionId, requestId) {
    const set = pendingInteractions.get(sessionId);
    if (!set) return;
    if (requestId) set.delete(requestId);
    else set.clear();
    if (set.size === 0) pendingInteractions.delete(sessionId);
  }
  function removePendingByRequestId(requestId) {
    if (!requestId || typeof requestId !== 'string') return false;
    for (const [sid, set] of pendingInteractions.entries()) {
      if (set.has(requestId)) {
        set.delete(requestId);
        if (set.size === 0) pendingInteractions.delete(sid);
        return true;
      }
    }
    return false;
  }

  function ensureToolSession(sessionId, now) {
    let s = sessions.get(sessionId);

    if (!s) {
      s = {
        sessionId: sessionId,
        parentId: null,
        title: 'Active Terminal',
        agent: 'Build',
        model: 'Claude Haiku 4.5',
        status: 'waiting',
        waitingForUser: false,
        lastActivityTime: now
      };
      sessions.set(sessionId, s);
    }

    s.waitingForUser = false;
    s.error = null;
    s.lastActivityTime = now;

    if (!s.parentId) rootSessionId = sessionId;
    if (!heartbeatTimer) heartbeatTimer = setInterval(() => sendAllReports(), 2500);

    return s;
  }

  async function markToolSessionStarted(input) {
    if (!isSessionId(input?.sessionID)) return;

    const now = Date.now();
    const callId = typeof input.callID === 'string' && input.callID ? input.callID : '__unknown__';
    const calls = activeToolCalls.get(input.sessionID) || new Map();
    calls.set(callId, now);
    activeToolCalls.set(input.sessionID, calls);

    const s = ensureToolSession(input.sessionID, now);
    await sendReportForSession(s, now, true);
  }

  async function markToolSessionFinished(input) {
    if (!isSessionId(input?.sessionID)) return;

    const now = Date.now();
    const calls = activeToolCalls.get(input.sessionID);
    if (calls) {
      const finishedId = typeof input.callID === 'string' && input.callID ? input.callID : null;
      if (finishedId && calls.has(finishedId)) {
        calls.delete(finishedId);
        if (calls.size === 0) activeToolCalls.delete(input.sessionID);
      } else if (!finishedId) {
        // Completion without ID can't be matched â€” clear instead of leaking green.
        activeToolCalls.delete(input.sessionID);
      }
    }

    const s = ensureToolSession(input.sessionID, now);
    // A finished tool call with no remaining live work ends the running
    // state instead of sticking on green until the 10min decay.
    if (s.status === 'running' && !hasActiveToolCalls(input.sessionID) && !hasPendingInteraction(input.sessionID)) {
      s.status = 'waiting';
    }
    await sendReportForSession(s, now, true);
  }

  // V2 publishes authoritative per-session usage (session.usage.updated) instead
  // of V1's per-message usage on message.updated. Totals are cumulative, so they
  // replace the local accumulator rather than adding to it.
  async function applyAuthoritativeUsage(input) {
    if (!isSessionId(input?.sessionID)) return;
    const now = Date.now();
    const s = ensureToolSession(input.sessionID, now);
    if (typeof input.cost === 'number' && isFinite(input.cost)) {
      s.cost = input.cost;
      s.rawCost = input.cost;
    }
    const tokens = normalizeTokens(input.tokens);
    if (tokens) s.tokens = tokens;
    await sendReportForSession(s, now, true);
  }

  try {
    if (ctx?.events?.on) {
      ctx.events.on('event', (event, session) => eventHandler(event, session));
    } else if (ctx?.client?.on) {
      ctx.client.on('event', (arg) => eventHandler(arg));
    }
  } catch (e) {}

  refreshHiddenAgents(true).catch(() => {});
  hiddenRefreshTimer = setInterval(() => refreshHiddenAgents().catch(() => {}), 5 * 60 * 1000);

  ensureServer().catch(() => {});

  // Watchdog: the lease-close handler covers a server that dies while we hold a
  // socket, but not a server that was already gone when this instance loaded, or
  // a spawn that silently failed. Cheap no-op while the lease is healthy.
  const watchdogTimer = setInterval(() => { ensureServer().catch(() => {}); }, 10000);

  return {
    event: eventHandler,
    usage: applyAuthoritativeUsage,
    tool: {
      start: markToolSessionStarted,
      finish: markToolSessionFinished
    },
    "tool.execute.before": async (input) => {
      await markToolSessionStarted(input);
    },
    "tool.execute.after": async (input) => {
      await markToolSessionFinished(input);
    },
    cleanup: () => {
      disposed = true;
      if (heartbeatTimer) clearInterval(heartbeatTimer);
      if (hiddenRefreshTimer) clearInterval(hiddenRefreshTimer);
      if (watchdogTimer) clearInterval(watchdogTimer);
      if (leaseSocket && !leaseSocket.destroyed) leaseSocket.destroy();
      pendingInteractions.clear();
      activeToolCalls.clear();
    }
  };
}

async function DashboardReporterPluginV1(ctx) {
  return setupPlugin(ctx);
}

// V2 setup: register the same reporter via V2 hook + event APIs.
// V1 calls server() and uses the returned hooks object.
// V2 reads default export id + setup() and ignores server().
async function DashboardReporterSetupV2(ctx) {
  const hooks = setupPlugin(ctx);
  const toToolInput = (e) => ({
    sessionID:
      e?.sessionID ?? e?.sessionId ?? e?.session_id ??
      e?.properties?.sessionID ?? e?.properties?.sessionId ??
      e?.input?.sessionID ?? undefined,
    callID:
      e?.callID ?? e?.callId ?? e?.id ?? e?.toolCallID ??
      e?.input?.callID ?? undefined,
  });
  try {
    await ctx?.tool?.hook?.("execute.before", (e) => hooks["tool.execute.before"](toToolInput(e)));
  } catch {}
  try {
    await ctx?.tool?.hook?.("execute.after", (e) => hooks["tool.execute.after"](toToolInput(e)));
  } catch {}
  try {
    if (ctx?.event?.subscribe) {
      const controller = new AbortController();
      void (async () => {
        try {
          for await (const event of ctx.event.subscribe({ signal: controller.signal })) {
            try {
              await routeV2Event(hooks, event);
            } catch {}
          }
        } catch {}
      })();
      const prevCleanup = hooks.cleanup;
      return () => {
        try { controller.abort(); } catch {}
        try { prevCleanup?.(); } catch {}
      };
    }
  } catch {}
  return () => {
    try { hooks.cleanup?.(); } catch {}
  };
}

// V2 public event stream -> the state machine the reporter already speaks.
// Shapes verified against /api/event on 2.0.6 (all events carry data.sessionID):
//   session.step.started       { agent, model:{id,providerID,variant}, assistantMessageID }
//   session.step.ended         { finish, cost, tokens:{input,output,reasoning,cache{read,write}} }
//   session.usage.updated      { cost, tokens }  (cumulative per session)
//   session.tool.input.started { id, name }  |  session.tool.success / .error { id }
async function routeV2Event(hooks, event) {
  const type = typeof event?.type === 'string' ? event.type : '';
  const data = event?.data && typeof event.data === 'object' ? event.data : {};
  const sessionID = data.sessionID;
  const callID = typeof data.id === 'string' ? data.id : undefined;

  switch (type) {
    case 'session.usage.updated':
      await hooks.usage?.({ sessionID, cost: data.cost, tokens: data.tokens });
      return;
    case 'session.tool.input.started':
      await hooks.tool?.start?.({ sessionID, callID });
      return;
    case 'session.tool.success':
    case 'session.tool.error':
      await hooks.tool?.finish?.({ sessionID, callID });
      return;
    case 'session.step.started':
      // Turn start: carries the agent and model for this step.
      await hooks.event({
        type: 'session.prompt',
        properties: { sessionID, agent: data.agent, model: data.model }
      });
      return;
    case 'session.step.ended':
      // Step end is not turn end (tool loops continue), but it does end the
      // quiet window the idle branch uses to decide running vs waiting.
      await hooks.event({
        type: 'session.idle',
        properties: { sessionID, status: 'idle' }
      });
      return;
    default:
      await hooks.event(event);
  }
}

export default {
  id: "agent-dashboard-reporter",
  server: DashboardReporterPluginV1,
  setup: DashboardReporterSetupV2,
};

// ====================================================================
// SECTION 2: Web Server & Real-Time Telemetry Engine
// ====================================================================
const activeSessions = new Map();
const serverLastLogs = new Map();
const subAgentMetricSnapshots = new Map();
const sessionTokenFileCache = new Map();
const DEBUG_SESSION_ROOT = path.join(os.homedir(), '.config', 'opencode', 'debug');

function subAgentMetricKey(parentId, sessionId) {
  return parentId + '\0' + sessionId;
}

function rememberSubAgentMetrics(parentId, sessionId, data) {
  if (!isSessionId(parentId) || !isSessionId(sessionId)) return;

  const key = subAgentMetricKey(parentId, sessionId);
  const current = subAgentMetricSnapshots.get(key) || { parentId, sessionId };
  subAgentMetricSnapshots.set(key, {
    parentId,
    sessionId,
    cost: (typeof data.cost === 'number' && isFinite(data.cost))
      ? Math.max(typeof current.cost === 'number' ? current.cost : 0, data.cost)
      : current.cost,
    tokens: data.tokens && typeof data.tokens === 'object'
      ? preferSessionTokens(current.tokens, data.tokens)
      : current.tokens,
    msgCount: (typeof data.msgCount === 'number')
      ? Math.max(current.msgCount || 0, data.msgCount)
      : (current.msgCount || 0)
  });
}

function forgetSubAgentMetricsForParent(parentId) {
  for (const [key, snapshot] of subAgentMetricSnapshots.entries()) {
    if (snapshot.parentId === parentId) subAgentMetricSnapshots.delete(key);
  }
}

function getSubAgentMetricTotals(parentId) {
  let costValue = 0;
  let tokensValue;
  let msgCount = 0;

  for (const snapshot of subAgentMetricSnapshots.values()) {
    if (snapshot.parentId !== parentId) continue;
    if (typeof snapshot.cost === 'number' && isFinite(snapshot.cost)) costValue += snapshot.cost;
    tokensValue = addTokens(tokensValue, snapshot.tokens);
    msgCount += snapshot.msgCount || 0;
  }

  return { costValue, tokensValue, msgCount };
}

function findDebugSessionDir(sessionId) {
  if (!isSessionId(sessionId)) return null;
  try {
    const entries = fs.readdirSync(DEBUG_SESSION_ROOT, { withFileTypes: true });
    const match = entries.find((entry) => entry.isDirectory() && entry.name.startsWith(sessionId + '('));
    return match ? path.join(DEBUG_SESSION_ROOT, match.name) : null;
  } catch {
    return null;
  }
}

function latestSessionJsonFile(sessionDir) {
  try {
    const files = fs.readdirSync(sessionDir)
      .map((name) => (/^(\d+)\.json$/.exec(name) ? { name, order: Number(/^(\d+)\.json$/.exec(name)[1]) } : null))
      .filter(Boolean)
      .sort((a, b) => b.order - a.order);
    return files.length ? path.join(sessionDir, files[0].name) : null;
  } catch {
    return null;
  }
}

function readPersistedSessionTokens(sessionId) {
  const sessionDir = findDebugSessionDir(sessionId);
  if (!sessionDir) return undefined;
  const jsonFile = latestSessionJsonFile(sessionDir);
  if (!jsonFile) return undefined;

  try {
    const stat = fs.statSync(jsonFile);
    const cacheKey = jsonFile;
    const cached = sessionTokenFileCache.get(cacheKey);
    if (cached && cached.mtimeMs === stat.mtimeMs && cached.size === stat.size) return cached.tokens;

    const raw = fs.readFileSync(jsonFile, 'utf8');
    const data = JSON.parse(raw);
    const totals = Array.isArray(data)
      ? data.reduce((sum, message) => {
          const info = message && typeof message === 'object' ? message.info : null;
          if (!info || info.role !== 'assistant' || !info.tokens || !info.time || typeof info.time.completed !== 'number') return sum;
          return addTokens(sum, info.tokens);
        }, undefined)
      : undefined;

    sessionTokenFileCache.set(cacheKey, { mtimeMs: stat.mtimeMs, size: stat.size, tokens: totals });
    return totals;
  } catch {
    return undefined;
  }
}

function log(tag, message) {
  const time = new Date().toLocaleTimeString();
  console.log(`[${time}] [${tag}] ${message}`);
}

function startServer() {
  log('INIT', `Starting Web Server on port ${DASHBOARD_PORT}...`);
  pluginLog(`agent-dashboard v${PLUGIN_VERSION} starting`);

  // ---- Write-protection: heartbeats require a bearer token (read endpoints stay open).
  //      If DASHBOARD_TOKEN is unset, the server stays open (backwards compatible).
  const TOKEN = process.env.DASHBOARD_TOKEN || null;
  function tokenMatches(req) {
    if (!TOKEN) return true;
    const auth = req.headers['authorization'] || '';
    const provided = auth.startsWith('Bearer ') ? auth.slice(7) : '';
    const a = crypto.createHash('sha256').update(provided).digest();
    const b = crypto.createHash('sha256').update(TOKEN).digest();
    return crypto.timingSafeEqual(a, b);
  }

  // ---- Lease tracking: each opencode terminal holds one TCP lease. When the last
  //      lease drops, the dashboard server shuts itself down (no terminals = no dashboard).
  const leaseSockets = new Set();
  let shutdownTimer = null;
  const SHUTDOWN_GRACE_MS = 30000;

  const leaseServer = net.createServer((socket) => {
    leaseSockets.add(socket);
    socket.on('close', () => {
      leaseSockets.delete(socket);
      if (leaseSockets.size === 0) {
        if (!shutdownTimer) {
          shutdownTimer = setTimeout(() => {
            if (leaseSockets.size === 0) {
              log('SHUTDOWN', `No active terminals for ${SHUTDOWN_GRACE_MS / 1000}s, shutting down dashboard server.`);
              process.exit(0);
            }
          }, SHUTDOWN_GRACE_MS);
        }
      } else if (shutdownTimer) {
        clearTimeout(shutdownTimer);
        shutdownTimer = null;
      }
    });
  });

  leaseServer.on('error', (e) => {
    // A second instance lost the race for the lease port: the running server
    // owns it, so this one has nothing to do.
    if (e && e.code === 'EADDRINUSE') {
      log('LEASE-BUSY', 'Another dashboard server owns the lease port; exiting.');
      process.exit(0);
    }
    log('LEASE-ERR', String((e && e.message) || e));
    process.exit(1);
  });

  leaseServer.listen(LEASE_PORT, '127.0.0.1', () => {
    log('INIT', `Lease listener active on port ${LEASE_PORT}`);
  });

  // ---- Authoritative session state: poll the opencode service.
  //      /api/session          -> every Session.Info (title, agent, model, cost, tokens, outcome, parentID)
  //      /api/session/active   -> sessions that own a live drain right now
  //      /api/session/{id}/permission + /form -> blocked on the user
  //      Credentials live in the service state file. Everything the legacy
  //      heartbeat state machine infers is treated as a hint; these reads decide
  //      which sessions are open, what they are doing and what they cost.
  let activeRunningIds = new Set();
  let serviceActiveStatus = new Map();
  let serviceSessions = new Map();
  let servicePending = new Set();
  let serviceMsgCounts = new Map();
  let serviceCreds = null;
  let serviceCredsMtime = 0;
  function readServiceCreds() {
    try {
      const f = path.join(os.homedir(), '.local', 'state', 'opencode', 'service.json');
      const st = fs.statSync(f);
      if (serviceCreds && st.mtimeMs === serviceCredsMtime) return serviceCreds;
      const j = JSON.parse(fs.readFileSync(f, 'utf8'));
      if (j && j.url && j.password) { serviceCreds = j; serviceCredsMtime = st.mtimeMs; return j; }
    } catch {}
    return serviceCreds;
  }
  function serviceFetch(pathname) {
    const creds = readServiceCreds();
    if (!creds) return null;
    const auth = Buffer.from('opencode:' + creds.password).toString('base64');
    return fetch(String(creds.url).replace(/\/$/, '') + pathname, {
      headers: { Authorization: 'Basic ' + auth },
      signal: AbortSignal.timeout(4000)
    });
  }
  async function serviceGet(pathname) {
    try {
      const res = await serviceFetch(pathname);
      if (!res || !res.ok) return null;
      return await res.json();
    } catch {
      return null;
    }
  }
  async function pollActiveSessions() {
    const j = await serviceGet('/api/session/active');
    if (!j) return;
    serviceActiveStatus = new Map(Object.entries(j.data || {}));
    activeRunningIds = new Set([...serviceActiveStatus.keys()].filter(id => serviceActiveStatus.get(id)?.type === 'running'));
  }
  async function pollServiceSessions() {
    const j = await serviceGet('/api/session?limit=' + SESSION_LIST_LIMIT + '&order=desc');
    if (!j || !Array.isArray(j.data)) return;
    const next = new Map();
    for (const info of j.data) {
      if (isSessionId(info?.id)) next.set(info.id, info);
    }
    serviceSessions = next;
    // Forget message counts for sessions the service no longer lists.
    if (serviceMsgCounts.size > next.size) {
      for (const id of [...serviceMsgCounts.keys()]) {
        if (!next.has(id)) serviceMsgCounts.delete(id);
      }
    }
  }
  // Pending permission/form requests are the authoritative "waiting for user"
  // signal; heartbeat inference sticks yellow long after the user answered.
  async function pollOpenSessionSignals() {
    if (interactionPollBusy) return;
    interactionPollBusy = true;
    try {
      const ids = [...activeSessions.keys()].filter(id => activeSessions.get(id).status !== 'closed');
      const results = await Promise.all(ids.map(async (id) => {
        const [perm, form, msgs] = await Promise.all([
          serviceGet('/api/session/' + encodeURIComponent(id) + '/permission'),
          serviceGet('/api/session/' + encodeURIComponent(id) + '/form'),
          pollMessageCount(id)
        ]);
        const blocked = (Array.isArray(perm?.data) && perm.data.length > 0) || (Array.isArray(form?.data) && form.data.length > 0);
        return { id, blocked, count: msgs };
      }));
      const pending = new Set();
      for (const r of results) {
        if (r.blocked) pending.add(r.id);
        if (typeof r.count === 'number') serviceMsgCounts.set(r.id, { count: r.count, at: Date.now() });
      }
      servicePending = pending;
    } catch {
    } finally {
      interactionPollBusy = false;
    }
  }
  // Message count is informational and only shown in extended view, so it is
  // capped: /api/session/{id}/message rejects limits above 200.
  async function pollMessageCount(id) {
    const cached = serviceMsgCounts.get(id);
    if (cached && Date.now() - cached.at < MSG_COUNT_TTL_MS) return cached.count;
    let count = 0;
    let cursor = null;
    for (let page = 0; page < 10; page++) {
      const query = '/api/session/' + encodeURIComponent(id) + '/message?limit=200' + (cursor ? '&cursor=' + encodeURIComponent(cursor) : '');
      const j = await serviceGet(query);
      if (!j || !Array.isArray(j.data) || j.data.length === 0) break;
      count += j.data.length;
      cursor = typeof j.cursor?.next === 'string' ? j.cursor.next : null;
      if (!cursor) break;
    }
    if (count === 0) return cached?.count;
    serviceMsgCounts.set(id, { count, at: Date.now() });
    return count;
  }
  pollActiveSessions();
  pollServiceSessions();
  setInterval(pollActiveSessions, ACTIVE_POLL_MS);
  setInterval(pollServiceSessions, SESSION_POLL_MS);
  setInterval(pollOpenSessionSignals, INTERACTION_POLL_MS);

  // TEMP-DEBUG: who announces presence (throttled per session), fjernes efter diagnose.
  const presenceLogFile = path.join(os.tmpdir(), 'dash-presence.log');
  const presenceLoggedAt = new Map();
  let interactionPollBusy = false;

  setInterval(() => {
    const now = Date.now();
    for (const [id, session] of activeSessions.entries()) {
      // Stale sessions should disappear quietly unless an explicit close event was received.
      // Et vindue der stadig viser sessionen holder den Ã¥ben trods manglende hjerteslag.
      const stillOpen = typeof session.openUntil === 'number' && session.openUntil > now;
      if (!stillOpen && session.status !== 'closed' && now - session.lastHeartbeat > STALE_HEARTBEAT_PURGE_MS) {
        log('PURGE', `Session heartbeat expired: ${shortId(id)} (${session.title})`);
        if (!session.parentId) forgetSubAgentMetricsForParent(id);
        activeSessions.delete(id);
        continue;
      }

      // Retain explicit closed sessions briefly before purging completely.
      if (session.status === 'closed' && session.closedAt && (now - session.closedAt > CLOSED_SESSION_RETENTION_MS)) {
        log('PURGE', `Closed session retention expired (${CLOSED_SESSION_RETENTION_MS / 1000}s): ${shortId(id)} (${session.title})`);
        if (!session.parentId) forgetSubAgentMetricsForParent(id);
        activeSessions.delete(id);
      }
    }
  }, 1000);

  function parseStatusInfo(statusStr) {
    switch (statusStr) {
      case 'running': return { type: 'running', label: 'Running', color: 'green' };
      case 'compacting': return { type: 'compacting', label: 'Compacting', color: 'cyan' };
      case 'user_response': return { type: 'user_response', label: 'Waiting for User Response', color: 'yellow' };
      case 'asking_parent': return { type: 'asking_parent', label: 'ASKING PARENT', color: 'yellow' };
      case 'interrupted': return { type: 'interrupted', label: 'Waiting (Interrupted)', color: 'orange' };
      case 'retrying': return { type: 'retrying', label: 'Retrying', color: 'skyblue' };
      case 'failed': return { type: 'failed', label: 'Failed', color: 'red' };
      case 'closed': return { type: 'closed', label: 'Closed', color: 'gray' };
      case 'waiting': return { type: 'waiting', label: 'Waiting (Idle)', color: 'white' };
      default: return { type: 'unknown', label: 'UNKNOWN', color: 'white' };
    }
  }

  function formatCompactDuration(ms) {
    if (!ms || ms < 0) return '0:00';
    const totalSeconds = Math.floor(ms / 1000);
    const seconds = totalSeconds % 60;
    const totalMinutes = Math.floor(totalSeconds / 60);
    const minutes = totalMinutes % 60;
    const hours = Math.floor(totalMinutes / 60);

    const secStr = String(seconds).padStart(2, '0');

    if (hours > 0) {
      const minStr = String(minutes).padStart(2, '0');
      return `${hours}:${minStr}:${secStr}`;
    }
    return `${minutes}:${secStr}`;
  }

  function formatCost(cost) {
    if (typeof cost !== 'number' || !isFinite(cost)) return null;
    return '$' + cost.toFixed(2);
  }

  function formatTokens(tokens) {
    const normalized = normalizeTokens(tokens);
    if (!normalized) return null;
    const fmt = (n) => {
      if (typeof n !== 'number' || !isFinite(n)) return null;
      if (n >= 1000000) return (n / 1000000).toFixed(1) + 'M';
      if (n >= 1000) return (n / 1000).toFixed(1) + 'k';
      return String(n);
    };
    const parts = [];
    const input = fmt(normalized.input);
    const cache = fmt(normalized.cache.read + normalized.cache.write);
    const output = fmt(normalized.output + normalized.reasoning);
    if (input !== null) parts.push(input + ' in');
    if (cache !== null && normalized.cache.read + normalized.cache.write > 0) parts.push(cache + ' cache');
    if (output !== null) parts.push(output + ' out');
    return parts.length ? parts.join(' / ') : null;
  }

  function applyFormattedMetrics(card) {
    card.cost = formatCost(card.costValue);
    card.tokens = formatTokens(card.tokensValue);
    card.subAgentCost = card.subAgentCostValue > 0 ? formatCost(card.subAgentCostValue) : null;
    card.subAgentTokens = tokenTotal(card.subAgentTokensValue) > 0 ? formatTokens(card.subAgentTokensValue) : null;
  }

  // The service is the source of truth for status: it knows which sessions own a
  // live drain (/api/session/active) and which are blocked on the user (pending
  // permission or form requests). Heartbeat inference only fills the states the
  // service cannot answer, and is downgraded when it contradicts the service -
  // that is what used to leave cards stuck green or yellow forever.
  function resolveDisplayStatus(id, s, info) {
    const legacy = s.status;
    if (legacy === 'closed') return 'closed';
    // A pending permission or form blocks the step, so it outranks the live
    // drain: a session waiting on the user is not "running", and V1 showed
    // exactly that as a yellow card with an alarm.
    if (servicePending.has(id)) return s.parentId ? 'asking_parent' : 'user_response';
    if (activeRunningIds.has(id)) return 'running';
    if (legacy === 'compacting' || legacy === 'retrying' || legacy === 'asking_parent') return legacy;
    if (info && info.outcome === 'failed') return 'failed';
    if (info && info.outcome === 'interrupted') return 'interrupted';
    if (legacy === 'user_response') return 'waiting';
    return legacy === 'running' ? 'waiting' : legacy;
  }

  // Session.Info wins over heartbeat guesses: it is the same data the TUI shows.
  function resolveCardTitle(s, info) {
    const serviceTitle = typeof info?.title === 'string' ? cleanTitle(info.title) : null;
    if (serviceTitle) return serviceTitle;
    return cleanTitle(s.title) || s.title;
  }

  function resolveCardDirectory(s, info) {
    return normalizeDirectory(info?.location?.directory) || normalizeDirectory(s.directory) || null;
  }

  function resolveCardParentId(s, info) {
    // A fork carries parentID but must always stay top level.
    if (info?.fork) return null;
    if (isSessionId(s.parentId)) return s.parentId;
    return isSessionId(info?.parentID) ? info.parentID : null;
  }

  function resolveCardCost(s, info) {
    if (typeof s.cost === 'number' && isFinite(s.cost) && s.cost > 0) return s.cost;
    if (typeof info?.cost === 'number' && isFinite(info.cost)) return info.cost;
    return undefined;
  }

  function resolveCardTokens(s, info) {
    if (tokenTotal(s.tokens) > 0) return s.tokens;
    return normalizeTokens(info?.tokens);
  }

  // "Ã…ben" afgÃ¸res her, ikke af hjerteslag. Reporteren hjertslaer hver session
  // den nogensinde har set, sÃ¥ uden denne filtrering bliver dashboardet et
  // arkiv over hele historikken for hver service-genstart.
  //
  // RÃ¦kkefÃ¸lgen er bevidst: tilstedevÃ¦relse fÃ¸rst. Et vindue der viser en
  // session har sat openUntil (se /api/presence), og intet mÃ¥ overrige det -
  // time.viewed er ikke brugbart, fordi opencode kun opdaterer den ved
  // session-skift, sÃ¥ et vindue der har stÃ¥et pÃ¥ samme session i timevis er
  // "aldrig set" i service-data. Derefter de to ting der er objektive:
  // en live drain, eller en besvarelse der mangler.
  function isOpenSession(id, s, now) {
    if (typeof s.openUntil === 'number' && s.openUntil > now) return true;
    if (activeRunningIds.has(id)) return true;
    if (servicePending.has(id)) return true;
    return false;
  }

  function buildCardData(id, s, now) {
    const info = serviceSessions.get(id) || null;
    const displayStatus = resolveDisplayStatus(id, s, info);
    if (displayStatus === 'running' && !s.runningSince) s.runningSince = now;
    const visibleStatus = displayStatus === 'waiting' && isInterruptedError(s.error) ? 'interrupted' : displayStatus;
    const isWaitingState = visibleStatus === 'waiting' || visibleStatus === 'user_response' || visibleStatus === 'asking_parent' || visibleStatus === 'interrupted';
    const waitingTimeMs = isWaitingState ? (now - (s.statusChangedAt || now)) : 0;
    const endTime = s.closedAt ? s.closedAt : now;
    const isRunningLike = visibleStatus === 'running' || visibleStatus === 'compacting';
    const runtimeMs = isRunningLike
      ? Math.max(0, endTime - (s.runningSince || s.statusChangedAt || s.startTime))
      : Math.max(0, s.lastRuntimeMs || 0);
    const uptimeMs = Math.max(0, endTime - s.startTime);

    const card = {
      id: id,
      title: resolveCardTitle(s, info),
      agent: (typeof info?.agent === 'string' && info.agent) ? formatAgentName(info.agent, !!resolveCardParentId(s, info)) : (s.agent || 'Build'),
      model: modelToString(info?.model) ? formatModelName(modelToString(info.model)) : (s.model || 'Claude Haiku 4.5'),
      directory: resolveCardDirectory(s, info),
      parentId: resolveCardParentId(s, info),
      status: parseStatusInfo(visibleStatus),
      alarmEligible: s.alarmEligible === true,
      startTime: s.startTime,
      lastActivity: (typeof s.lastActivityAt === 'number' ? s.lastActivityAt : s.startTime),
      totalUptime: formatCompactDuration(uptimeMs),
      runtime: formatCompactDuration(runtimeMs),
      waitingTime: isWaitingState ? formatCompactDuration(waitingTimeMs) : null,
      isCacheCold: isWaitingState && waitingTimeMs >= COLD_CACHE_MS,
      costValue: resolveCardCost(s, info),
      tokensValue: resolveCardTokens(s, info),
      subAgentCostValue: 0,
      subAgentTokensValue: undefined,
      subAgentMsgCount: 0,
      cost: null,
      tokens: null,
      subAgentCost: null,
      subAgentTokens: null,
      error: s.error || null,
      retryInfo: s.retryInfo || null,
      msgCount: s.msgCount || serviceMsgCounts.get(id)?.count || 0,
      compactionCount: s.compactionCount || 0,
      todos: Array.isArray(s.todos) ? s.todos : [],
      subAgents: []
    };
    const persistedTokens = readPersistedSessionTokens(id);
    if (persistedTokens && tokenTotal(card.tokensValue) === 0) card.tokensValue = persistedTokens;
    applyFormattedMetrics(card);
    return card;
  }

  function hasInProgressTodo(card) {
    return Array.isArray(card.todos) && card.todos.some(t => t && t.status === 'in_progress');
  }

  function getCards() {
    const now = Date.now();
    const sessionCardsMap = new Map();

    // Kun Ã¥bne sessions kommer pÃ¥ kort. Hjerteslag er ikke nok: reporteren
    // hjertslaer alt den har set, sÃ¥ uden denne filtrering vokser dashboardet
    // til en liste over hele historikken for hver service-genstart.
    for (const [id, s] of activeSessions.entries()) {
      if (!isOpenSession(id, s, now)) continue;
      sessionCardsMap.set(id, buildCardData(id, s, now));
    }

    // En live drain er Ã¥ben per definition, selv uden at et vindue har meldt sig
    // endnu (ny session, headless kÃ¸rsel, reporter-forsinkelse).
    for (const id of activeRunningIds.keys()) {
      if (sessionCardsMap.has(id)) continue;
      sessionCardsMap.set(id, buildCardData(id, {
        title: 'Active Terminal',
        agent: 'Build',
        model: 'Claude Haiku 4.5',
        parentId: null,
        status: 'running',
        startTime: now,
        statusChangedAt: now,
        runningSince: now,
        lastRuntimeMs: 0
      }, now));
    }

    const rootCards = [];

    for (const [id, card] of sessionCardsMap.entries()) {
      // Forks are always top-level even if they carry a stale parentId
      const isForkCard = isForkTitle(card.title);
      if (!isForkCard && card.parentId && sessionCardsMap.has(card.parentId)) {
        const parentCard = sessionCardsMap.get(card.parentId);
        // Don't nest under a fork parent either
        if (!isForkTitle(parentCard.title)) {
          parentCard.subAgents.push(card);
        } else {
          rootCards.push(card);
        }
      } else {
        rootCards.push(card);
      }
    }

    // Parent cards include their direct sub-agent usage and stay running while active work is tracked.
    for (const card of rootCards) {
      let hasActiveSubAgent = false;
      const subAgentTotals = getSubAgentMetricTotals(card.id);
      if (subAgentTotals.costValue > 0 || tokenTotal(subAgentTotals.tokensValue) > 0 || subAgentTotals.msgCount > 0) {
        card.subAgentCostValue = subAgentTotals.costValue;
        card.subAgentTokensValue = subAgentTotals.tokensValue;
        card.subAgentMsgCount = subAgentTotals.msgCount;
        if (typeof card.costValue === 'number' && isFinite(card.costValue)) card.costValue += subAgentTotals.costValue;
        else if (subAgentTotals.costValue > 0) card.costValue = subAgentTotals.costValue;
        card.tokensValue = addTokens(card.tokensValue, subAgentTotals.tokensValue);
        card.msgCount = (card.msgCount || 0) + subAgentTotals.msgCount;
        applyFormattedMetrics(card);
      }
      if (card.subAgents && card.subAgents.length > 0) {
        hasActiveSubAgent = card.subAgents.some(sub => sub.status.type === 'running' || sub.status.type === 'asking_parent' || hasInProgressTodo(sub));
      }
      if (hasActiveSubAgent && card.status.type !== 'closed' && card.status.type !== 'interrupted') {
        card.status = parseStatusInfo('running');
        card.waitingTime = null;
        card.isCacheCold = false;
      }
    }

    rootCards.sort((a, b) => a.startTime - b.startTime || a.id.localeCompare(b.id));
    for (const card of rootCards) {
      if (card.subAgents.length > 0) {
        card.subAgents.sort((a, b) => a.startTime - b.startTime || a.id.localeCompare(b.id));
      }
    }

    return rootCards;
  }

  function generateDashboardHTML() {
    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <title>OpenCode Terminal Dashboard</title>
  <script>
    window.openStates = window.openStates || {};
    window.lastStatuses = window.lastStatuses || {};

    window.dashboardLabels = {};
    try { window.dashboardLabels = JSON.parse(localStorage.getItem('dashboardLabels') || '{}'); } catch(e) {}

    var labelColors = ['blue', 'green', 'red', 'yellow', 'orange', 'purple', 'pink', 'cyan', 'gray', 'white'];

    // groupColor() hands back a NAME ("blue"), which is fine for a CSS class
    // but not for an SVG fill written into a style attribute. Map it to hex.
    var COLOR_HEX = {
      blue: '#3b82f6', green: '#22c55e', red: '#ef4444', yellow: '#eab308',
      orange: '#f97316', purple: '#a855f7', pink: '#ec4899', cyan: '#06b6d4',
      gray: '#64748b', white: '#e2e8f0', skyblue: '#38bdf8',
    };
    function colorHex(name) {
      if (!name) return '#3b82f6';
      if (String(name).slice(0, 1) === '#') return String(name);
      return COLOR_HEX[String(name)] || '#3b82f6';
    }

    // One colour per group, keyed by grouping mode + group name. A directory
    // group and a status group can share a name ("test") and must be able to
    // differ, so the mode is part of the key. Kept apart from dashboardLabels:
    // a session's own label colour is not a group colour. No entry means
    // "auto" - the built-in colours that carry meaning (Error red, Running
    // green, directory blue).
    window.dashboardGroupColors = {};
    try { window.dashboardGroupColors = JSON.parse(localStorage.getItem('dashboardGroupColors') || '{}'); } catch(e) {}

    function groupColorKey(grouping, label) {
      return String(grouping || '?') + ':' + String(label == null ? '' : label);
    }
    function getGroupColor(grouping, label) {
      var v = window.dashboardGroupColors[groupColorKey(grouping, label)];
      return (typeof v === 'string' && labelColors.indexOf(v) !== -1) ? v : 'auto';
    }
    function setGroupColor(grouping, label, color) {
      var key = groupColorKey(grouping, label);
      if (!color || color === 'auto') delete window.dashboardGroupColors[key];
      else window.dashboardGroupColors[key] = color;
      try { localStorage.setItem('dashboardGroupColors', JSON.stringify(window.dashboardGroupColors)); } catch(e) {}
    }
    function labelData(id) {
      var value = window.dashboardLabels[id];
      if (!value) return null;
      if (typeof value !== 'object') return null;
      return { text: value.text || '', color: value.color || 'blue' };
    }
    function existingLabels() {
      var seen = {};
      var labels = [];
      Object.keys(window.dashboardLabels).forEach(function(id) {
        var data = labelData(id);
        if (!data || !data.text || seen[data.text]) return;
        seen[data.text] = true;
        labels.push(data);
      });
      labels.sort(function(a, b) { return a.text.localeCompare(b.text); });
      return labels;
    }
    function getLabel(id) {
      var data = labelData(id);
      return data && data.text ? data.text : null;
    }
    function getLabelColor(id) {
      var data = labelData(id);
      return data && data.color ? data.color : 'blue';
    }
    function setLabel(id, label) {
      if (label) window.dashboardLabels[id] = { text: label, color: getLabelColor(id) }; else delete window.dashboardLabels[id];
      try { localStorage.setItem('dashboardLabels', JSON.stringify(window.dashboardLabels)); } catch(e) {}
    }
    function setLabelColor(id, color) {
      var text = getLabel(id);
      if (!text || labelColors.indexOf(color) === -1) return;
      window.dashboardLabels[id] = { text: text, color: color };
      try { localStorage.setItem('dashboardLabels', JSON.stringify(window.dashboardLabels)); } catch(e) {}
    }
    function setExistingLabel(id, data) {
      if (!data || !data.text) return;
      window.dashboardLabels[id] = { text: data.text, color: data.color || 'blue' };
      try { localStorage.setItem('dashboardLabels', JSON.stringify(window.dashboardLabels)); } catch(e) {}
    }

    function addExistingLabelsSubmenu(menu, id, labels) {
      if (!labels.length) return;
      var wrap = document.createElement('div');
      wrap.className = 'context-submenu-wrap';
      var trigger = document.createElement('button');
      trigger.type = 'button';
      trigger.className = 'context-submenu-trigger';
      trigger.textContent = 'Labels';
      var submenu = document.createElement('div');
      submenu.className = 'context-submenu';
labels.forEach(function(data) {
        var row = document.createElement('div');
        row.className = 'label-pick-row';
        var btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'label-pick label-' + data.color;
        btn.textContent = data.text;
        btn.onclick = function(e) { e.stopPropagation(); setExistingLabel(id, data); refresh(); closeMenu(); };
        var del = document.createElement('button');
        del.type = 'button';
        del.className = 'label-pick-remove';
        del.textContent = '\u00d7';
        del.title = 'Remove this label from all sessions';
        del.onclick = function(e) {
          e.stopPropagation();
          Object.keys(window.dashboardLabels).forEach(function(sid) {
            var d = labelData(sid);
            if (d && d.text === data.text) delete window.dashboardLabels[sid];
          });
          try { localStorage.setItem('dashboardLabels', JSON.stringify(window.dashboardLabels)); } catch(e2) {}
          refresh();
          closeMenu();
        };
        row.appendChild(btn);
        row.appendChild(del);
        submenu.appendChild(row);
      });
      wrap.appendChild(trigger);
      wrap.appendChild(submenu);
      menu.appendChild(wrap);
    }

    function labelBadge(id) {
      var l = getLabel(id);
      return l ? '<span class="session-label label-' + esc(getLabelColor(id)) + '">' + esc(l) + '</span>' : '';
    }

    function closeMenu() {
      if (window._labelMenu) { window._labelMenu.remove(); window._labelMenu = null; }
    }

    function showLabelMenu(x, y, id) {
      closeMenu();
      var menu = document.createElement('div');
      menu.className = 'context-menu';
      var setBtn = document.createElement('button');
      setBtn.textContent = 'Set label...';
      setBtn.onclick = function() {
        var v = prompt('Label for session:', getLabel(id) || '');
        if (v !== null) { setLabel(id, v.trim()); refresh(); }
        closeMenu();
      };
      var clearBtn = document.createElement('button');
      clearBtn.textContent = 'Remove label';
      clearBtn.onclick = function() { setLabel(id, null); refresh(); closeMenu(); };
      menu.appendChild(setBtn);
      var labels = existingLabels();
      addExistingLabelsSubmenu(menu, id, labels);
      if (getLabel(id)) {
        var colorTitle = document.createElement('div');
        colorTitle.className = 'context-menu-title';
        colorTitle.textContent = 'Set label color';
        menu.appendChild(colorTitle);
        var colorGrid = document.createElement('div');
        colorGrid.className = 'label-color-grid';
        labelColors.forEach(function(color) {
          var btn = document.createElement('button');
          btn.type = 'button';
          btn.className = 'label-color-choice label-' + color;
          btn.title = color.charAt(0).toUpperCase() + color.slice(1);
          btn.onclick = function(e) { e.stopPropagation(); setLabelColor(id, color); refresh(); };
          colorGrid.appendChild(btn);
        });
        menu.appendChild(colorGrid);
      }
      menu.appendChild(clearBtn);
      menu.style.left = x + 'px';
      menu.style.top = y + 'px';
      document.body.appendChild(menu);
      window._labelMenu = menu;
      setTimeout(function() { document.addEventListener('click', closeMenu, { once: true }); }, 0);
    }

    // Colour for one specific group header. Right-click the header itself.
    function showGroupColorMenu(x, y, grouping, label) {
      closeMenu();
      var menu = document.createElement('div');
      menu.className = 'context-menu';
      var title = document.createElement('div');
      title.className = 'context-menu-title';
      title.textContent = 'Color for "' + (label || 'group') + '"';
      menu.appendChild(title);

      var current = getGroupColor(grouping, label);
      var grid = document.createElement('div');
      grid.className = 'label-color-grid';
      // Auto first: it restores the built-in colours that carry meaning.
      var autoBtn = document.createElement('button');
      autoBtn.type = 'button';
      autoBtn.className = 'label-color-choice label-auto' + (current === 'auto' ? ' chosen' : '');
      autoBtn.title = 'Auto';
      autoBtn.textContent = 'A';
      autoBtn.onclick = function(e) { e.stopPropagation(); setGroupColor(grouping, label, 'auto'); closeMenu(); refresh(); };
      grid.appendChild(autoBtn);

      labelColors.forEach(function(color) {
        var btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'label-color-choice label-' + color + (current === color ? ' chosen' : '');
        btn.title = color.charAt(0).toUpperCase() + color.slice(1);
        btn.onclick = function(e) { e.stopPropagation(); setGroupColor(grouping, label, color); closeMenu(); refresh(); };
        grid.appendChild(btn);
      });
      menu.appendChild(grid);
      menu.style.left = x + 'px';
      menu.style.top = y + 'px';
      document.body.appendChild(menu);
      window._labelMenu = menu;
      setTimeout(function() { document.addEventListener('click', closeMenu, { once: true }); }, 0);
    }

    document.addEventListener('contextmenu', function(e) {
      // Group header before card: a header can sit inside the grid, and a
      // card click must not swallow it.
      var header = e.target.closest ? e.target.closest('.group-header[data-group-label]') : null;
      if (header) {
        e.preventDefault();
        showGroupColorMenu(
          e.clientX, e.clientY,
          header.getAttribute('data-grouping'),
          header.getAttribute('data-group-label')
        );
        return;
      }
      var el = e.target.closest ? e.target.closest('.card, .sub-card') : null;
      if (!el) return;
      var id = el.getAttribute('data-session-id');
      if (!id) return;
      e.preventDefault();
      showLabelMenu(e.clientX, e.clientY, id);
    });

    function shortId(id) {
      if (!id || typeof id !== 'string') return 'none';
      return id.length > 6 ? '...' + id.slice(-6) : id;
    }

    function esc(s) {
      return String(s == null ? '' : s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
    }

    function statusTitle(c) {
      if (c.error && (c.status.type === 'interrupted' || c.status.type === 'failed')) {
        return 'Error: ' + c.error;
      }
      if (c.status.type === 'retrying' && c.retryInfo) {
        var r = c.retryInfo;
        var t = 'Retry';
        if (typeof r.attempt === 'number') t += ' ' + r.attempt + (typeof r.next === 'number' ? '/' + r.next : '');
        if (r.message) t += ': ' + r.message;
        return t;
      }
      return '';
    }

    function metaLine(c, extended, compact) {
      var line1 = [];
      if (!compact) {
        line1.push('<span class="label">Uptime:</span> <span class="value timer-value">' + c.totalUptime + '</span>');
        line1.push('<span class="divider">-</span> <span class="label">Runtime:</span> <span class="value timer-value">' + c.runtime + '</span>');
        if (c.waitingTime) line1.push('<span class="divider">-</span> <span class="label">Idle:</span> <span class="value timer-value highlight-waiting">' + c.waitingTime + '</span>' + (c.isCacheCold ? ' <span class="cold-cache" title="Cache cold">&#10052;</span>' : ''));
      }

      var line2 = [];
      var line3 = [];
      function pushMetric(html) {
        if (line2.length) line2.push('<span class="divider">-</span> ' + html);
        else line2.push(html);
      }
      if (extended && c.msgCount > 0) pushMetric('<span class="label">Msgs:</span> <span class="value">' + c.msgCount + ' (' + (c.subAgentMsgCount || 0) + ')' + '</span>');
      if (extended && c.cost) pushMetric('<span class="label">Cost:</span> <span class="value">' + esc(c.cost) + '</span>');
      if (extended && c.compactionCount > 0) pushMetric('<span class="label">Compactions:</span> <span class="value">' + c.compactionCount + '</span>');
      if (extended && c.tokens) line3.push('<span class="label">Tokens:</span> <span class="value" title="In = tokens sent to the model (prompt, context, tools) / Out = tokens generated by the model (response, reasoning)">' + esc(c.tokens) + '</span>');

      var html = '<div>' + line1.join('') + '</div>';
      if (line2.length) html += '<div>' + line2.join('') + '</div>';
      if (line3.length) html += '<div>' + line3.join('') + '</div>';
      return html;
    }

    function todoIcon(status) {
      if (status === 'completed') return '&#9745;';
      if (status === 'in_progress') return '&#9680;';
      if (status === 'cancelled') return '&#10005;';
      return '&#9633;';
    }

    function todoColor(status) {
      if (status === 'completed') return '#22c55e';
      if (status === 'in_progress') return '#eab308';
      if (status === 'cancelled') return '#64748b';
      return '#94a3b8';
    }

    function todosHTML(c) {
      if (!c.todos || c.todos.length === 0) return '';
      var done = c.todos.filter(function(t) { return t.status === 'completed'; }).length;
      var autoFoldTodos = localStorage.getItem('dashboardAutoFoldTodos') !== 'no';
      var isOpen = autoFoldTodos ? window.openStates['todo-' + c.id] === true : true;
      var openAttr = isOpen ? ' open' : '';
      var items = c.todos.map(function(t) {
        return '<div class="todo-row" style="color:' + todoColor(t.status) + '">' +
          '<span class="todo-icon">' + todoIcon(t.status) + '</span> ' +
          '<span class="todo-text">' + esc(t.content) + '</span>' +
          (t.priority ? '<span class="todo-priority">' + esc(t.priority) + '</span>' : '') +
        '</div>';
      }).join('');
      return '<div class="todos-container">' +
        '<details data-card-id="todo-' + c.id + '" class="todos-details"' + openAttr + '>' +
          '<summary class="todos-summary">' +
            '<span class="chevron">&#9654;</span> TODOS (' + done + '/' + c.todos.length + '):' +
          '</summary>' +
          '<div class="todos-list">' + items + '</div>' +
        '</details>' +
      '</div>';
    }

    function beep(freq, dur) {
      try {
        if (!window.audioCtx) window.audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        var ctx = window.audioCtx;
        if (ctx.state === 'suspended') ctx.resume();
        var lowFreq = Math.max(180, freq * 0.75);
        var half = dur / 2;

        function playTone(startAt, toneFreq, toneDur) {
          var o = ctx.createOscillator();
          var g = ctx.createGain();
          o.connect(g);
          g.connect(ctx.destination);
          o.type = 'sine';
          o.frequency.value = toneFreq;
          g.gain.setValueAtTime(0.3, startAt);
          g.gain.exponentialRampToValueAtTime(0.0001, startAt + toneDur);
          o.start(startAt);
          o.stop(startAt + toneDur);
        }

        playTone(ctx.currentTime, lowFreq, half);
        playTone(ctx.currentTime + half, freq, half);
      } catch(e) {}
    }

    function checkAlarms(cards, jobsDone, errors, users) {
      if (!jobsDone && !errors && !users) { window.lastStatuses = {}; return; }
      var now = {};
      cards.forEach(function(c) { now[c.id] = { status: c.status.type, alarmEligible: c.alarmEligible === true }; });
      Object.keys(now).forEach(function(id) {
        var prev = window.lastStatuses[id];
        if (prev && prev.status !== now[id].status) {
          if (now[id].status === 'failed' && errors) beep(880, 1.0);
          else if (now[id].status === 'user_response' && now[id].alarmEligible && users) beep(660, 0.6);
          else if (now[id].status === 'closed' && jobsDone) beep(520, 0.6);
        }
      });
      window.lastStatuses = now;
    }


    function renderSubAgent(sub, mode, grouping) {
      var extended = mode === 'extended';
      var compact = mode === 'compact';
      var badgeTitle = statusTitle(sub);
      var showLabelBadge = grouping !== 'label';
      return '<div class="sub-card status-' + sub.status.color + '" data-session-id="' + sub.id + '">' +
        '<div class="card-header">' +
          '<div class="sub-session-title">&#129302; ' + esc(sub.title) + (showLabelBadge ? labelBadge(sub.id) : '') + '</div>' +
          '<div class="subtitle-row">' +
            '<span class="sub-session-subtitle">' + esc(sub.agent) + ' (' + esc(sub.model) + ')</span>' +
            '<span class="badge badge-' + sub.status.color + '"' + (badgeTitle ? ' title="' + esc(badgeTitle) + '"' : '') + '>' + sub.status.label + '</span>' +
          '</div>' +
        '</div>' +
        '<div class="card-body">' +
          '<div class="time-compact">' + metaLine(sub, extended, compact) + '</div>' +
        '</div>' +
        todosHTML(sub) +
      '</div>';
    }

    function cardHTML(c, mode, grouping) {
      var compact = mode === 'compact';
      var autoFoldAgents = localStorage.getItem('dashboardAutoFoldAgents') !== 'no';
      var isOpen = autoFoldAgents ? window.openStates[c.id] === true : true;
      var openAttr = isOpen ? ' open' : '';
      var badgeTitle = statusTitle(c);
      var showLabelBadge = grouping !== 'label';

      var subAgentsHTML = (c.subAgents && c.subAgents.length > 0)
        ? '<div class="sub-agents-container">' +
            '<details data-card-id="' + c.id + '" class="sub-agents-details"' + openAttr + '>' +
              '<summary class="sub-agents-summary">' +
                '<span class="chevron">&#9654;</span> ACTIVE SUB-AGENTS (' + c.subAgents.length + '):' +
              '</summary>' +
              '<div class="sub-agents-list">' +
                c.subAgents.map(function(sub) { return renderSubAgent(sub, mode, grouping); }).join('') +
              '</div>' +
            '</details>' +
          '</div>'
        : '';

      return '<div class="card status-' + c.status.color + '" data-session-id="' + c.id + '">' +
        '<div class="card-header">' +
          '<div class="session-title">' + esc(c.title) + (showLabelBadge ? labelBadge(c.id) : '') + '</div>' +
          '<div class="subtitle-row">' +
            '<span class="session-subtitle">' + esc(c.agent) + ' (' + esc(c.model) + ')</span>' +
            '<span class="badge badge-' + c.status.color + '"' + (badgeTitle ? ' title="' + esc(badgeTitle) + '"' : '') + '>' + c.status.label + '</span>' +
          '</div>' +
        '</div>' +
        '<div class="card-body">' +
          '<div class="time-compact">' + metaLine(c, mode === 'extended', compact) + '</div>' +
        '</div>' +
        todosHTML(c) +
        subAgentsHTML +
        (compact ? '' : '<div class="card-footer">Session ID: ' + esc(c.id) + '</div>') +
      '</div>';
    }

    function directoryGroup(c) {
      return (c && c.directory) ? String(c.directory) : 'No directory';
    }

    // Group label: the last folder only. "C:/Desktop/gizmo-factory" reads as
    // "gizmo-factory". The full path stays on the header tooltip, and grouping
    // still keys on the whole path so two projects with the same folder name
    // stay separate groups.
    function directoryName(dir) {
      if (!dir) return '';
      var parts = String(dir).split('/').filter(Boolean);
      return parts.length ? parts[parts.length - 1] : String(dir);
    }

    // Status buckets, used for the shirt colour in the office view.
    function statusGroup(c) {
      var type = c.status && c.status.type;
      if (type === 'failed' || type === 'interrupted' || type === 'retrying') return 'Error';
      if (type === 'user_response' || type === 'asking_parent') return 'User Request';
      if (type === 'running' || type === 'compacting') return 'Running';
      if (type === 'waiting') return 'Waiting';
      if (type === 'closed') return 'Closed';
      return 'Unknown';
    }

    function groupColor(label, cards, grouping) {
      // A colour chosen for this exact group wins over every automatic rule
      // below, including the status colours that carry meaning.
      var forced = getGroupColor(grouping, label);
      if (forced !== 'auto') return forced;
      if (label === 'Error') return 'red';
      if (label === 'User Request') return 'yellow';
      if (label === 'Running') return 'green';
      if (label === 'Waiting') return 'white';
      if (label === 'Closed') return 'gray';
      if (label === 'Unknown' || label === 'Unlabeled' || label === 'No directory') return 'white';
      for (var i = 0; cards && i < cards.length; i++) {
        var data = labelData(cards[i].id);
        if (data && data.text === label && data.color) return data.color;
      }
      // Directories are neutral, not a status colour: many projects have no
      // running session, and painting the group green would imply otherwise.
      if (label && label.indexOf('/') !== -1) return 'blue';
      return cards && cards[0] && cards[0].status && cards[0].status.color ? cards[0].status.color : 'white';
    }

    function groupedHTML(cards, mode, grouping) {
      if (grouping === 'none') return cards.map(function(c) { return cardHTML(c, mode, grouping); }).join('');

      var groups = [];
      if (grouping === 'label') {
        var hasLabels = cards.some(function(c) { return !!getLabel(c.id); });
        if (!hasLabels) return cards.map(function(c) { return cardHTML(c, mode, 'none'); }).join('');
        var labelMap = {};
        cards.forEach(function(c) {
          var key = getLabel(c.id) || 'Unlabeled';
          if (!labelMap[key]) labelMap[key] = [];
          labelMap[key].push(c);
        });
        Object.keys(labelMap).sort(function(a, b) {
          if (a === 'Unlabeled') return 1;
          if (b === 'Unlabeled') return -1;
          return a.localeCompare(b);
        }).forEach(function(label) { groups.push({ label: label, labelGroup: true, color: groupColor(label, labelMap[label], 'label'), cards: labelMap[label] }); });
      } else if (grouping === 'status') {
        ['Error', 'User Request', 'Running', 'Waiting', 'Closed', 'Unknown'].forEach(function(label) {
          var items = cards.filter(function(c) { return statusGroup(c) === label; });
          if (items.length) groups.push({ label: label, color: groupColor(label, items, 'status'), cards: items });
        });
      } else if (grouping === 'directory') {
        var byDir = {};
        cards.forEach(function(c) {
          var key = directoryGroup(c);
          if (!byDir[key]) byDir[key] = [];
          byDir[key].push(c);
        });
        // "No directory" last: it is the exception, not a project.
        Object.keys(byDir).sort(function(a, b) {
          if (a === 'No directory') return 1;
          if (b === 'No directory') return -1;
          return a.localeCompare(b);
        }).forEach(function(label) {
          groups.push({ label: label, color: groupColor(label, byDir[label], 'directory'), cards: byDir[label] });
        });
      }

      return groups.map(function(group) {
        var groupKey = 'group-' + grouping + '-' + group.label;
        var isOpen = window.openStates[groupKey] !== false;
        return '<section class="group-box group-' + esc(group.color) + '">' +
          '<button type="button" class="group-header' + (group.labelGroup ? ' label-group' : '') + '" data-group-key="' + esc(groupKey) + '" data-grouping="' + esc(grouping) + '" data-group-label="' + esc(group.label) + '">' +
            '<span class="chevron">' + (isOpen ? '&#9660;' : '&#9654;') + '</span> ' +
            (grouping === 'directory' && group.label !== 'No directory'
              ? '<span class="group-dir" title="' + esc(group.label) + '">' + esc(directoryName(group.label)) + '</span>'
              : esc(group.label)) +
            ' (' + group.cards.length + ')' +
          '</button>' +
          '<div class="group-body' + (isOpen ? '' : ' collapsed') + '">' +
            '<div class="group-cards grid">' + group.cards.map(function(c) { return cardHTML(c, mode, grouping); }).join('') + '</div>' +
          '</div>' +
        '</section>';
      }).join('');
    }

    // ==================================================================
    // House view: one room per group, one small isometric figure per session.
    // Figures wear the colour of their group, so a room reads as one project.
    // ==================================================================

    // What a figure is doing, derived only from signals the service actually
    // exposes: status.type plus the pending-permission flag the card carries.
    function activity(c) {
      var t = c.status && c.status.type;
      if (t === 'running' || t === 'compacting') return 'working';
      if (t === 'user_response' || t === 'asking_parent') return 'blocked';
      if (t === 'failed' || t === 'retrying') return 'error';
      if (t === 'interrupted') return 'sulk';
      return 'idle';
    }


    // ==================================================================
    // Office view: ONE empty floor split into four equal quarters, one per
    // status class. Every session stands in the quarter its status calls for
    // and walks between three points inside it.
    //
    // The furniture drawing code below (ISLANDS, SPOTS, MEETING, FOOTPRINT,
    // isoPlace and friends) is no longer called. It is kept because putting
    // the room back is a one-line change in houseOfficeHTML, and because
    // BLOCKED is still consulted by walkable() and the pathfinder.
    // ==================================================================

    // ---- Isometric projection --------------------------------------
    // Everything lives on a square grid of tiles and is projected to screen
    // with the standard 2:1 isometric formula. Working in grid coordinates
    // means "one tile up-right" and "one tile down-left" are just +/-1, so
    // spots are described the way you would describe them on paper.
    //   x = (c - r) * halfW        c grows right-and-down
    //   y = (c + r) * halfH        r grows left-and-down
    var TW = 56, TH = 28;          // tile diamond, 2:1
    var GRID = 18;                 // tiles per side
    var ORIGIN_X = 520, ORIGIN_Y = 96;

    function isoX(c, r) { return ORIGIN_X + (c - r) * (TW / 2); }
    function isoY(c, r) { return ORIGIN_Y + (c + r) * (TH / 2); }

    // The room is laid out after the reference image: a walled meeting room in the
    // far left, two rows of three desks across the middle, shelving on the far
    // right, and the break area along the near edge - espresso machine, dart
    // board, two sofas around a coffee table.
    //
    // GRID 18 wide. Diagonals matter: a row on a constant c or r draws as a
    // line going down-right or down-left, while a row on a constant c+r draws
    // horizontally across the screen. The desk rows use both.

    // Desks: two rows of three. A row on a constant r draws as a horizontal
    // line across the screen, and the second row is shifted one tile left,
    // which is how the reference image shows them. The rows are three tiles
    // apart because each desk is a 2x2 footprint, and two rows two apart
    // would touch.
    var ISLANDS = [
      { c: 7, r: 2 }, { c: 9, r: 2 }, { c: 11, r: 2 },
      { c: 6, r: 5 }, { c: 8, r: 5 }, { c: 10, r: 5 },
    ];

    var SPOTS = {
      // Kitchen end of the break area.
      coffee:  { c: 6,  r: 10 },   // espresso machine on its counter
      darts:   { c: 6,  r: 13 },   // dart board on a short partition
      // Lounge: two sofas either side of a low table, as drawn.
      sofaA:   { c: 9,  r: 11 },
      table:   { c: 11, r: 11 },   // books and a plant
      sofaB:   { c: 13, r: 10 },
      // Far right: shelving, and the broom closet behind it.
      shelves: { c: 14, r: 3 },
      closet:  { c: 15, r: 1 },
      sulk:    { c: 15, r: 8 },
      toilet:  { c: 1,  r: 7 },
      door:    { c: 5,  r: 7 },    // by the meeting room wall, as drawn
    };
    var CHILL_SPOTS = ['coffee', 'darts', 'sofaA', 'sofaB', 'toilet'];

    // Footprints, in tiles. These are the obstacles pathfinding walks around.
    var FOOTPRINT = {
      island: [2, 2], coffee: [2, 1], darts: [2, 2], sofaA: [2, 2], sofaB: [2, 2],
      table: [2, 2], shelves: [2, 3], closet: [2, 2], sulk: [1, 1], toilet: [2, 2],
      door: [1, 1],
    };

// The walled meeting room in the far corner. Nobody works in here, so the
    // whole footprint including the interior is solid.
    var MEETING = { c: 1, r: 1, w: 5, h: 5 };

    // ---- Pathfinding -------------------------------------------------
    // A* on the tile grid. Furniture blocks tiles, so figures step around the
    // desks instead of walking through them, which is what made the office
    // look like the figures were ignoring the furniture entirely.
    function inBounds(c, r) { return c >= 0 && r >= 0 && c <= GRID && r <= GRID; }

    // The floor is empty now - the four quarters are the only division - so no
    // tile is blocked. The function stays because BLOCKED is still consulted by
    // walkable() and the pathfinder, and blocking a quarter would be the one
    // change needed to put walls back.
    function buildBlocked() {
      return Object.create(null);
    }
    var BLOCKED = buildBlocked();

    function walkable(c, r) { return inBounds(c, r) && !BLOCKED[c + ',' + r]; }

    // The seat tile itself sits inside a footprint, so aim for a tile a figure can
    // actually stand on. Prefer the one CLOSEST TO THE VIEWER (largest c+r):
    // picking the nearest tile by distance alone put people on the far side of
    // the desks, which is why they rendered behind the furniture.
    function seatTile(t) {
      if (walkable(t.c, t.r)) return { c: t.c, r: t.r };
      var best = null, bestScore = -1e9;
      for (var dc = 0; dc <= 2; dc++) for (var dr = 0; dr <= 2; dr++) {
        for (var s = 0; s < 4; s++) {
          var c = t.c + (s === 1 || s === 2 ? -dc : dc);
          var r = t.r + (s >= 2 ? dr : -dr);
          if (!walkable(c, r)) continue;
          // deeper in the room wins; then closest wins
          var score = (c + r) * 10 - (dc + dr);
          if (score > bestScore) { bestScore = score; best = { c: c, r: r }; }
        }
      }
      return best || { c: t.c, r: t.r };
    }

    // ---- Seats ------------------------------------------------------
    // Where a figure stands for a piece of furniture, as a tile offset
    // (dc,dr) from the spot's own tile.
    //
    // The rule that matters: dc+dr must be at least 5. The furniture covers
    // tiles c..c+1 by r..r+1, but its DRAWN corner reaches grid (c+2, r+2),
    // which is depth c+r+4. Standing shallower than that put the figure ON
    // the front edge or behind it. The hand-picked SEATS tables did exactly
    // that, which is why people kept rendering inside the desks.
    // All candidates sit on the c+r=5 diagonal, spread along the front edge.
    var SEAT_CANDIDATES = [[1, 2], [1, 3], [2, 2], [1, 4], [2, 3], [0, 3]];

    function seatTileFor(spot, idx) {
      var n = SEAT_CANDIDATES.length;
      for (var round = 0; round < 5; round++) {
        for (var i = 0; i < n; i++) {
          var o = SEAT_CANDIDATES[(idx + i + round * 2) % n];
          var t = { c: spot.c + o[0] + round, r: spot.r + o[1] + round };
          if (walkable(t.c, t.r)) return t;
        }
      }
      return seatTile(spot);
    }

    // 8-way A*. No cutting corners: a diagonal step needs both orthogonal
    // neighbours free, otherwise figures clip the corners of the desks.
    var DIRS = [[1,0],[-1,0],[0,1],[0,-1],[1,1],[1,-1],[-1,1],[-1,-1]];
    function findPath(from, to) {
      var goal = seatTile(to);
      var sk = from.c + ',' + from.r, gk = goal.c + ',' + goal.r;
      if (sk === gk) return [{ c: from.c, r: from.r }, { c: goal.c, r: goal.r }];
      var open = [{ c: from.c, r: from.r, f: Math.abs(from.c - goal.c) + Math.abs(from.r - goal.r) }];
      var came = Object.create(null), best = Object.create(null);
      best[sk] = 0;
      var closed = Object.create(null);
      while (open.length) {
        open.sort(function(a, b) { return a.f - b.f; });
        var cur = open.shift();
        var ck = cur.c + ',' + cur.r;
        if (closed[ck]) continue;
        if (ck === gk) break;
        closed[ck] = 1;
        for (var d = 0; d < DIRS.length; d++) {
          var nc = cur.c + DIRS[d][0], nr = cur.r + DIRS[d][1];
          var nk = nc + ',' + nr;
          if (!walkable(nc, nr) || closed[nk]) continue;
          if (DIRS[d][0] && DIRS[d][1] && (!walkable(cur.c + DIRS[d][0], cur.r) || !walkable(cur.c, cur.r + DIRS[d][1]))) continue;
          var cost = DIRS[d][0] && DIRS[d][1] ? 1.414 : 1;
          var ng = best[ck] + cost;
          if (best[nk] != null && ng >= best[nk]) continue;
          best[nk] = ng;
          came[nk] = ck;
          open.push({ c: nc, r: nr, f: ng + Math.abs(nc - goal.c) + Math.abs(nr - goal.r) });
        }
      }
      if (!came[gk] && sk !== gk) return null;
      var path = [], k = gk;
      while (k) { path.push({ c: +k.split(',')[0], r: +k.split(',')[1] }); k = came[k]; }
      path.reverse();
      path.push(goal);
      if (to.c !== goal.c || to.r !== goal.r) path.push({ c: to.c, r: to.r });
      return path;
    }

    // A flat panel standing upright along the grid edge from (c0,r0) to (c1,r0),
    // between two heights. This is what a monitor or a door frame is: the
    // grid line lifted vertically, so it leans the same way as the floor
    // instead of hanging as an unrotated rectangle.
    function isoPanel(c0, r0, c1, r1, lo, hi, cls) {
      var A = [isoX(c0, r0), isoY(c0, r0)];
      var B = [isoX(c1, r1), isoY(c1, r1)];
      function P(p, up) { return p[0] + ',' + (p[1] - up); }
      return '<polygon class="' + cls + '" points="' +
        P(A, hi) + ' ' + P(B, hi) + ' ' + P(B, lo) + ' ' + P(A, lo) + '"/>';
    }

    // An isometric cuboid occupying tiles (c0,r0) to (c1,r1), raised by h
    // pixels. Three faces: the rhombus on top and the two sides that face the
    // viewer, which in this projection are the +c edge and the +r edge.
    function isoBox(c0, r0, c1, r1, h, cls) {
      var A = [isoX(c0, r0), isoY(c0, r0)];
      var B = [isoX(c1, r0), isoY(c1, r0)];
      var C = [isoX(c1, r1), isoY(c1, r1)];
      var D = [isoX(c0, r1), isoY(c0, r1)];
      function P(p, up) { return p[0] + ',' + (p[1] - up); }
      return '<g class="iso ' + cls + '">' +
        '<polygon class="fx-top" points="' + P(A, h) + ' ' + P(B, h) + ' ' + P(C, h) + ' ' + P(D, h) + '"/>' +
        '<polygon class="fx-left" points="' + P(D, h) + ' ' + P(C, h) + ' ' + P(C, 0) + ' ' + P(D, 0) + '"/>' +
        '<polygon class="fx-right" points="' + P(B, h) + ' ' + P(C, h) + ' ' + P(C, 0) + ' ' + P(B, 0) + '"/>' +
      '</g>';
    }

    // The floor: one rhombus with tile lines, drawn in the same projection as
    // everything standing on it.
    function isoFloorSVG() {
      var out = '<polygon class="iso-floor-face" points="' +
        isoX(0, 0) + ',' + isoY(0, 0) + ' ' +
        isoX(GRID, 0) + ',' + isoY(GRID, 0) + ' ' +
        isoX(GRID, GRID) + ',' + isoY(GRID, GRID) + ' ' +
        isoX(0, GRID) + ',' + isoY(0, GRID) + '"/>';
      for (var i = 0; i <= GRID; i++) {
        out += '<line class="iso-grid" x1="' + isoX(i, 0) + '" y1="' + isoY(i, 0) + '" x2="' + isoX(i, GRID) + '" y2="' + isoY(i, GRID) + '"/>';
        out += '<line class="iso-grid" x1="' + isoX(0, i) + '" y1="' + isoY(0, i) + '" x2="' + isoX(GRID, i) + '" y2="' + isoY(GRID, i) + '"/>';
      }
      return out;
    }
    // A wall standing upright on the grid edge (c0,r0)-(c1,r1). No top face:
    // a room is an OPEN box, which is the whole point of drawing it
    // isometrically. You see in over the near wall.
    function isoWallH(c0, r0, c1, r1, h, cls) {
      var A = [isoX(c0, r0), isoY(c0, r0)];
      var B = [isoX(c1, r1), isoY(c1, r1)];
      return '<polygon class="' + cls + '" points="' +
        A[0] + ',' + (A[1] - h) + ' ' + B[0] + ',' + (B[1] - h) + ' ' +
        B[0] + ',' + B[1] + ' ' + A[0] + ',' + A[1] + '"/>';
    }
    // The thickness of a wall, seen from above.
    function isoWallTop(c0, r0, c1, r1, h, t, cls) {
      var A = [isoX(c0, r0), isoY(c0, r0)];
      var B = [isoX(c1, r1), isoY(c1, r1)];
      var A2 = [isoX(c0, r0 + t), isoY(c0, r0 + t)];
      var B2 = [isoX(c1, r1 + t), isoY(c1, r1 + t)];
      return '<polygon class="' + cls + '" points="' +
        A[0] + ',' + (A[1] - h) + ' ' + B[0] + ',' + (B[1] - h) + ' ' +
        B2[0] + ',' + (B2[1] - h) + ' ' + A2[0] + ',' + (A2[1] - h) + '"/>';
    }
    // A door standing in a wall: the leaf plus a handle, drawn on the grid
    // edge like any other panel.
    function isoDoorway(c, r, cls) {
      var x = isoX(c, r), y = isoY(c, r);
      return isoPanel(c, r, c, r + 1, 0, 38, cls) +
        '<circle class="door-knob" cx="' + (x + 9) + '" cy="' + (y - 19) + '" r="1.8"/>';
    }
    // A round table: an ellipse for the top, a curved side down to the floor,
    // and an ellipse at the base.
    function isoRoundTable(c, r, rx, ry, h, cls) {
      var x = isoX(c, r), y = isoY(c, r);
      return '<ellipse class="' + cls + '" cx="' + x + '" cy="' + (y - h) + '" rx="' + rx + '" ry="' + ry + '"/>' +
        '<path class="' + cls + '-side" d="M' + (x - rx) + ' ' + (y - h) +
        ' A ' + rx + ' ' + ry + ' 0 0 0 ' + (x + rx) + ' ' + (y - h) +
        ' L ' + (x + rx) + ' ' + y +
        ' A ' + rx + ' ' + ry + ' 0 0 1 ' + (x - rx) + ' ' + y + ' Z"/>' +
        '<ellipse class="' + cls + '-side" cx="' + x + '" cy="' + y + '" rx="' + rx + '" ry="' + ry + '"/>';
    }
    function isoStool(c, r, cls) {
      var x = isoX(c, r), y = isoY(c, r);
      return '<path class="' + cls + '-stem" d="M' + x + ' ' + (y - 12) + ' L' + x + ' ' + y + '"/>' +
        '<ellipse class="' + cls + '-foot" cx="' + x + '" cy="' + y + '" rx="7" ry="3.5"/>' +
        '<ellipse class="' + cls + '" cx="' + x + '" cy="' + (y - 13) + '" rx="6.5" ry="3.5"/>';
    }
    // The broom that gives the closet its name.
    function isoBroom(c, r) {
      var x = isoX(c, r), y = isoY(c, r);
      return '<path class="broom-stick" d="M' + (x + 2) + ' ' + (y - 4) + ' L' + (x + 12) + ' ' + (y - 30) + '"/>' +
        '<path class="broom-head" d="M' + (x - 4) + ' ' + (y - 3) + ' L' + (x + 6) + ' ' + (y - 3) +
        ' L' + (x + 4) + ' ' + (y + 5) + ' L' + (x - 2) + ' ' + (y + 5) + ' Z"/>';
    }

    // Depth order: in this projection the tiles closest to the viewer are the

    // Furniture is built from cuboids, walls and discs, so it shares the
    // floor's projection and needs no separate sprite sheet.
    function isoPlace(kind, c, r) {
      var x = isoX(c, r), y = isoY(c, r);
      var F = FOOTPRINT[kind] || [2, 2];

      if (kind === 'island') {
        // Desk surface, monitor standing at the back edge, chair on the near
        // edge. The monitor is an isoPanel so it leans with the floor instead
        // of hanging there as a flat black rectangle.
        var s = isoBox(c, r, c + F[0], r + F[1], 15, 'desk');
        s += isoPanel(c, r, c + F[0], r, 15, 40, 'screen');
        s += isoPanel(c + 0.4, r, c + F[0] - 0.4, r, 18, 36, 'screen-glow');
        s += isoBox(c + 0.6, r + F[1] - 0.7, c + 1.4, r + F[1] - 0.1, 11, 'chair');
        return s;
      }

      if (kind === 'meeting') {
        // Three walls with a doorway in the near one, drawn without a top
        // face so you can see the table inside.
        var h = 46, t = 0.22;
        var o = '';
        o += isoWallTop(c, r, c + F[0], r, h, t, 'wall-top') + isoWallH(c, r, c + F[0], r, h, 'wall');
        o += isoWallTop(c, r, c, r + F[1], h, t, 'wall-top') + isoWallH(c, r, c, r + F[1], h, 'wall');
        var gap = c + 1;
        o += isoWallTop(c, r + F[1], gap, r + F[1], h, t, 'wall-top') + isoWallH(c, r + F[1], gap, r + F[1], h, 'wall');
        o += isoWallTop(gap + 1, r + F[1], c + F[0], r + F[1], h, t, 'wall-top') + isoWallH(gap + 1, r + F[1], c + F[0], r + F[1], h, 'wall');
        o += isoDoorway(gap, r + F[1], 'door');
        var tc = c + F[0] / 2, tr = r + F[1] / 2;
        o += isoRoundTable(tc, tr, 15, 7.5, 15, 'mtable');
        o += isoStool(tc - 0.8, tr - 0.7, 'mstool') + isoStool(tc + 0.8, tr - 0.7, 'mstool');
        o += isoStool(tc, tr + 0.8, 'mstool');
        return o;
      }

      if (kind === 'closet') {
        // Three walls, open to the front, with a broom inside. Figures that
        // have not been touched for a long time stand in here.
        var ch = 40;
        var co = isoWallTop(c, r, c + F[0], r, ch, 0.2, 'wall-top') + isoWallH(c, r, c + F[0], r, ch, 'wall');
        co += isoWallTop(c, r, c, r + F[1], ch, 0.2, 'wall-top') + isoWallH(c, r, c, r + F[1], ch, 'wall');
        co += isoWallTop(c + F[0], r, c + F[0], r + F[1], ch, 0.2, 'wall-top') + isoWallH(c + F[0], r, c + F[0], r + F[1], ch, 'wall');
        co += isoBroom(c + 0.6, r + F[1] - 0.4);
        return co;
      }

      if (kind === 'shelves') {
        // Two tall units side by side with three open shelves each.
        var o2 = '';
        for (var u = 0; u < 2; u++) {
          var uc = c + u * 0.95;
          o2 += isoBox(uc, r, uc + 0.8, r + F[1], 54, 'shelf');
          for (var sh = 1; sh <= 3; sh++) {
            var sa = isoX(uc, r), sb = isoY(uc, r) - sh * 13;
            var sc2 = isoX(uc + 0.8, r), sd = isoY(uc + 0.8, r) - sh * 13;
            o2 += '<path class="shelf-gap" d="M' + sa + ' ' + sb + ' L' + sc2 + ' ' + sd + '"/>';
          }
        }
        return o2;
      }

      if (kind === 'coffee') {
        // Espresso machine on a counter.
        var m = isoBox(c + 0.1, r + F[1] - 0.9, c + F[0] - 0.1, r + F[1], 17, 'counter');
        m += isoBox(c + 0.35, r + F[1] - 0.85, c + 0.95, r + F[1] - 0.3, 33, 'machine');
        m += isoBox(c + 1.1, r + F[1] - 0.8, c + 1.4, r + F[1] - 0.3, 27, 'machine');
        m += '<circle class="machine-light" cx="' + (x + 16) + '" cy="' + (y + 6 - 26) + '" r="2.6"/>';
        return m;
      }

      if (kind === 'darts') {
        var d = isoPanel(c + 0.2, r + F[1], c + 1.4, r + F[1], 26, 58, 'board');
        d += isoBox(c + 0.5, r + F[1] - 0.7, c + 1.1, r + F[1] - 0.1, 44, 'board-inner');
        d += isoBox(c + 0.1, r + 0.1, c + F[0] - 0.1, r + 0.7, 13, 'cabinet');
        return d;
      }

      if (kind === 'sofaA' || kind === 'sofaB') {
        var f = isoBox(c + 0.1, r + 0.4, c + F[0] - 0.1, r + F[1] - 0.1, 13, 'sofa');
        f += isoBox(c + 0.1, r + 0.1, c + F[0] - 0.1, r + 0.55, 26, 'sofa-back');
        f += isoBox(c + 0.05, r + 0.4, c + 0.35, r + F[1] - 0.1, 19, 'sofa-arm');
        f += isoBox(c + F[0] - 0.35, r + 0.4, c + F[0] - 0.05, r + F[1] - 0.1, 19, 'sofa-arm');
        return f;
      }

      if (kind === 'table') {
        // Low table with a stack of books and a plant.
        var tb = isoBox(c + 0.35, r + 0.5, c + F[0] - 0.35, r + F[1] - 0.5, 12, 'ctable');
        tb += isoBox(c + 0.55, r + 0.85, c + 1.0, r + 1.25, 18, 'books');
        tb += '<circle class="plant" cx="' + (x + 22) + '" cy="' + (y + 4 - 17) + '" r="5"/>';
        return tb;
      }

      if (kind === 'toilet') {
        return isoBox(c + 0.45, r + 0.7, c + 1.55, r + 1.8, 15, 'wc') +
          isoBox(c + 0.3, r + 0.2, c + 1.7, r + 0.75, 30, 'wc-tank');
      }

      if (kind === 'sulk') {
        return isoBox(c + 0.3, r + 0.4, c + 1.4, r + 1.3, 14, 'stool') +
          isoBox(c + 0.3, r + 0.4, c + 1.4, r + 0.8, 30, 'stool-back');
      }

      if (kind === 'door') {
        return isoDoorway(c, r, 'door') + isoBox(c - 0.15, r, c + 0.15, r + 1, 46, 'door-frame');
      }

      return '';
    }
    // ones with the largest c+r, so that sum is the z-index.
    function depthOf(c, r) { return Math.round(c + r) * 10; }

    // ---- Figures -----------------------------------------------------

    function hair() {
      return '<path class="hair" d="M9.6 13 Q9.6 5 18 5 Q26.4 5 26.4 13 Q23.4 9.5 18 9.5 Q12.6 9.5 9.6 13 Z"/>';
    }

    // Head with an expression that carries the activity, so a figure can be
    // read without its bubble.
    function head(act) {
      var eyes, mouth, brows;
      if (act === 'error') {
        brows = '<path class="brow-angry" d="M12.6 14.4 L16.4 15.8 M23.4 14.4 L19.6 15.8"/>';
        eyes = '<circle class="eye" cx="15" cy="17.8" r="1.15"/><circle class="eye" cx="21" cy="17.8" r="1.15"/>';
        mouth = '<path class="mouth frown" d="M15 23.4 Q18 20.6 21 23.4"/>';
      } else if (act === 'sulk') {
        brows = '<path class="brow" d="M12.6 15.4 L16.4 15.8 M23.4 15.4 L19.6 15.8"/>';
        eyes = '<path class="eye-closed" d="M13.4 17.8 L16.6 17.8 M19.4 17.8 L22.6 17.8"/>';
        mouth = '<path class="mouth flat" d="M15.4 22.4 L20.6 22.4"/>';
      } else if (act === 'blocked') {
        brows = '<path class="brow" d="M12.6 14.6 L16.4 15 M23.4 14.6 L19.4 15"/>';
        eyes = '<circle class="eye" cx="15" cy="17.6" r="1.2"/><circle class="eye" cx="21" cy="17.6" r="1.2"/>';
        mouth = '<path class="mouth" d="M15.4 22.6 L20.6 22.6"/>';
      } else if (act === 'idle') {
        brows = '<path class="brow" d="M12.6 14.8 L16.4 15.2 M23.4 14.8 L19.6 15.2"/>';
        eyes = '<circle class="eye" cx="15" cy="17.6" r="1.05"/><circle class="eye" cx="21" cy="17.6" r="1.05"/>';
        mouth = '<path class="mouth" d="M15.4 22 Q18 23.8 20.6 22"/>';
      } else {
        brows = '<path class="brow" d="M12.6 14.6 L16.4 15 M23.4 14.6 L19.6 15"/>';
        eyes = '<circle class="eye" cx="15" cy="17.6" r="1.05"/><circle class="eye" cx="21" cy="17.6" r="1.05"/>';
        mouth = '<path class="mouth" d="M15.4 22.2 Q18 21.2 20.6 22.2"/>';
      }
      return '<circle class="head" cx="18" cy="17" r="7.4"/>' +
        '<ellipse class="ear" cx="10.7" cy="18" rx="1.3" ry="2"/>' +
        '<ellipse class="ear" cx="25.3" cy="18" rx="1.3" ry="2"/>' +
        brows + eyes +
        '<path class="nose" d="M18 18.2 L17.3 20.4 L19 20.4"/>' +
        mouth;
    }

    // Torso, head and hair are shared by every pose; only the limbs differ.
    function bodyCore(act, lean) {
      return '<path class="shirt" d="M12 25 L24 25 L25.5 41 L10.5 41 Z"/>' +
        '<path class="collar" d="M15.6 25 L18 29 L20.4 25 Z"/>' +
        '<path class="placket" d="M18 29 L18 41"/>' +
        hair() + head(act);
    }

    function poseStand(act, swing) {
      var s = swing ? -1 : 1;
      return '<ellipse class="ground-shadow" cx="18" cy="57" rx="10" ry="3"/>' +
        '<path class="leg" d="M14.5 40 L' + (15.5 + s * 2) + ' 50"/>' +
        '<path class="leg" d="M21.5 40 L' + (20.5 - s * 2) + ' 50"/>' +
        '<ellipse class="shoe" cx="' + (16.5 + s * 2) + '" cy="51.4" rx="3.3" ry="2"/>' +
        '<ellipse class="shoe" cx="' + (19.5 - s * 2) + '" cy="51.4" rx="3.3" ry="2"/>' +
        '<path class="arm" d="M12.5 27 Q' + (10 - s * 2) + ' 32 ' + (11 - s * 3) + ' 37"/>' +
        '<path class="arm" d="M23.5 27 Q' + (26 + s * 2) + ' 32 ' + (25 + s * 3) + ' 37"/>' +
        '<circle class="hand" cx="' + (10.5 - s * 3) + '" cy="38" r="2"/>' +
        '<circle class="hand" cx="' + (25.5 + s * 3) + '" cy="38" r="2"/>' +
        bodyCore(act, 0);
    }

    function poseSit(act) {
      // Facing the screen when at a desk, arms forward onto the keyboard.
      var desk = act === 'working' || act === 'blocked';
      var lA = desk ? 'M14.5 40 L12 46 L12 49' : 'M14.5 40 L12 46 L12 49';
      var aL = desk ? 'M12.5 27 Q9 31 8 35' : 'M12.5 27 Q8 31 7 36';
      var aR = desk ? 'M23.5 27 Q27 31 28 35' : 'M23.5 27 Q28 31 29 36';
      return '<ellipse class="ground-shadow" cx="18" cy="49" rx="11" ry="3"/>' +
        '<path class="leg" d="' + lA + '"/>' +
        '<path class="leg" d="M21.5 40 L24 46 L24 49"/>' +
        '<ellipse class="shoe" cx="11" cy="50" rx="3.2" ry="2"/>' +
        '<ellipse class="shoe" cx="25" cy="50" rx="3.2" ry="2"/>' +
        '<path class="arm" d="' + aL + '"/>' +
        '<path class="arm" d="' + aR + '"/>' +
        '<circle class="hand" cx="8" cy="36" r="2"/>' +
        '<circle class="hand" cx="28" cy="36" r="2"/>' +
        bodyCore(act, 0);
    }

    // ---- Seated gestures -------------------------------------------
    // One pose, not two. Swapping two frames from the cycle keyframes cost
    // 40 KB of CSS per gesturing figure; instead only the pose's VISIBILITY is
    // baked into the cycle (three stops), and the arm motion is a short
    // looping transform shared by every figure.
    function seatedLegs() {
      return '<path class="leg" d="M14.5 40 L12 46 L12 49"/>' +
        '<path class="leg" d="M21.5 40 L24 46 L24 49"/>' +
        '<ellipse class="shoe" cx="11" cy="50" rx="3.2" ry="2"/>' +
        '<ellipse class="shoe" cx="25" cy="50" rx="3.2" ry="2"/>';
    }

    function poseGesture(act, gesture) {
      var flail = gesture === 'flail';
      // Typing: hands low over the keyboard, arms nearly straight down.
      // Flailing: arms already raised, so the CSS rotation only has to swing
      // them through a wide arc from there.
      var aL = flail ? 'M12.5 27 Q7 20 9 14' : 'M12.5 27 Q9.5 30 11 32';
      var aR = flail ? 'M23.5 27 Q29 20 27 14' : 'M23.5 27 Q26.5 30 25 32';
      var hL = flail ? [9, 12] : [11, 33];
      var hR = flail ? [27, 12] : [25, 33];
      var r = flail ? 2.2 : 2;
      return '<ellipse class="ground-shadow" cx="18" cy="49" rx="11" ry="3"/>' +
        seatedLegs() +
        // Arm and hand share a group, so the CSS rotation carries both.
        '<g class="garm garm-l">' +
          '<path class="arm" d="' + aL + '"/>' +
          '<circle class="hand" cx="' + hL[0] + '" cy="' + hL[1] + '" r="' + r + '"/>' +
        '</g>' +
        '<g class="garm garm-r">' +
          '<path class="arm" d="' + aR + '"/>' +
          '<circle class="hand" cx="' + hR[0] + '" cy="' + hR[1] + '" r="' + r + '"/>' +
        '</g>' +
        bodyCore(act, 0);
    }

    // ---- Deterministic placement and phase --------------------------
    // The page rewrites the grid every second, which restarts any running CSS
    // animation at frame 0. Both the phase AND the spot are therefore derived
    // from the session id: the same session always resumes at the same point
    // in the same loop and heads for the same place. Deriving the spot from
    // the array index instead made figures teleport whenever a session came
    // or went and the list shifted.
    function idHash(id) {
      var h = 0x811c9dc5;
      for (var i = 0; i < id.length; i++) {
        h ^= id.charCodeAt(i);
        h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
        h = h ^ (h >>> 13);
      }
      return h >>> 0;
    }
    // Where in its cycle a figure should resume. The grid is rewritten every
    // second, which restarts the CSS animation from zero, so a FIXED negative
    // delay froze every figure at the same point forever - it never advanced
    // past 75% of the trip and just appeared to hop forward and back. Taking
    // the delay from the wall clock makes every rebuild resume at the correct
    // point; the per-id jitter keeps figures out of lockstep.
    function phaseOf(id, cycle) {
      var jitter = (idHash(id) % 900) / 1000;
      var at = (Date.now() / 1000 + jitter) % cycle;
      return '-' + at.toFixed(3) + 's';
    }

    // A figure stands slightly to the side of its spot so two on the same
    // island or sofa do not occupy the same pixel. Derived from the id ALONE:
    // using the array index made figures jump whenever a session came or went.
    function seatOffset(id) {
      return ((idHash(id + ':seat') % 5) - 2) * 7;
    }

    // ---- Debug overlay (CTRL+D) ---------------------------------------
    // CTRL+D toggles it; then clicking a figure opens a panel with that
    // figure's state, its full timeline and how long is left of each leg.
    var debugOn = false;
    var debugSel = null;
    var dbg = window.__officeDbg || (window.__officeDbg = Object.create(null));

    function debugPanel() {
      var el = document.getElementById('office-debug');
      if (!el) {
        el = document.createElement('div');
        el.id = 'office-debug';
        el.className = 'office-debug';
        document.body.appendChild(el);
      }
      return el;
    }

    function fmtSec(s) {
      s = Math.max(0, Math.round(s));
      return Math.floor(s / 60) + 'm ' + String(s % 60).padStart(2, '0') + 's';
    }

    // Live view of the selected figure, refreshed with the grid. The panel is
    // created on first use - it used to be created by debugPanel(), which
    // nothing called, so clicking a figure silently did nothing at all.
    function renderDebug() {
      if (!debugOn) {
        var old = document.getElementById('office-debug');
        if (old) { old.style.display = 'none'; old.innerHTML = ''; }
        return;
      }
      var el = debugPanel();
      el.style.display = 'block';
      var d = dbg[debugSel];
      if (!d) { el.innerHTML = '<div class="dbg-head">DEBUG</div><div class="dbg-none">Ingen figur valgt. Klik paa en.</div>'; return; }
      var now = (Date.now() / 1000) % d.cycle;
      var at = 0, cur = 0, left = 0;
      for (var i = 0; i < d.legs.length; i++) {
        var s = d.legs[i].secs;
        if (now < at + s) { cur = i; left = at + s - now; break; }
        at += s;
      }
      var rows = d.legs.map(function(l, i) {
        var cls = i === cur ? ' dbg-cur' : '';
        return '<tr class="' + cls + '"><td>' + esc(l.label) + '</td><td>' + fmtSec(l.secs) + '</td></tr>';
      }).join('');
      el.innerHTML =
        '<div class="dbg-head">DEBUG <span>CTRL+D for at lukke</span></div>' +
        '<div class="dbg-title">' + esc(d.title) + '</div>' +
        '<div class="dbg-state">' + esc(d.state) + '</div>' +
        '<table class="dbg-tbl">' +
          '<tr><th>state</th><th>varighed</th></tr>' + rows +
        '</table>' +
        '<div class="dbg-now">Nu: <b>' + esc(d.state) + '</b> &middot; ' + fmtSec(left) + ' til naeste</div>' +
        '<div class="dbg-grid">' +
          '<span>session</span><code>' + esc(d.id) + '</code>' +
          '<span>cyklus</span><code>' + fmtSec(d.cycle) + '</code>' +
          '<span>flis</span><code>' + d.tile + '</code>' +
          '<span>z-index</span><code>' + d.z + '</code>' +
          '<span>position</span><code>' + d.x + ', ' + d.y + '</code>' +
          '<span>sti</span><code>' + d.pathLen + ' flis</code>' +
          '<span>keyframe</span><code>' + esc(d.anim) + '</code>' +
        '</div>';
    }

    function installDebug() {
      // Ctrl+D is a reserved browser shortcut for "bookmark this page", and
      // not every browser hands it to the page at all - hence the visible
      // toggle in the office header as the reliable way in.
      window.addEventListener('keydown', function(e) {
        if (!(e.ctrlKey || e.metaKey)) return;
        if (String(e.key || '').toLowerCase() !== 'd' && e.code !== 'KeyD') return;
        e.preventDefault();
        e.stopPropagation();
        setDebug(!debugOn);
      }, true);

      document.addEventListener('click', function(e) {
        var t = e.target;
        if (!t || !t.closest) return;
        // The button works whether or not the keyboard shortcut arrived.
        if (t.closest('.dbg-toggle')) {
          e.preventDefault();
          e.stopPropagation();
          setDebug(!debugOn);
          return;
        }
        if (!debugOn) return;
        var w = t.closest('.walker');
        if (!w) return;
        e.preventDefault();
        e.stopPropagation();
        debugSel = w.getAttribute('data-session-id');
        renderDebug();
      });
    }

    function setDebug(on) {
      debugOn = !!on;
      if (!debugOn) debugSel = null;
      // Immediate feedback on the button that was clicked. The next render
      // writes the same state into the fresh markup, so they agree.
      var btn = document.querySelector('.dbg-toggle');
      if (btn) {
        btn.className = 'dbg-toggle' + (debugOn ? ' on' : '');
        btn.textContent = debugOn ? 'Debug ON' : 'Debug';
        btn.setAttribute('aria-pressed', debugOn ? 'true' : 'false');
      }
      renderDebug();
    }

    // ---- Pan and zoom -------------------------------------------------
    // The office is rebuilt every second, so zoom and pan live in variables
    // and are written into the markup as an inline transform. Setting them on
    // the element instead would reset the view on every rebuild.
    var VIEW_Z = 1, VIEW_X = 0, VIEW_Y = 0;
    var ZOOM_MIN = 0.45, ZOOM_MAX = 2.8;

    function viewCss() {
      return 'transform:translate(' + VIEW_X.toFixed(1) + 'px,' + VIEW_Y.toFixed(1) + 'px) scale(' + VIEW_Z.toFixed(3) + ')';
    }
    function saveView() {
      // Writing localStorage is a synchronous disk hit. Doing it on every wheel
      // tick or every mousemove is a large part of why panning used to stutter,
      // so the write is coalesced to one per frame boundary.
      if (saveQueued) return;
      saveQueued = true;
      setTimeout(function() { saveQueued = false; saveNow(); }, 400);
    }
    var saveQueued = false;
    function saveNow() {
      try { localStorage.setItem('dashboardView', JSON.stringify({ z: VIEW_Z, x: VIEW_X, y: VIEW_Y })); } catch (e) {}
    }
    function loadView() {
      try {
        var v = JSON.parse(localStorage.getItem('dashboardView') || 'null');
        if (v && typeof v.z === 'number' && isFinite(v.z)) {
          VIEW_Z = Math.max(ZOOM_MIN, Math.min(ZOOM_MAX, v.z));
          VIEW_X = +v.x || 0;
          VIEW_Y = +v.y || 0;
        }
      } catch (e) {}
    }

    // The viewport is replaced on every rebuild, so the cached node is checked
    // for being detached before it is reused instead of re-querying the DOM on
    // every pointer move.
    var viewVp = null, viewStage = null, lastTransform = '';
    function stageNode() {
      if (viewStage && viewStage.parentNode) return viewStage;
      viewVp = document.querySelector('.office-viewport');
      viewStage = viewVp ? viewVp.querySelector('.office-stage') : null;
      return viewStage;
    }

    // mousemove fires faster than the display refreshes. Painting straight from
    // it means several layout passes per frame, so requests are coalesced into
    // one per animation frame.
    var paintQueued = false;
    function queueView() {
      if (paintQueued) return;
      paintQueued = true;
      requestAnimationFrame(function() {
        paintQueued = false;
        var st = stageNode();
        if (!st) return;
        var t = viewCss();
        if (t !== lastTransform) { lastTransform = t; st.style.transform = t; }
      });
    }

    function setZoom(next, cx, cy) {
      next = Math.max(ZOOM_MIN, Math.min(ZOOM_MAX, next));
      if (next === VIEW_Z) return;
      // Keep the point under the cursor where it is. The transform scales about
      // the centre, so cx/cy are offsets from the viewport centre.
      VIEW_X = cx - (cx - VIEW_X) * (next / VIEW_Z);
      VIEW_Y = cy - (cy - VIEW_Y) * (next / VIEW_Z);
      VIEW_Z = next;
      queueView();
      saveView();
    }
    function applyView() {
      var st = stageNode();
      if (!st) return;
      lastTransform = viewCss();
      st.style.transform = lastTransform;
    }

    // While the camera is moving, the 23 figures freeze. Their animations
    // rewrite left, top, z-index and opacity every frame, and repainting that
    // under a moving transform is most of the cost of a pan.
    var idleTimer = null;
    function markInteracting(vp) {
      vp.classList.add('interacting');
      if (idleTimer) clearTimeout(idleTimer);
      idleTimer = setTimeout(function() {
        idleTimer = null;
        if (viewVp) viewVp.classList.remove('interacting');
      }, 260);
    }

    // Bound to the document, not to the viewport element: the viewport is
    // replaced on every rebuild and would drop its listeners.
    function installPanZoom() {
      document.addEventListener('wheel', function(e) {
        var vp = e.target && e.target.closest ? e.target.closest('.office-viewport') : null;
        if (!vp) return;
        e.preventDefault();
        var r = vp.getBoundingClientRect();
        var cx = e.clientX - r.left - r.width / 2;
        var cy = e.clientY - r.top - r.height / 2;
        setZoom(VIEW_Z * Math.pow(1.0018, -e.deltaY), cx, cy);
        markInteracting(vp);
      }, { passive: false });

      // Right click and drag pans. Left click is left alone so the figures and
      // the cards keep working.
      var drag = null;
      document.addEventListener('mousedown', function(e) {
        if (e.button !== 2) return;
        var vp = e.target && e.target.closest ? e.target.closest('.office-viewport') : null;
        if (!vp) return;
        e.preventDefault();
        drag = { x: e.clientX, y: e.clientY, px: VIEW_X, py: VIEW_Y };
        vp.classList.add('panning', 'interacting');
      });
      document.addEventListener('mousemove', function(e) {
        if (!drag) return;
        e.preventDefault();
        VIEW_X = drag.px + (e.clientX - drag.x);
        VIEW_Y = drag.py + (e.clientY - drag.y);
        queueView();
      });
      document.addEventListener('mouseup', function(e) {
        if (!drag) return;
        if (viewVp) {
          viewVp.classList.remove('panning');
          markInteracting(viewVp);
        }
        drag = null;
        saveView();
      });
      // The office view has no other use for a right click.
      document.addEventListener('contextmenu', function(e) {
        var vp = e.target && e.target.closest ? e.target.closest('.office-viewport') : null;
        if (vp) e.preventDefault();
      });
      // Double click resets, which is the only way back if you zoom too far.
      document.addEventListener('dblclick', function(e) {
        var vp = e.target && e.target.closest ? e.target.closest('.office-viewport') : null;
        if (!vp) return;
        VIEW_Z = 1; VIEW_X = 0; VIEW_Y = 0;
        applyView();
        saveView();
      });
    }

    // ---- Four zones ---------------------------------------------------
    // The furniture has been taken out and the floor divided into four equal
    // quarters. A session belongs to exactly one of them, chosen from its
    // status, and wanders inside it.
    var MID = GRID / 2;
    var ZONES = [
      { key: 'green',  act: 'working', label: 'WORKING_IN_GREEN_ZONE',  pause: [40, 70],  gesture: 'type' },
      { key: 'orange', act: 'blocked', label: 'QUESTION_IN_ORANGE_ZONE', pause: [20, 45], gesture: null },
      { key: 'red',    act: 'error',   label: 'ERROR_IN_RED_ZONE',     pause: [15, 35],  gesture: 'flail' },
      { key: 'grey',   act: 'idle',    label: 'IDLE_IN_GREY_ZONE',      pause: [25, 60],  gesture: null },
    ];
    // Each quarter of the floor, in grid coordinates. c0/r0 is the far corner.
    var QUAD = [
      { c0: 0, c1: MID, r0: 0, r1: MID },        // green  - far corner
      { c0: 0, c1: MID, r0: MID, r1: GRID },      // orange - left corner
      { c0: MID, c1: GRID, r0: MID, r1: GRID },   // red    - near corner
      { c0: MID, c1: GRID, r0: 0, r1: MID },      // grey   - right corner
    ];

    // Which quarter a session belongs in. Interrupted counts as red: it is not
    // idle, it is stuck, and grey is for sessions nobody is waiting on.
    function zoneOf(c) {
      var t = c.status && c.status.type;
      if (t === 'user_response' || t === 'asking_parent') return 1;
      if (t === 'failed' || t === 'retrying' || t === 'interrupted') return 2;
      if (t === 'running' || t === 'compacting') return 0;
      return 3;
    }

    // The quadrants a figure is allowed to stand in: its quarter, inset by a
    // tile so nobody ends up on the dividing line.
    function zoneFloor(zi) {
      var q = QUAD[zi];
      return { c0: q.c0 + 1, c1: q.c1 - 1, r0: q.r0 + 1, r1: q.r1 - 1 };
    }

    // The four coloured quarters, drawn as one rhombus each with a label.
    function zoneSVG(counts) {
      return QUAD.map(function(q, i) {
        var pts = isoX(q.c0, q.r0) + ',' + isoY(q.c0, q.r0) + ' ' +
                  isoX(q.c1, q.r0) + ',' + isoY(q.c1, q.r0) + ' ' +
                  isoX(q.c1, q.r1) + ',' + isoY(q.c1, q.r1) + ' ' +
                  isoX(q.c0, q.r1) + ',' + isoY(q.c0, q.r1);
        var mc = (q.c0 + q.c1) / 2, mr = (q.r0 + q.r1) / 2;
        return '<polygon class="zone zone-' + ZONES[i].key + '" points="' + pts + '"/>' +
          '<g class="zone-tag">' +
            '<text x="' + isoX(mc, mr).toFixed(0) + '" y="' + (isoY(mc, mr) + 34).toFixed(0) + '">' +
              ZONES[i].key.toUpperCase() + '</text>' +
            '<text class="zone-n" x="' + isoX(mc, mr).toFixed(0) + '" y="' + (isoY(mc, mr) + 54).toFixed(0) + '">' +
              (counts ? counts[i] : 0) + '</text>' +
          '</g>';
      }).join('');
    }

    // A figure walks between three points inside its own quarter. The points
    // come from the session id, so a session keeps the same spot across
    // rebuilds instead of drifting every second.
    function zoneWaypoints(id, zi) {
      var b = zoneFloor(zi);
      var cw = Math.max(1, b.c1 - b.c0 + 1), rh = Math.max(1, b.r1 - b.r0 + 1);
      var out = [];
      for (var n = 0; n < 3; n++) {
        var h = idHash(id + ':w' + n);
        out.push({ c: b.c0 + (h % cw), r: b.r0 + ((h >>> 9) % rh) });
      }
      return out;
    }

    function buildZoneTimeline(id, zi) {
      var Z = ZONES[zi];
      var wps = zoneWaypoints(id, zi);
      var legs = [];
      var walk = function(i, salt) {
        return { k: 'walk', to: wps[i], secs: secs(id, salt, 10, 20), label: 'WALKING_IN_' + Z.key.toUpperCase() + '_ZONE' };
      };
      var pause = function(i, salt) {
        return { k: 'sit', to: wps[i], secs: secs(id, salt, Z.pause[0], Z.pause[1]),
                 label: Z.label, gesture: Z.gesture };
      };
      // The first leg is a pause, not a walk: there is no door to come in
      // through any more, so a figure starts where it stands and only moves
      // between its own three points.
      legs.push(pause(0, 's0'));
      legs.push(walk(1, 'w1'), pause(1, 's1'));
      legs.push(walk(2, 'w2'), pause(2, 's2'));
      legs.push(walk(0, 'wf'), pause(0, 'sf'));
      return legs;
    }

    // A session untouched for this long is not put away any more - there is no
    // closet. It stands still in the grey quarter, dimmed, so it is visibly out
    // of service rather than idling like a healthy one.
    var CLOSET_MS = 72 * 60 * 60 * 1000;

    function isStale(c) {
      var at = typeof c.lastActivity === 'number' ? c.lastActivity : c.startTime;
      if (typeof at !== 'number') return false;
      return (Date.now() - at) > CLOSET_MS;
    }

    // ---- Named states -------------------------------------------------
    // Every figure is always in exactly one of these, and the current one is
    // written onto the figure so you can read it without hovering.
    var DEST_NAME = {
      door: 'DOOR', sofaA: 'SOFA', sofaB: 'SOFA', coffee: 'ESPRESSO',
      darts: 'DART_BOARD', toilet: 'TOILET', closet: 'BROOM_CLOSET',
      shelves: 'SHELVES', table: 'COFFEE_TABLE',
    };
    function destName(key) {
      var k = String(key || 'door');
      if (k.slice(0, 6) === 'island') return 'DESK';
      return DEST_NAME[k] || 'DOOR';
    }

    // What a session is doing at its desk. A session that needs an answer or
    // that failed was working at that desk, so it belongs there too.
    function deskState(c) {
      var t = c.status && c.status.type;
      if (t === 'user_response' || t === 'asking_parent') return 'QUESTION';
      if (t === 'failed' || t === 'retrying') return 'ERROR';
      return 'WORKING';
    }

    // ---- State timeline ----------------------------------------------
    // Real seconds, not percentages of a 9 second loop. A figure walks, then
    // spends a believable amount of time doing one thing, then moves on. The
    // whole cycle is two to four minutes, which is what makes the office look
    // unhurried instead of frantic.
    var IDLE_STATES = [
      { spot: 'sofa',    secs: [20, 60], label: 'SIT_IN_SOFA' },
      { spot: 'coffee',  secs: [10, 20], label: 'TAKE_A_COFFEE' },
      { spot: 'darts',   secs: [20, 40], label: 'PLAY_DARTS' },
      { spot: 'toilet',  secs: [60, 90], label: 'TAKE_A_SHIT' },
      { spot: 'canteen', secs: [15, 30], label: 'GET_A_SANDWICH' },
    ];
    var WALK_SECS = [10, 20];

    // Deterministic in [a,b], salted per leg so two legs never tie.
    function secs(id, salt, a, b) {
      return a + (idHash(id + ':' + salt) % 1000) / 1000 * (b - a);
    }

    // How long a figure stays at a given spot. Uses the per-activity durations
    // (sitting on the sofa is quick, being in the toilet is not) and falls
    // back to a plain range for anything not in the list.
    function staySecs(id, spot, salt) {
      for (var i = 0; i < IDLE_STATES.length; i++) {
        if (IDLE_STATES[i].spot === spot) return secs(id, salt, IDLE_STATES[i].secs[0], IDLE_STATES[i].secs[1]);
      }
      return secs(id, salt, 15, 45);
    }

    // The loop a single figure runs through. Returns legs in order, each with
    // the spot it is heading for / sitting at, how long it lasts, and the
    // name of the state it is in.
    function buildTimeline(id, mode, spots, label) {
      var legs = [];
      var W = function(salt) { return secs(id, salt, WALK_SECS[0], WALK_SECS[1]); };
      var walk = function(to, salt) { return { k: 'walk', to: to, secs: W(salt), label: 'WALKING_TO_' + destName(to) }; };
      if (mode === 'work') {
        legs.push(walk(spots[0], 'w1'));
        legs.push({ k: 'sit', to: spots[0], secs: secs(id, 's1', 180, 420), label: label + '_AT_DESK' });
        legs.push(walk('door', 'w2'));
        legs.push({ k: 'sit', to: 'door', secs: secs(id, 's2', 10, 20), label: 'WAITING_AT_DOOR' });
        return legs;
      }
      // Idle: visit its main spot, then a different one, then back to the door.
      // Two spots per figure keeps the number of people per seat low enough
      // that nobody has to sit on somebody else.
      legs.push(walk(spots[0], 'wa'));
      legs.push({ k: 'sit', to: spots[0], secs: staySecs(id, spots[0], 'sa'), label: idleLabel(spots[0]) });
      legs.push(walk(spots[1], 'wb'));
      legs.push({ k: 'sit', to: spots[1], secs: staySecs(id, spots[1], 'sb'), label: idleLabel(spots[1]) });
      legs.push(walk('door', 'wc'));
      legs.push({ k: 'sit', to: 'door', secs: secs(id, 'sc', 10, 25), label: 'WAITING_AT_DOOR' });
      return legs;
    }

    function idleLabel(spot) {
      for (var i = 0; i < IDLE_STATES.length; i++) {
        if (IDLE_STATES[i].spot === spot) return IDLE_STATES[i].label;
      }
      return 'IDLE_AT_' + destName(spot);
    }

    // Which state is this figure in right now? The grid is rebuilt every
    // second, so asking the clock once per rebuild is enough to keep the
    // label truthful.
    function stateNow(legs, total, cycle) {
      var pct = ((Date.now() / 1000) % cycle) / cycle * 100;
      var at = 0;
      for (var i = 0; i < legs.length; i++) {
        var span = legs[i].secs / total * 100;
        if (pct < at + span) return legs[i].label || ('IDLE_AT_' + destName(legs[i].to));
        at += span;
      }
      return legs[legs.length - 1].label || 'IDLE';
    }

    // ---- Per-figure animation from a real path ------------------------
    // A CSS animation can only hold keyframes we write out, so each distinct
    // route gets its own generated @keyframes. Rules are APPENDED to one
    // style element and cached by signature: rewriting the element would
    // invalidate every running animation on the page.
    var animCache = window.__officeAnims || (window.__officeAnims = Object.create(null));

    // One registered route: a timeline of legs, each leg a path plus a duration.
    // Turned into four @keyframes rules - position, and the three poses.
    function registerTimeline(id, legs, ptsFor, total) {
      var sig = id + '|' + total.toFixed(1) + '|' + legs.map(function(l) {
        return l.k + l.to + l.secs.toFixed(1);
      }).join(',') + '|' + legs.map(function(l) {
        return ptsFor(l).map(function(p) { return p[0].toFixed(0) + '.' + p[1].toFixed(0); }).join(' ');
      }).join('|');
      var name = 'of' + (idHash(sig) % 1000000);
      if (animCache[sig]) return { base: name, cached: true };

      // Walk windows become the stride poses, sit windows become the sit pose.
      // A sit window can also carry a gesture (typing, flailing); those get
      // their own pairs of poses, and the plain sit pose is suppressed there.
      var posKf = [], aR = [], bR = [], sitR = [];
      var gA = [];                      // gesture window, baked into the cycle
      var gesture = null;
      var at = 0, first = true, firstPt = null, firstZ = 5;

      legs.forEach(function(leg) {
        var span = leg.secs / total * 100;
        var s0 = at, s1 = at + span;
        if (leg.k === 'walk') {
          var pts = ptsFor(leg);
          var zs = leg._tiles.map(zOf);
          var len = pathLength(pts);
          var steps = Math.max(2, Math.min(30, Math.round(len / 30)));
          // Stride length: about 55px per step at walking pace.
          var perLeg = Math.max(2, Math.min(20, Math.round(len / 55)));
          if (first) { firstPt = pts[0]; firstZ = zs[0]; posKf.push(atPct(0, pts[0][0], pts[0][1], zs[0])); first = false; }
          else posKf.push(atPct(s0, pts[0][0], pts[0][1], zs[0]));
          for (var i = 1; i <= steps; i++) {
            var pf = pointOn(pts, (i / steps) * len);
            // pf[2] is the segment it landed on, pf[3] how far along it.
            var seg = pf[2];
            var nz = zs[Math.min(seg + 1, zs.length - 1)];
            posKf.push(atPct(s0 + span * (i / steps), pf[0], pf[1], zs[seg] + (nz - zs[seg]) * pf[3]));
          }
          for (var j = 0; j < perLeg; j++) {
            var q0 = s0 + span * (j / perLeg);
            var q1 = s0 + span * ((j + 1) / perLeg);
            (j % 2 === 0 ? aR : bR).push([q0, q1]);
          }
        } else {
          var pl = ptsFor(leg);
          var pz = zOf(leg._tiles[0]);
          if (first) { firstPt = pl[0]; firstZ = pz; posKf.push(atPct(0, pl[0][0], pl[0][1], pz)); first = false; }
          posKf.push(atPct(s1, pl[0][0], pl[0][1], pz));
          if (leg.gesture) {
            gesture = leg.gesture;
            // Only the window itself is baked in. The arm movement is a short
            // looping CSS animation, so one range is all this needs.
            gA.push([s0, s1]);
          } else {
            sitR.push([s0, s1]);
          }
        }
        at = s1;
      });
      if (!firstPt) firstPt = parseFirst(posKf[0] || '');
      // Close the loop exactly on the first point.
      posKf.push(atPct(100, firstPt[0], firstPt[1], firstZ));

      var css = '@keyframes ' + name + '_p{' + posKf.join('') + '}' +
        '@keyframes ' + name + '_s{' + opacityFrames(sitR) + '}' +
        '@keyframes ' + name + '_a{' + opacityFrames(aR) + '}' +
        '@keyframes ' + name + '_b{' + opacityFrames(bR) + '}' +
        (gesture
          ? '@keyframes ' + name + '_g{' + opacityFrames(gA) + '}'
          : '');

      var el = window.__officeStyle;
      if (!el) {
        el = document.createElement('style');
        el.id = 'office-anim';
        document.head.appendChild(el);
        window.__officeStyle = el;
      }
      el.appendChild(document.createTextNode(css));
      animCache[sig] = 1;
      return { base: name, cached: false };
    }

    // Painter's-algorithm depth: nearest to the viewer is the largest c+r. This
    // has to travel WITH the animation, because a walking figure passes behind
    // one desk and in front of the next. One static value taken from the
    // destination made them walk through the furniture.
    function zOf(tile) { return 5 + (tile.c + tile.r) * 10; }

    function atPct(pct, left, top, z) {
      return pct.toFixed(3) + '%{transform:translate(' + left.toFixed(1) + 'px,' + top.toFixed(1) +
        'px);z-index:' + Math.round(z) + '}';
    }
    function parseFirst(kf) {
      var m = kf.match(/translate\(([\d.-]+)px,([\d.-]+)px\)/);
      return m ? [+m[1], +m[2]] : [0, 0];
    }
    function pathLength(pts) {
      var total = 0;
      for (var i = 1; i < pts.length; i++) {
        var dx = pts[i][0] - pts[i - 1][0], dy = pts[i][1] - pts[i - 1][1];
        total += Math.sqrt(dx * dx + dy * dy);
      }
      return total;
    }
    // A point "want" pixels along the path, measured from the start. Also
    // returns which segment it landed on and how far along it, so the caller
    // can interpolate the depth from the tiles at either end.
    function pointOn(pts, want) {
      var acc = 0;
      for (var i = 1; i < pts.length; i++) {
        var dx = pts[i][0] - pts[i - 1][0], dy = pts[i][1] - pts[i - 1][1];
        var d = Math.sqrt(dx * dx + dy * dy);
        if (acc + d >= want) {
          var u = d ? (want - acc) / d : 0;
          return [pts[i - 1][0] + dx * u, pts[i - 1][1] + dy * u, i - 1, u];
        }
        acc += d;
      }
      var lastSeg = pts.length - 2;
      return [pts[pts.length - 1][0], pts[pts.length - 1][1], lastSeg < 0 ? 0 : lastSeg, 1];
    }

    // Build an opacity keyframe list where the pose is visible during the
    // given [start,end] ranges and hidden elsewhere. Ranges MUST arrive
    // sorted and disjoint: the cursor below assumes it, and out-of-order
    // ranges emit percentages like 83 followed by 11, which the browser
    // silently clamps and the pose then never changes.
    function opacityFrames(ranges) {
      var rs = ranges.slice().sort(function(a, b) { return a[0] - b[0]; });
      var kf = [], cursor = 0;
      rs.forEach(function(rg) {
        var s = Math.max(0, rg[0]), e = Math.min(100, rg[1]);
        if (e <= s + 0.05) return;
        if (s > cursor + 0.05) kf.push([cursor, s - 0.02, 0]);
        // End the visible run a hair early. Ending it AT e would make it
        // overlap the next pose by 0.02%, leaving two poses opaque at once.
        kf.push([s, e - 0.02, 1]);
        cursor = Math.max(cursor, e);
      });
      if (cursor < 100) kf.push([cursor, 100, 0]);
      return kf.map(function(k) {
        return k[0].toFixed(3) + '%{opacity:' + k[2] + '}';
      }).join('');
    }

    function personSVG(c, mode, color) {
      var act = activity(c);
      var stale = isStale(c);
      var id = c.id || '';

      // Which of the four quarters this session belongs in, decided by its
      // status. The timeline decides both the total cycle and every place the
      // figure visits, so the walk legs can be pathfound from one leg to the
      // next rather than always from the same start.
      var zi = stale ? 3 : zoneOf(c);
      var legs, mainTile;
      if (stale) {
        // Untouched for over three days: out of service. It stands still in
        // the corner of the grey quarter, dimmed, so it reads as parked
        // rather than as a session idling normally.
        var sb = zoneFloor(3);
        mainTile = { c: sb.c1, r: sb.r1 };
        legs = [{ k: 'sit', to: mainTile, secs: 999, label: 'OUT_OF_SERVICE_72H' }];
      } else {
        legs = buildZoneTimeline(id, zi);
        mainTile = legs[0].to;
      }

      var total = 0;
      legs.forEach(function(l) { total += l.secs; });
      var cycle = total;
      var phase = phaseOf(id, cycle);

      // Pixel points for one leg. Walks run A* between the two tiles; sits
      // resolve to their seat tile, nudged sideways so two people never share
      // the exact same spot.
      function tileOf(key) {
        // Zone legs carry their tile directly, resolved once from the id.
        if (key && typeof key === 'object') return key;
        var b = zoneFloor(3);
        return { c: b.c0, r: b.r0 };
      }
      function ptsFor(leg) {
        if (leg._pts) return leg._pts;
        var key = String(leg.to);
        var fromTile = tileOf(leg._from != null ? leg._from : 'door');
        var toTile = tileOf(key);
        var ox = seatOffset(id), oy = ox * 0.5;
        // The tiles are kept alongside the pixels so the animation can work
        // out how DEEP the figure is at any point and hide it behind the
        // furniture it is currently walking past.
        if (leg.k === 'sit') {
          leg._tiles = [toTile];
          leg._pts = [[isoX(toTile.c, toTile.r) + ox, isoY(toTile.c, toTile.r) + oy]];
          return leg._pts;
        }
        var path = findPath(fromTile, toTile) || [fromTile, toTile];
        leg._tiles = path;
        leg._pts = path.map(function(p) { return [isoX(p.c, p.r) + ox, isoY(p.c, p.r) + oy]; });
        return leg._pts;
      }
      // Chain the legs so each walk starts where the previous one ended. The
      // first leg is a pause, so it seeds the chain with its own tile.
      var cur = legs[0].to;
      legs.forEach(function(leg) { leg._from = cur; cur = leg.to; });
      // Close the loop: the last leg must end where the first began.
      legs[legs.length - 1]._closeTo = legs[0]._from;

      var anim = stale ? { base: 'none' } : registerTimeline(id, legs, ptsFor, cycle);
      var startPts = ptsFor(legs[0]);

      var bubble = '';
      if (act === 'blocked' || act === 'error' || act === 'sulk') {
        var cls = act === 'blocked' ? 'bubble-warn' : (act === 'error' ? 'bubble-err' : 'bubble-stop');
        bubble = '<g class="bubble ' + cls + '">' +
          '<rect x="29" y="-2" width="14" height="11" rx="2.5"/>' +
          '<path d="M32 9 L28 14 L35 9 Z"/>' +
          '<text x="36" y="7.6" class="bubble-mark">' + (act === 'error' ? '&#10007;' : '!') + '</text></g>';
      }

      var label = (c.title || c.id) + ' - ' + (c.status ? c.status.label : '');
      var state = stale ? legs[0].label : stateNow(legs, total, cycle);
      var gesture = null;
      for (var gj = 0; gj < legs.length; gj++) if (legs[gj].gesture) gesture = legs[gj].gesture;

      // Feed the debug overlay. Recorded every rebuild so the panel is current.
      var dbgLegs = legs.map(function(l) { return { label: l.label, secs: l.secs }; });
      dbg[c.id] = {
        id: c.id, title: label, state: state, cycle: cycle, legs: dbgLegs,
        tile: mainTile.c + ',' + mainTile.r,
        z: depthOf(mainTile.c, mainTile.r) + 5,
        x: startPts[0][0].toFixed(0), y: startPts[0][1].toFixed(0),
        pathLen: legs.reduce(function(n, l) {
          var p = ptsFor(l);
          return n + (p.length > 1 ? p.length : 0);
        }, 0),
        anim: stale ? '(staar stille)' : anim.base,
      };
      renderDebug();
      return '<div class="walker walker-' + act + '" data-mode="zone" data-zi="' + zi + '" ' +
          'data-state="' + state + '" ' +
          (stale ? 'data-stale="1" ' : '') +
          (gesture ? 'data-gesture="' + gesture + '" ' : '') +
          (stale ? '' : 'data-anim="' + anim.base + '" ') +
          'style="--x0:' + startPts[0][0].toFixed(1) + 'px;--y0:' + startPts[0][1].toFixed(1) + 'px;' +
            '--anim-p:' + anim.base + '_p;--anim-s:' + anim.base + '_s;' +
            '--anim-a:' + anim.base + '_a;--anim-b:' + anim.base + '_b;' +
            '--anim-g:' + anim.base + '_g;' +
            '--shirt:' + colorHex(color) + ';' +
            '--z:' + depthOf(mainTile.c, mainTile.r) + ';' +
            '--cycle:' + cycle.toFixed(3) + 's;--phase:' + phase + '" ' +
          'data-session-id="' + esc(c.id) + '" ' +
          // Escape sequences are eaten by the serving layer; keep this line single.
          'title="' + esc(label + ' - ' + state) + '" role="img" aria-label="' + esc(state) + '">' +
        '<span class="fig-state">' + esc(state) + '</span>' +
        '<svg class="person person-' + act + '" viewBox="-4 -6 48 68" width="48" height="68">' +
          bubble +
          '<g class="pose pose-sit">' + poseSit(act) + '</g>' +
          '<g class="pose pose-walk-a">' + poseStand(act, false) + '</g>' +
          '<g class="pose pose-walk-b">' + poseStand(act, true) + '</g>' +
          '<g class="pose pose-gest">' + poseGesture(act, gesture || 'type') + '</g>' +
        '</svg>' +
      '</div>';
    }

    // ---- The office -------------------------------------------------
    // ONE room for every session, whatever the card grouping is. Grouping
    // still decides the shirt colour, so you can see which project someone
    // belongs to - it just no longer splits them into separate offices.
    function houseOfficeHTML(cards) {
      var grouping = localStorage.getItem('dashboardGrouping') || 'none';
      var buckets = {};
      cards.forEach(function(c) {
        var label = grouping === 'status' ? statusGroup(c)
          : (grouping === 'label' ? (getLabel(c.id) || 'Unlabeled') : directoryGroup(c));
        if (!buckets[label]) buckets[label] = [];
        buckets[label].push(c);
      });
      // Grouping still decides the shirt colour, so you can tell which project
      // someone belongs to. It just no longer splits the office into rooms.
      var shirt = {};
      Object.keys(buckets).forEach(function(label) {
        var col = groupColor(label, buckets[label], grouping);
        buckets[label].forEach(function(c) { shirt[c.id] = col; });
      });

      var walkers = cards.map(function(c) {
        return personSVG(c, 'zone', shirt[c.id]);
      }).join('');

      // Head counts per quarter, for the legend. Stale sessions count as grey:
      // they are parked there, not idling.
      var counts = [0, 0, 0, 0];
      cards.forEach(function(c) { counts[isStale(c) ? 3 : zoneOf(c)]++; });

      var stageW = ORIGIN_X + GRID * (TW / 2) + 40;
      var stageH = ORIGIN_Y + GRID * TH + 110;

      var legend = ZONES.map(function(z, i) {
        return '<span class="lg lg-' + z.key + '">' + z.label + ' <b>' + counts[i] + '</b></span>';
      }).join('') +
        (counts[3] !== cards.length ? '' : '');

      return '<section class="office">' +
        '<div class="office-header">' +
          '<span class="office-title">Zones</span>' +
          '<span class="office-legend">' + legend + '</span>' +
          '<span class="office-count">' + cards.length + '</span>' +
          // The header is rebuilt every second, so the button's state has to be written
          // into the markup. Patching the node after the fact meant it showed
          // "Debug ON" for a second and then reverted, because the next render
          // emitted a fresh button with the default text.
          '<button class="dbg-toggle' + (debugOn ? ' on' : '') + '" type="button" ' +
            'aria-pressed="' + (debugOn ? 'true' : 'false') + '" ' +
            'title="Toggle the debug panel (Ctrl+D)">' + (debugOn ? 'Debug ON' : 'Debug') + '</button>' +
        '</div>' +
        '<div class="office-viewport" style="height:' + stageH.toFixed(0) + 'px" title="Scroll = zoom, right-click drag = move, double-click = reset">' +
          '<div class="office-stage" style="width:' + stageW.toFixed(0) + 'px;height:' + stageH.toFixed(0) + 'px;' + viewCss() + '">' +
          '<svg class="iso-svg" width="' + stageW.toFixed(0) + '" height="' + stageH.toFixed(0) + '">' +
            isoFloorSVG() +
            zoneSVG(counts) +
          '</svg>' +
          '<div class="walker-layer">' + walkers + '</div>' +
        '</div></div>' +
      '</section>';
    }

    function render(cards) {
      var container = document.getElementById('grid');
      var mode = localStorage.getItem('dashboardInfoMode') || 'standard';
      var grouping = localStorage.getItem('dashboardGrouping') || 'none';
      var q = document.getElementById('filterInput').value.trim().toLowerCase();

      checkAlarms(cards,
        localStorage.getItem('dashboardAlarmJobsDone') === 'yes',
        localStorage.getItem('dashboardAlarmErrors') === 'yes',
        localStorage.getItem('dashboardAlarmUsers') === 'yes');

      // Preserve open/closed state of accordion elements across 1-second auto-refreshes
      document.querySelectorAll('.sub-agents-details[data-card-id], .todos-details[data-card-id]').forEach(function(el) {
        var cardId = el.getAttribute('data-card-id');
        if (cardId) {
          window.openStates[cardId] = el.open;
        }
      });

      if (q) {
        cards = cards.filter(function(c) {
          var hay = (c.title + ' ' + c.agent + ' ' + c.status.label + ' ' + (c.directory || '')).toLowerCase();
          return hay.indexOf(q) !== -1;
        });
      }

      if (!cards || cards.length === 0) {
        container.className = 'grid';
        container.innerHTML = '<div class="offline-box">' +
          '<div class="offline-title">No open OpenCode terminals detected.</div>' +
          '<div class="offline-tip">Open a terminal window and run opencode to see live session status.</div>' +
        '</div>';
        return;
      }
      var html = mode === 'house' ? houseOfficeHTML(cards) : groupedHTML(cards, mode, grouping);
      container.className = mode === 'house' ? 'house-grid'
        : (grouping === 'none' || html.indexOf('group-box') === -1 ? 'grid' : 'grouped-grid');
      container.innerHTML = html;
    }

    function loadSettings() {
      if (!localStorage.getItem('dashboardInfoMode')) localStorage.setItem('dashboardInfoMode', 'standard');
      if (!localStorage.getItem('dashboardGrouping')) localStorage.setItem('dashboardGrouping', 'none');
      [['dashboardAlarmJobsDone', 'no'], ['dashboardAlarmErrors', 'no'], ['dashboardAlarmUsers', 'no'], ['dashboardAutoFoldTodos', 'yes'], ['dashboardAutoFoldAgents', 'yes']].forEach(function(pair) {
        if (!localStorage.getItem(pair[0])) localStorage.setItem(pair[0], pair[1]);
      });

      function updateMenuState() {
        document.querySelectorAll('[data-setting][data-value]').forEach(function(btn) {
          var setting = btn.getAttribute('data-setting');
          var value = btn.getAttribute('data-value');
          btn.classList.toggle('active', localStorage.getItem(setting) === value);
        });
        document.querySelectorAll('[data-toggle]').forEach(function(btn) {
          var key = btn.getAttribute('data-toggle');
          var on = localStorage.getItem(key) === 'yes';
          btn.classList.toggle('active', on);
          btn.textContent = on ? 'ON' : 'OFF';
        });
      }

      document.querySelectorAll('[data-setting][data-value]').forEach(function(btn) {
        btn.addEventListener('click', function(e) {
          e.preventDefault();
          e.stopPropagation();
          localStorage.setItem(btn.getAttribute('data-setting'), btn.getAttribute('data-value'));
          updateMenuState();
          refresh();
        });
      });
      document.querySelectorAll('[data-toggle]').forEach(function(btn) {
        btn.addEventListener('click', function(e) {
          e.preventDefault();
          e.stopPropagation();
          var key = btn.getAttribute('data-toggle');
          localStorage.setItem(key, localStorage.getItem(key) === 'yes' ? 'no' : 'yes');
          updateMenuState();
          refresh();
        });
      });

      var settingsMenu = document.getElementById('settingsMenu');
      var settingsWrap = document.getElementById('settingsWrap');
      var settingsButton = document.getElementById('settingsButton');
      var settingsCloseTimer = null;
      function openSettings() {
        if (settingsCloseTimer) clearTimeout(settingsCloseTimer);
        settingsMenu.classList.add('open');
      }
      function closeSettings() { settingsMenu.classList.remove('open'); }
      function scheduleCloseSettings() { settingsCloseTimer = setTimeout(closeSettings, 100); }
      settingsButton.addEventListener('click', function(e) { e.preventDefault(); e.stopPropagation(); openSettings(); });
      settingsWrap.addEventListener('mouseenter', openSettings);
      settingsWrap.addEventListener('mouseleave', scheduleCloseSettings);
      document.getElementById('grid').addEventListener('click', function(e) {
        var header = e.target.closest ? e.target.closest('.group-header[data-group-key]') : null;
        if (!header) return;
        var key = header.getAttribute('data-group-key');
        window.openStates[key] = window.openStates[key] === false;
        refresh();
      });
      updateMenuState();
      document.getElementById('filterInput').addEventListener('input', refresh);
    }

    async function refresh() {
      try {
        const res = await fetch('/api/data');
        const cards = await res.json();
        render(cards);
      } catch(e) {}
    }

    setInterval(refresh, 1000);
    // Bound while the script parses, not inside onload: a handler registered after
// the load event has already fired never runs. window.addEventListener is used
// rather than assigning window.onload, which would clobber any other handler.
installDebug();
installPanZoom();
loadView();
window.addEventListener('load', function() { loadSettings(); refresh(); });
  </script>
  <style>
    body { background-color: #0f172a; color: #f8fafc; font-family: system-ui, -apple-system, sans-serif; margin: 0; padding: 24px; }
    h1 { margin-top: 0; font-size: 1.5rem; color: #94a3b8; margin-bottom: 20px; }
    .grid { display: grid; grid-template-columns: repeat(auto-fill, 360px); gap: 20px; align-items: start; }
    .card { width: 360px; box-sizing: border-box; background: #1e293b; border-radius: 8px; border-left: 6px solid #64748b; padding: 16px; box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.3); display: flex; flex-direction: column; transition: all 0.3s ease; }
    .card.status-white { border-left-color: #f3f4f6; }
    .card.status-green { border-left-color: #22c55e; }
    .card.status-red { border-left-color: #ef4444; }
    .card.status-yellow { border-left-color: #eab308; }
    .card.status-orange { border-left-color: #f97316; }
    .card.status-skyblue { border-left-color: #38bdf8; }
    .card.status-cyan { border-left-color: #22d3ee; }
    .card.status-gray { border-left-color: #64748b; opacity: 0.65; }
    
    .card-header { display: flex; flex-direction: column; margin-bottom: 10px; gap: 4px; }
    .session-title { font-weight: bold; font-size: 1.1rem; line-height: 1.2; word-break: break-word; }
    .subtitle-row { display: flex; justify-content: space-between; align-items: center; gap: 8px; margin-top: 2px; }
    .session-subtitle { font-size: 0.85rem; color: #94a3b8; font-weight: 500; }

    /* Directory group header: folder name in mono, full path on hover. */
    .group-dir {
      font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      text-transform: none;
      letter-spacing: 0;
    }
    .badge { font-size: 0.75rem; padding: 4px 8px; border-radius: 4px; font-weight: 600; text-transform: uppercase; white-space: nowrap; }
    .badge-white { background: #ffffff; color: #0f172a; }
    .badge-green { background: #22c55e; color: #052e16; }
    .badge-red { background: #ef4444; color: #450a0a; }
    .badge-yellow { background: #eab308; color: #422006; }
    .badge-orange { background: #f97316; color: #431407; }
    .badge-skyblue { background: #38bdf8; color: #082f49; }
    .badge-cyan { background: #22d3ee; color: #083344; }
    .badge-gray { background: #64748b; color: #f8fafc; }
    
    .time-compact { font-size: 0.8rem; color: #cbd5e1; margin-bottom: 6px; }
    .time-compact .label { color: #94a3b8; }
    .time-compact .value { font-weight: 600; color: #f8fafc; }
    .time-compact .timer-value { display: inline-block; min-width: 5.36ch; text-align: right; font-family: ui-monospace, SFMono-Regular, Consolas, "Liberation Mono", monospace; font-variant-numeric: tabular-nums; }
    .time-compact .divider { margin: 0 6px; color: #475569; }
    .time-compact .highlight-waiting { color: #fde047; font-weight: 600; }
    .time-compact .cold-cache { color: #7dd3fc; font-size: 0.9rem; vertical-align: middle; }
    .time-compact > div + div { margin-top: 2px; }
    .session-label { display: inline-block; margin-left: 8px; font-size: 0.7rem; font-weight: 600; color: #0f172a; background: #7dd3fc; border-radius: 4px; padding: 1px 6px; vertical-align: middle; }
    .label-blue { background: #38bdf8 !important; color: #082f49 !important; }
    .label-green { background: #22c55e !important; color: #052e16 !important; }
    .label-red { background: #ef4444 !important; color: #450a0a !important; }
    .label-yellow { background: #eab308 !important; color: #422006 !important; }
    .label-orange { background: #f97316 !important; color: #431407 !important; }
    .label-purple { background: #a855f7 !important; color: #2e1065 !important; }
    .label-pink { background: #ec4899 !important; color: #500724 !important; }
    .label-cyan { background: #06b6d4 !important; color: #083344 !important; }
    .label-gray { background: #64748b !important; color: #f8fafc !important; }
    .label-white { background: #f3f4f6 !important; color: #0f172a !important; }
    .context-menu { position: fixed; background: #1e293b; border: 1px solid #334155; border-radius: 6px; box-shadow: 0 8px 16px rgba(0, 0, 0, 0.4); padding: 4px; z-index: 1000; min-width: 140px; }
    .context-menu button { display: block; width: 100%; text-align: left; background: none; border: none; color: #f8fafc; padding: 6px 10px; font-size: 0.8rem; font-family: system-ui, -apple-system, sans-serif; cursor: pointer; border-radius: 4px; }
    .context-menu button:hover { background: #334155; }
    .context-menu-title { color: #94a3b8; font-size: 0.7rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.06em; padding: 6px 8px 3px; }
    .context-submenu-wrap { position: relative; }
    .context-submenu-trigger::after { content: 'Ã¢â‚¬Âº'; float: right; }
    .context-submenu { display: none; position: absolute; left: 100%; top: 0; min-width: 150px; background: #1e293b; border: 1px solid #334155; border-radius: 6px; box-shadow: 0 8px 16px rgba(0, 0, 0, 0.4); padding: 4px; }
    .context-submenu-wrap:hover .context-submenu { display: block; }
    .label-pick-row { display: flex; align-items: center; gap: 4px; }
    .label-pick-row .label-pick { flex: 1; }
    .label-pick-remove { flex: 0 0 20px; width: 20px; text-align: center; color: #94a3b8; }
    .label-pick-remove:hover { color: #ef4444; }
    .label-color-grid { display: grid; grid-template-columns: repeat(5, 20px); gap: 5px; padding: 4px 8px 8px; }
    .context-menu .label-color-choice { width: 20px; height: 20px; padding: 0; border: 1px solid #0f172a; border-radius: 50%; }
    .context-menu .label-color-choice:hover { outline: 2px solid #f8fafc; background: inherit; }
    .context-menu .label-color-choice.chosen { outline: 2px solid #f8fafc; }
    /* Auto swatch: split circle, the same convention as the other labels. */
    .context-menu .label-color-choice.label-auto {
      background: conic-gradient(#ef4444 0 33%, #22c55e 33% 66%, #3b82f6 66% 100%);
      color: #0f172a; font-size: 11px; font-weight: 800; line-height: 1;
    }
    /* Group header: right-click sets this group's colour. */
    .group-header[data-group-label] { cursor: context-menu; }
    .group-header[data-group-label]:hover { filter: brightness(1.08); }

    .controls { display: flex; gap: 10px; margin-bottom: 20px; align-items: center; flex-wrap: nowrap; position: relative; }
    .controls input {
      background: #1e293b; color: #f8fafc; border: 1px solid #334155; border-radius: 6px;
      padding: 8px 12px; font-size: 0.85rem; font-family: system-ui, -apple-system, sans-serif;
    }
    .controls input { flex: 1; min-width: 180px; }
    .controls input::placeholder { color: #64748b; }
    .settings-wrap { position: relative; flex: 0 0 auto; }
    .settings-button { width: 38px; height: 38px; border-radius: 6px; border: 1px solid #334155; background: #1e293b; color: #cbd5e1; font-size: 1.1rem; cursor: pointer; }
    .settings-button:hover { border-color: #475569; color: #f8fafc; }
    .settings-menu { display: none; position: absolute; right: 0; top: 44px; z-index: 1000; min-width: 260px; background: #111827; border: 1px solid #334155; border-radius: 8px; box-shadow: 0 12px 28px rgba(0,0,0,0.45); padding: 12px; }
    .settings-menu.open { display: block; }
    .settings-section + .settings-section { margin-top: 12px; padding-top: 12px; border-top: 1px solid #334155; }
    .settings-heading { color: #94a3b8; font-size: 0.72rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.08em; margin-bottom: 7px; }
    .settings-row { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-top: 6px; }
    .settings-options { display: flex; gap: 6px; flex-wrap: wrap; }
    .settings-option, .settings-toggle { border: 1px solid #334155; background: #0f172a; color: #cbd5e1; border-radius: 6px; padding: 5px 8px; font-size: 0.78rem; font-family: system-ui, -apple-system, sans-serif; cursor: pointer; }
    .settings-option:hover, .settings-toggle:hover { border-color: #475569; color: #f8fafc; }
    .settings-option.active, .settings-toggle.active { background: #38bdf8; border-color: #38bdf8; color: #082f49; font-weight: 700; }
    .settings-row-label { color: #cbd5e1; font-size: 0.82rem; }
    .grouped-grid { display: flex; flex-direction: column; gap: 18px; }
    .group-box { position: relative; border: 1px solid #334155; border-left: 4px solid #f3f4f6; border-radius: 10px; padding: 22px 16px 16px; background: #172033; }
    .group-header { position: absolute; top: -14px; left: 16px; display: inline-flex; align-items: center; gap: 6px; margin: 0; background: #f3f4f6; color: #0f172a; border: 1px solid #334155; border-radius: 6px; padding: 4px 10px; font-size: 0.72rem; font-weight: 700; letter-spacing: 0.08em; text-transform: uppercase; white-space: nowrap; cursor: pointer; }
    .group-header.label-group { font-size: calc(0.72rem + 2px); }
    .group-body.collapsed { display: none; }
    .group-white { border-left-color: #f3f4f6; }
    .group-white .group-header { background: #f3f4f6; color: #0f172a; }
    .group-green { border-left-color: #22c55e; }
    .group-green .group-header { background: #22c55e; color: #052e16; }
    .group-red { border-left-color: #ef4444; }
    .group-red .group-header { background: #ef4444; color: #450a0a; }
    .group-yellow { border-left-color: #eab308; }
    .group-yellow .group-header { background: #eab308; color: #422006; }
    .group-orange { border-left-color: #f97316; }
    .group-orange .group-header { background: #f97316; color: #431407; }
    .group-skyblue { border-left-color: #38bdf8; }
    .group-skyblue .group-header { background: #38bdf8; color: #082f49; }
    .group-gray { border-left-color: #64748b; }
    .group-gray .group-header { background: #64748b; color: #f8fafc; }
    .group-blue { border-left-color: #38bdf8; }
    .group-blue .group-header { background: #38bdf8; color: #082f49; }
    .group-purple { border-left-color: #a855f7; }
    .group-purple .group-header { background: #a855f7; color: #2e1065; }
    .group-pink { border-left-color: #ec4899; }
    .group-pink .group-header { background: #ec4899; color: #500724; }
    .group-cyan { border-left-color: #06b6d4; }
    .group-cyan .group-header { background: #06b6d4; color: #083344; }
    .group-cards { margin-left: 8px; }

    /* ---- House view: one office, many figures ---- */
    .house-grid { display: flex; flex-direction: column; gap: 18px; }

    .office {
      border: 1px solid #334155;
      border-radius: 10px;
      overflow: hidden;
      background: linear-gradient(180deg, #0f172a 0%, #111c33 62%, #0d1526 100%);
    }
    .office-header {
      display: flex; align-items: center; gap: 10px;
      padding: 7px 12px;
      background: #1e293b;
      border-bottom: 1px solid #334155;
    }
    .office-title { font-weight: 700; font-size: 0.85rem; color: #e2e8f0; }
    .office-legend { display: flex; gap: 9px; flex-wrap: wrap; }
    .lg { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
    .lg { font-size: 0.68rem; color: #64748b; display: flex; align-items: center; gap: 4px; }
    .lg::before { content: ""; width: 8px; height: 8px; border-radius: 50%; display: inline-block; }
    .lg-work::before, .lg-green::before { background: #22c55e; }
    .lg-walk::before { background: #38bdf8; }
    .lg-ask::before, .lg-orange::before { background: #f97316; }
    .lg-err::before, .lg-red::before { background: #ef4444; }
    .lg-still::before, .lg-grey::before { background: #64748b; }
    .lg b { color: #e2e8f0; font-weight: 700; }
    .office-count { margin-left: auto; font-size: 0.75rem; color: #64748b; font-variant-numeric: tabular-nums; }

    /* ---- Isometric stage -------------------------------------------
       The floor and every cuboid are drawn in one SVG that already carries
       the 2:1 isometric projection, so nothing is skewed with CSS transforms
       and the grid, the furniture and the figures all agree on where a tile
       is. Figures stand upright (a "billboard") on top of the projection,
       which is how isometric games draw people. */
    .office-stage {
      position: relative;
      overflow: hidden;
      background:
        radial-gradient(ellipse 70% 60% at 50% 42%, #16213a 0%, #0b1222 72%, #070c18 100%);
      /* Scales about the middle, which is also what setZoom() assumes. */
      transform-origin: 50% 50%;
      will-change: transform;
    }
    /* The window you pan and zoom inside. The stage keeps its own pixel size;
       the viewport clips it and takes the gestures. */
    .office-viewport {
      position: relative;
      overflow: hidden;
      background: #070c18;
      border-top: 1px solid rgba(148,163,184,0.14);
      cursor: grab;
      touch-action: none;
    }
    .office-viewport.panning { cursor: grabbing; }

    /* While the camera is moving the figures freeze. Every one of them
       animates left, top, z-index and opacity each frame, and repainting that
       under a moving transform was most of the cost of a pan. */
    .office-viewport.interacting .walker,
    .office-viewport.interacting .person .pose,
    .office-viewport.interacting .garm { animation-play-state: paused; }
    .iso-svg { position: absolute; inset: 0; display: block; z-index: 1; }
    /* Each piece of furniture is its own layer so it interleaves with the
       figures by depth instead of sitting in one flat SVG above or below. */
    .piece { position: absolute; pointer-events: none; }
    .piece svg { display: block; overflow: visible; }

    /* Floor */
    .iso-floor-face { fill: #16213a; stroke: rgba(148, 163, 184, 0.30); stroke-width: 1; }
    .iso-grid { stroke: rgba(148, 163, 184, 0.11); stroke-width: 1; }

    /* Cuboid faces. In this projection the +c edge faces right-down and the
       +r edge faces left-down, so those two are the lit and shaded sides and
       the rhombus on top is the brightest. */
    .iso .fx-top   { fill: #475569; stroke: rgba(2, 6, 23, 0.55); stroke-width: 0.6; }
    .iso .fx-left  { fill: #263449; stroke: rgba(2, 6, 23, 0.55); stroke-width: 0.6; }
    .iso .fx-right { fill: #1c2740; stroke: rgba(2, 6, 23, 0.55); stroke-width: 0.6; }

    .iso.desk .fx-top { fill: #b98a54; }
    .iso.desk .fx-left { fill: #8a5f34; }
    .iso.desk .fx-right { fill: #75502c; }

    .iso .screen { fill: #0f172a; stroke: #475569; stroke-width: 0.8; }
    .iso .screen-glow { fill: #38bdf8; opacity: 0.85; }
    .iso .chair { fill: #4b5563; stroke: #0f172a; stroke-width: 0.5; }

    .iso.machine .fx-top { fill: #64748b; }
    .iso.machine .fx-left { fill: #3f4b5f; }
    .iso.machine .fx-right { fill: #334155; }
    .iso .glow { fill: #fbbf24; }

    .iso.board .fx-top { fill: #7c5a3a; }
    .iso.board .fx-left { fill: #5c4229; }
    .iso.board .fx-right { fill: #4a3520; }
    .iso .board { fill: #1e293b; stroke: #64748b; stroke-width: 1; }
    .iso .board-inner { fill: #ef4444; stroke: none; }
    .iso.cabinet .fx-top { fill: #7c5a3a; }
    .iso.cabinet .fx-left { fill: #5c4229; }
    .iso.cabinet .fx-right { fill: #4a3520; }

    .iso.sofa .fx-top { fill: #64748b; }
    .iso.sofa .fx-left { fill: #475569; }
    .iso.sofa .fx-right { fill: #3f4b5f; }
    .iso.sofa-back .fx-top { fill: #7c8ba1; }
    .iso.sofa-back .fx-left { fill: #55637a; }
    .iso.sofa-back .fx-right { fill: #475569; }
    .iso.sofa-arm .fx-top { fill: #94a3b8; }
    .iso.sofa-arm .fx-left { fill: #64748b; }
    .iso.sofa-arm .fx-right { fill: #55637a; }

    .iso.wc .fx-top { fill: #f1f5f9; }
    .iso.wc .fx-left { fill: #cbd5e1; }
    .iso.wc .fx-right { fill: #b6c2d1; }
    .iso.wc-tank .fx-top { fill: #f8fafc; }
    .iso.wc-tank .fx-left { fill: #dde4ed; }
    .iso.wc-tank .fx-right { fill: #c7d0dc; }

    .iso.counter .fx-top { fill: #b98a54; }
    .iso.counter .fx-left { fill: #8a5f34; }
    .iso.counter .fx-right { fill: #75502c; }
    .iso.pot .fx-top { fill: #94a3b8; }
    .iso.pot .fx-left { fill: #64748b; }
    .iso.pot .fx-right { fill: #55637a; }

    .iso .door { fill: #334155; stroke: #64748b; stroke-width: 1; }
    .iso.door-frame .fx-top { fill: #64748b; }
    .iso.door-frame .fx-left { fill: #3f4b5f; }
    .iso.door-frame .fx-right { fill: #334155; }
    .iso.stool .fx-top { fill: #6b7280; }
    .iso.stool .fx-left { fill: #4b5563; }
    .iso.stool .fx-right { fill: #3f4650; }
    .iso.stool-back .fx-top { fill: #7c8ba1; }
    .iso.stool-back .fx-left { fill: #55637a; }
    .iso.stool-back .fx-right { fill: #475569; }

    /* Walkers travel between two points. --phase is a negative delay derived
       from the WALL CLOCK, so the 1s grid rebuild resumes each figure at the
       point it had actually reached and the walk reads as continuous. A fixed
       delay froze every figure at the same spot forever. */
    /* ---- Furniture, kept for when the room comes back ----------------
       Nothing renders this today. The rules stay so that restoring it is a
       matter of putting the pieces back into houseOfficeHTML, not of
       rewriting the look from scratch.
       ---------------------------------------------------------------- */

    /* Walled meeting room and the broom closet. Walls have no top face, only a
       thickness strip, so you see in over the near wall - which is the whole
       reason to draw a room isometrically in the first place. */
    .wall { fill: #3f4c63; stroke: #0f172a; stroke-width: 0.8; }
    .wall-top { fill: #5b6a84; stroke: #0f172a; stroke-width: 0.6; }
    .door { fill: #7c5a3a; stroke: #0f172a; stroke-width: 0.8; }
    .door-knob { fill: #fbbf24; }
    .door-frame .fx-top { fill: #64748b; }
    .door-frame .fx-left { fill: #3f4b5f; }
    .door-frame .fx-right { fill: #334155; }
    .mtable { fill: #7c5a3a; stroke: #0f172a; stroke-width: 0.7; }
    .mtable-side { fill: #5c4229; stroke: #0f172a; stroke-width: 0.5; }
    .mstool { fill: #b98a54; stroke: #0f172a; stroke-width: 0.6; }
    .mstool-stem, .mstool-foot { fill: #8a5f34; stroke: #0f172a; stroke-width: 0.4; }

    /* Shelving and the low table between the sofas. */
    .iso.shelf .fx-top { fill: #64748b; }
    .iso.shelf .fx-left { fill: #475569; }
    .iso.shelf .fx-right { fill: #3b4658; }
    .shelf-gap { stroke: #1e293b; stroke-width: 2; }
    .iso.ctable .fx-top { fill: #8a5f34; }
    .iso.ctable .fx-left { fill: #6b4a28; }
    .iso.ctable .fx-right { fill: #5a3e21; }
    .iso.books .fx-top { fill: #e2e8f0; }
    .iso.books .fx-left { fill: #cbd5e1; }
    .iso.books .fx-right { fill: #b6c2d1; }
    .plant { fill: #22c55e; stroke: #14532d; stroke-width: 0.6; }
    .iso.board-inner .fx-top { fill: #ef4444; }
    .iso.board-inner .fx-left { fill: #b91c1c; }
    .iso.board-inner .fx-right { fill: #991b1b; }
    .broom-stick { stroke: #b98a54; stroke-width: 1.4; fill: none; stroke-linecap: round; }
    .broom-head { fill: #a16207; stroke: #0f172a; stroke-width: 0.5; }

    /* ---- The four quarters ------------------------------------------
       One per status class. The fills are deliberately faint: this is a colour
       key for a crowd of figures, not the main event, and a strong wash would
       swallow the shirts. */
    .zone { stroke-width: 1.5; }
    .zone-green { fill: rgba(34,197,94,0.13); stroke: rgba(34,197,94,0.45); }
    .zone-orange { fill: rgba(249,115,22,0.13); stroke: rgba(249,115,22,0.45); }
    .zone-red { fill: rgba(239,68,68,0.13); stroke: rgba(239,68,68,0.45); }
    .zone-grey { fill: rgba(100,116,139,0.12); stroke: rgba(100,116,139,0.38); }
    /* Name and head count in the middle of each quarter. */
    .zone-tag text { text-anchor: middle; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
    .zone-tag text:first-child { font-size: 11px; letter-spacing: 1.4px; font-weight: 700; }
    .zone-tag .zone-n { font-size: 17px; font-weight: 700; }
    .zone-green + .zone-tag text { fill: #22c55e; }
    .zone-orange + .zone-tag text { fill: #f97316; }
    .zone-red + .zone-tag text { fill: #ef4444; }
    .zone-grey + .zone-tag text { fill: #94a3b8; }

    /* A session nobody has touched for three days stands still, dimmed, so it
       reads as parked rather than idling. */
    .walker[data-stale="1"] .person { opacity: 0.5; filter: grayscale(0.7) brightness(0.75); }
    .walker[data-stale="1"] .pose-sit { animation: none; opacity: 1; }
    .walker[data-stale="1"] .pose-walk-a,
    .walker[data-stale="1"] .pose-walk-b,
    .walker[data-stale="1"] .pose-gest { animation: none; opacity: 0; }
    .walker[data-state="OUT_OF_SERVICE_72H"] .fig-state { color: #94a3b8; border-color: rgba(100,116,139,0.5); }

    .walker { position: absolute; width: 48px; height: 68px; cursor: pointer; }
    .walker:hover { filter: brightness(1.25); }
    /* Movement animates transform, not left/top. left/top force a layout pass on
       every one of the 23 figures on every frame; translate is composited and
       runs on the GPU. The offsets are PIXELS because a percentage inside
       translate() is relative to the 48px figure, not to the office. */
    .walker {
      left: 0; top: 0;
      transform: translate(var(--x0), var(--y0));
      margin-left: -24px; margin-top: -68px;
      /* Painter's algorithm: nearer tiles (larger c+r) draw over farther ones.
         This was written as .walker[data-z] but the markup never carried a
         data-z attribute, so no figure had any z-index at all and DOM order
         decided everything. --z is always present, so match on that. While a
         figure is walking its @keyframes override this, because depth has to
         change as it passes the desks. */
      z-index: calc(5 + var(--z, 0));
      animation-duration: var(--cycle); animation-timing-function: ease-in-out;
      animation-iteration-count: infinite; animation-delay: var(--phase);
    }
    /* No z-index on the layer itself: giving it one would create a stacking
       context and trap every figure above or below every desk again. Its
       children must share the stage's order. */
    .walker-layer { position: absolute; inset: 0; }
    .walker[data-anim]  { animation-name: var(--anim-p); }

    /* The state a figure is in right now, written by personSVG() from the
       wall clock. Sits above the head and brightens on hover so the office
       can be read at a glance but not shouted at. */
    .fig-state {
      position: absolute;
      left: 50%; bottom: 70px;
      transform: translateX(-50%);
      padding: 1px 5px;
      border-radius: 3px;
      background: rgba(15, 23, 42, 0.82);
      border: 1px solid rgba(148, 163, 184, 0.28);
      color: #94a3b8;
      font: 600 8px/1.35 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      letter-spacing: 0.02em;
      white-space: nowrap;
      pointer-events: none;
      opacity: 0.55;
      transition: opacity 0.15s;
    }
    .walker:hover .fig-state { opacity: 1; color: #e2e8f0; border-color: rgba(148, 163, 184, 0.6); }
    .walker[data-state^="WALKING"] .fig-state { color: #7dd3fc; border-color: rgba(56, 189, 248, 0.45); }
    .walker[data-state^="WORKING"] .fig-state { color: #86efac; border-color: rgba(34, 197, 94, 0.45); }
    .walker[data-state^="QUESTION"] .fig-state { color: #fde047; border-color: rgba(234, 179, 8, 0.5); }
    .walker[data-state^="ERROR"] .fig-state { color: #fca5a5; border-color: rgba(239, 68, 68, 0.5); }
    .walker[data-state^="SULKING"] .fig-state { color: #f0abfc; border-color: rgba(168, 85, 247, 0.5); }

    /* ---- Debug overlay (CTRL+D) ---- */
    .dbg-toggle {
      margin-left: 8px;
      padding: 2px 9px;
      border-radius: 4px;
      border: 1px solid #334155;
      background: #0f172a;
      color: #64748b;
      font: 600 0.64rem/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      cursor: pointer;
    }
    .dbg-toggle:hover { color: #e2e8f0; border-color: #475569; }
    .dbg-toggle.on { color: #f59e0b; border-color: #f59e0b; background: #1e293b; }
    .office-debug {
      position: fixed;
      right: 12px; bottom: 12px;
      z-index: 9999;
      width: 320px;
      padding: 10px 12px 12px;
      background: rgba(2, 6, 23, 0.96);
      border: 1px solid #334155;
      border-radius: 8px;
      box-shadow: 0 12px 32px rgba(0, 0, 0, 0.6);
      color: #cbd5e1;
      font: 11px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      display: none;
    }
    .dbg-head { display: flex; justify-content: space-between; align-items: baseline; margin-bottom: 8px; padding-bottom: 6px; border-bottom: 1px solid #1e293b; }
    .dbg-head b, .dbg-head { color: #f59e0b; font-weight: 700; letter-spacing: 0.08em; }
    .dbg-head span { color: #475569; font-weight: 400; letter-spacing: 0; }
    .dbg-none { color: #64748b; }
    .dbg-title { color: #e2e8f0; margin-bottom: 6px; word-break: break-word; }
    .dbg-state { color: #38bdf8; font-weight: 700; margin-bottom: 8px; }
    .dbg-tbl { width: 100%; border-collapse: collapse; margin-bottom: 8px; }
    .dbg-tbl th { text-align: left; color: #475569; font-weight: 400; border-bottom: 1px solid #1e293b; padding: 2px 0; }
    .dbg-tbl td { padding: 2px 0; color: #64748b; }
    .dbg-tbl td:last-child { text-align: right; }
    .dbg-tbl tr.dbg-cur td { color: #f59e0b; font-weight: 700; }
    .dbg-now { color: #94a3b8; margin-bottom: 8px; }
    .dbg-now b { color: #facc15; }
    .dbg-grid { display: grid; grid-template-columns: auto 1fr; gap: 2px 10px; border-top: 1px solid #1e293b; padding-top: 8px; }
    .dbg-grid span { color: #475569; }
    .dbg-grid code { color: #7dd3fc; word-break: break-all; }

    /* Pose switching ----------------------------------------------------
       Every route gets its own generated @keyframes (see registerTimeline), so
       the strides line up with the bends in the path instead of a fixed
       schedule. Each visible range is bounded by 0.01% steps so every edge is
       a hard cut, and step-end holds the value until the segment ends. */
    .person .pose {
      opacity: 0;
      animation-duration: var(--cycle);
      animation-timing-function: step-end;
      animation-iteration-count: infinite;
      animation-delay: var(--phase);
    }
    .walker[data-anim] .pose-sit     { animation-name: var(--anim-s); }
    .walker[data-anim] .pose-walk-a { animation-name: var(--anim-a); }
    .walker[data-anim] .pose-walk-b { animation-name: var(--anim-b); }
    /* Seated gestures. The pose is off unless the figure carries a data-gesture,
       so someone sitting at the sofa never shows a desk pose. The pose's
       visibility is driven by the cycle keyframes; the arm movement below is a
       short loop shared by every figure, which is why a gesture costs three
       keyframe stops instead of eight hundred. */
    .person .pose-gest { animation: none; opacity: 0; }
    .walker[data-gesture] .pose-gest { animation-name: var(--anim-g); opacity: 0; }
    .walker[data-gesture="type"] { --gest-dur: 0.44s; }
    .walker[data-gesture="flail"] { --gest-dur: 0.30s; }
    /* Rotating about the shoulder, not the figure's centre, or the arms sweep
       around the wrong pivot. */
    .walker[data-gesture] .garm-l { transform-origin: 12.5px 27px; }
    .walker[data-gesture] .garm-r { transform-origin: 23.5px 27px; }
    .walker[data-gesture] .garm-l,
    .walker[data-gesture] .garm-r { animation: gestType var(--gest-dur) ease-in-out infinite; }
    .walker[data-gesture="flail"] .garm-l { animation-name: gestFlailL; }
    .walker[data-gesture="flail"] .garm-r { animation-name: gestFlailR; }
    /* Typing: a two pixel bob, which at this size reads as fingers on keys. */
    @keyframes gestType {
      0%, 100% { transform: translateY(0); }
      50% { transform: translateY(2px); }
    }
    /* Flailing: a wide, fast swing through a big angle, mirrored so the two
       arms do not move as one block. */
    @keyframes gestFlailL {
      0%, 100% { transform: rotate(-36deg); }
      50% { transform: rotate(28deg); }
    }
    @keyframes gestFlailR {
      0%, 100% { transform: rotate(36deg); }
      50% { transform: rotate(-28deg); }
    }

    @media (prefers-reduced-motion: reduce) {
      .person .pose { animation: none; opacity: 0; }
      .walker[data-mode] .pose-sit { animation: none; opacity: 1; }
      .walker[data-mode] .pose-walk-a,
      .walker[data-mode] .pose-walk-b { animation: none; opacity: 0; }
      .walker { animation: none; }
    }

    .person { cursor: pointer; overflow: visible; }
    .person:hover { filter: brightness(1.22); }

    /* Figure parts. .shirt is the piece that carries the group colour. */
    /* The shirt carries the group colour. It arrives as --shirt on the figure
       itself, because there is one office now, not one room per group. */
    .person .shirt { fill: var(--shirt, #3b82f6); stroke: #0f172a; stroke-width: 0.6; stroke-linejoin: round; }
    .person .collar { fill: #f8fafc; stroke: #0f172a; stroke-width: 0.5; }
    .person .placket { stroke: rgba(15, 23, 42, 0.45); stroke-width: 0.7; fill: none; }
    .person .head { fill: #f2d3b0; stroke: #0f172a; stroke-width: 0.6; }
    .person .ear { fill: #e9c39c; stroke: #0f172a; stroke-width: 0.4; }
    .person .hair { fill: #6b4423; stroke: #0f172a; stroke-width: 0.5; }
    .person .eye { fill: #1c1917; }
    .person .eye-closed { stroke: #1c1917; stroke-width: 1.3; fill: none; stroke-linecap: round; }
    .person .brow { stroke: #5a3a1c; stroke-width: 0.9; fill: none; stroke-linecap: round; }
    .person .brow-angry { stroke: #7f1d1d; stroke-width: 1; fill: none; stroke-linecap: round; }
    .person .nose { stroke: #b58b63; stroke-width: 0.8; fill: none; stroke-linecap: round; stroke-linejoin: round; }
    .person .mouth { stroke: #7f1d1d; stroke-width: 1; fill: none; stroke-linecap: round; }
    .person .mouth.frown { stroke: #991b1b; stroke-width: 1.1; }
    .person .mouth.flat { stroke-width: 1.1; }
    .person .leg { stroke: #2b3444; stroke-width: 3.4; fill: none; stroke-linecap: round; }
    .person .shoe { fill: #1f2937; stroke: #0f172a; stroke-width: 0.4; }
    .person .arm { stroke: #e9c39c; stroke-width: 2.7; fill: none; stroke-linecap: round; }
    .person .hand { fill: #f2d3b0; stroke: #0f172a; stroke-width: 0.4; }
    .person .ground-shadow { fill: rgba(15, 23, 42, 0.42); }
    .person .spot { fill: #94a3b8; font-size: 9px; text-anchor: middle; }

    /* ---- Frame animation -------------------------------------------
       The grid is rewritten every second, so no animation can simply "play".
       Each figure emits N stacked frames; only one is visible at a time via
       opacity. A step-end animation makes every frame hold for its slice and
       then switch, and --phase (a NEGATIVE delay derived from the session id)
       puts each figure at a deterministic point in the loop - so after every
       rebuild it resumes the frame it was on and the walk reads as continuous.
       Two stride frames plus a sit frame mean legs and arms actually change
       instead of the figure sliding sideways. */

    /* Muted clothing for the two unhappy states, like the reference sheet's
       greyed-out frames, while keeping the group colour readable. */
    .person-error .shirt { filter: saturate(0.45) brightness(0.82); }
    .person-sulk  .shirt { filter: saturate(0.3) brightness(0.7); }


    .bubble rect, .bubble path { stroke: #0f172a; stroke-width: 0.6; }
    .bubble-warn rect, .bubble-warn path { fill: #eab308; }
    .bubble-err  rect, .bubble-err  path { fill: #ef4444; }
    .bubble-stop rect, .bubble-stop path { fill: #f97316; }
    .bubble-mark { fill: #0f172a; font-size: 8.5px; font-weight: 800; text-anchor: middle; }

    .card-footer { margin-top: auto; padding-top: 10px; font-size: 0.7rem; color: #64748b; border-top: 1px solid #334155; }
    
    /* Sub-Agent Nested Styles & Collapsible Accordion */
    .sub-agents-container { margin-top: 12px; padding-top: 12px; border-top: 1px dashed #334155; }
    .sub-agents-details { width: 100%; }
    .sub-agents-summary { 
      font-size: 0.8rem; 
      font-weight: 600; 
      color: #94a3b8; 
      margin-bottom: 8px; 
      text-transform: uppercase; 
      letter-spacing: 0.05em; 
      cursor: pointer; 
      user-select: none;
      list-style: none;
      display: flex;
      align-items: center;
      gap: 6px;
    }
    .sub-agents-summary::-webkit-details-marker { display: none; }
    .sub-agents-summary:hover { color: #f8fafc; }
    .chevron { display: inline-block; font-size: 0.7rem; transition: transform 0.2s ease; color: #64748b; }
    .sub-agents-details[open] .chevron { transform: rotate(90deg); }
    .sub-agents-details:not([open]) .chevron { transform: rotate(0deg); }
    .sub-agents-list { margin-top: 8px; }

    /* Todos accordion */
    .todos-container { margin-top: 10px; padding-top: 10px; border-top: 1px dashed #334155; }
    .todos-details { width: 100%; }
    .todos-summary {
      font-size: 0.8rem;
      font-weight: 600;
      color: #94a3b8;
      margin-bottom: 8px;
      text-transform: uppercase;
      letter-spacing: 0.05em;
      cursor: pointer;
      user-select: none;
      list-style: none;
      display: flex;
      align-items: center;
      gap: 6px;
    }
    .todos-summary::-webkit-details-marker { display: none; }
    .todos-summary:hover { color: #f8fafc; }
    .todos-details[open] .chevron { transform: rotate(90deg); }
    .todos-details:not([open]) .chevron { transform: rotate(0deg); }
    .todos-list { margin-top: 6px; display: flex; flex-direction: column; gap: 4px; }
    .todo-row { display: flex; align-items: center; gap: 8px; font-size: 0.82rem; padding: 3px 4px; }
    .todo-icon { flex-shrink: 0; }
    .todo-text { flex: 1; word-break: break-word; }
    .todo-priority { font-size: 0.7rem; text-transform: uppercase; color: #64748b; flex-shrink: 0; }

    .sub-card { background: #0f172a; border-radius: 6px; border-left: 4px solid #64748b; padding: 10px 12px; margin-bottom: 8px; box-shadow: inset 0 2px 4px rgba(0,0,0,0.2); transition: all 0.3s ease; }
    .sub-card.status-white { border-left-color: #f3f4f6; }
    .sub-card.status-green { border-left-color: #22c55e; }
    .sub-card.status-red { border-left-color: #ef4444; }
    .sub-card.status-yellow { border-left-color: #eab308; }
    .sub-card.status-orange { border-left-color: #f97316; }
    .sub-card.status-skyblue { border-left-color: #38bdf8; }
    .sub-card.status-cyan { border-left-color: #22d3ee; }
    .sub-card.status-gray { border-left-color: #64748b; opacity: 0.65; }
    .sub-session-title { font-weight: 600; font-size: 0.95rem; line-height: 1.2; color: #e2e8f0; word-break: break-word; }
    .sub-session-subtitle { font-size: 0.8rem; color: #64748b; font-weight: 500; }

    .offline-box { background: #1e293b; padding: 24px; border-radius: 8px; text-align: center; width: 100%; grid-column: 1 / -1; }
    .offline-title { color: #f8fafc; font-weight: bold; font-size: 1.1rem; margin-bottom: 8px; }
    .offline-tip { color: #94a3b8; font-size: 0.9rem; }
    @media (max-width: 430px) {
      .grid { grid-template-columns: 1fr; }
      .card { width: 100%; }
    }
  </style>
</head>
<body>
  <h1>OpenCode Active Terminals Dashboard</h1>
  <div class="controls">
    <input id="filterInput" type="text" placeholder="Filter: title, agent, status..." />
    <div id="settingsWrap" class="settings-wrap">
      <button id="settingsButton" class="settings-button" type="button" title="Dashboard settings">&#9881;</button>
      <div id="settingsMenu" class="settings-menu">
        <div class="settings-section">
          <div class="settings-heading">View</div>
          <div class="settings-options">
            <button class="settings-option" type="button" data-setting="dashboardInfoMode" data-value="compact">Compact</button>
            <button class="settings-option" type="button" data-setting="dashboardInfoMode" data-value="standard">Normal</button>
            <button class="settings-option" type="button" data-setting="dashboardInfoMode" data-value="extended">Extended</button>
          </div>
        </div>
        <div class="settings-section">
          <div class="settings-heading">Grouping</div>
          <div class="settings-options">
            <button class="settings-option" type="button" data-setting="dashboardGrouping" data-value="status">Status</button>
            <button class="settings-option" type="button" data-setting="dashboardGrouping" data-value="directory">Directory</button>
            <button class="settings-option" type="button" data-setting="dashboardGrouping" data-value="label">Label</button>
            <button class="settings-option" type="button" data-setting="dashboardGrouping" data-value="none">None</button>
          </div>
        </div>
        <div class="settings-section">
          <div class="settings-heading">Alarms</div>
          <div class="settings-row"><span class="settings-row-label">Jobs</span><button class="settings-toggle" type="button" data-toggle="dashboardAlarmJobsDone">OFF</button></div>
          <div class="settings-row"><span class="settings-row-label">User request</span><button class="settings-toggle" type="button" data-toggle="dashboardAlarmUsers">OFF</button></div>
          <div class="settings-row"><span class="settings-row-label">Errors</span><button class="settings-toggle" type="button" data-toggle="dashboardAlarmErrors">OFF</button></div>
        </div>
        <div class="settings-section">
          <div class="settings-heading">Auto Folding</div>
          <div class="settings-row"><span class="settings-row-label">TODOS</span><button class="settings-toggle" type="button" data-toggle="dashboardAutoFoldTodos">ON</button></div>
          <div class="settings-row"><span class="settings-row-label">AGENTS</span><button class="settings-toggle" type="button" data-toggle="dashboardAutoFoldAgents">ON</button></div>
        </div>
      </div>
    </div>
  </div>
  <div id="content">
    <div id="grid" class="grid">Listening for active terminal heartbeats...</div>
  </div>
</body>
</html>`;
  }

  const server = http.createServer((req, res) => {
    // Presence from TUI sidebars: every open window announces the session it
    // currently views (with live title/model from the TUI client). Only fills
    // gaps Ã¢â‚¬â€ never touches status, timers or counters. Keeps cold-but-open
    // sessions visible; they purge 15s after the last window stops announcing.
    if (req.method === 'POST' && req.url === '/api/presence') {
      if (!tokenMatches(req)) {
        res.writeHead(401, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ ok: false, error: 'unauthorized' }));
        return;
      }
      let body = '';
      req.on('data', chunk => { body += chunk; });
      req.on('end', () => {
        try {
          const data = JSON.parse(body);
          if (!data.sessionId || !isSessionId(data.sessionId)) {
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ ok: false }));
            return;
          }
          const now = Date.now();
          const rawTitle = typeof data.title === 'string' ? data.title.trim() : '';
          // A window may announce a debug/placeholder title; never let it stick.
          const junkTitle = !rawTitle || /^DBG\b/.test(rawTitle) || rawTitle.startsWith('api=[');
          const title = !junkTitle && !isForkTitle(rawTitle) ? (cleanTitle(rawTitle) || rawTitle) : null;

          // "owner" er den session vinduet viser lige nu; "tabs" er de andre
          // faner der stÃ¥r Ã¥bne i samme vindue. Begge er Ã¥bne og skal pÃ¥
          // kortet - en fane du kan klikke tilbage til er ikke historik.
          // Ã‰t `openUntil` pr. session, fordi flere vinduer kan dele faner:
          // den lÃ¦ngste levetid vinder, sÃ¥ Ã©t lukket vindue ikke lukker et
          // faneblad som et andet vindue stadig har Ã¥bent.
          const markOpen = (sessionID) => {
            if (!isSessionId(sessionID)) return;
            const until = now + VIEWED_OPEN_MS;
            const known = activeSessions.get(sessionID);
            if (known) {
              if (typeof known.openUntil !== 'number' || known.openUntil < until) known.openUntil = until;
              return;
            }
            activeSessions.set(sessionID, {
              title: 'Active Terminal',
              agent: 'Build',
              model: 'Claude Haiku 4.5',
              parentId: null,
              status: 'waiting',
              startTime: now,
              statusChangedAt: now,
              lastHeartbeat: now,
              runningSince: null,
              lastRuntimeMs: 0,
              openUntil: until
            });
            log('PRESENCE', `Open session registered: ${shortId(sessionID)}`);
          };

          markOpen(data.owner);
          if (Array.isArray(data.tabs)) {
            for (const tab of data.tabs) markOpen(tab);
          }

          const rawModel = typeof data.model === 'string' && data.model ? data.model : null;
          const rawAgent = typeof data.agent === 'string' && data.agent ? data.agent : null;
          const rawDirectory = normalizeDirectory(data.directory);
          const existing = activeSessions.get(data.sessionId);
          if (existing) {
            if (title && (existing.title === 'Active Terminal' || existing.title === 'Sub-Agent Task' || existing.title === '')) existing.title = title;
            else if (title && title !== existing.title && !isForkTitle(existing.title)) existing.title = title;
            if (rawModel && (!existing.model || existing.model === 'Claude Haiku 4.5')) existing.model = formatModelName(rawModel);
            if (rawAgent && (!existing.agent || rawAgent !== existing.agent)) existing.agent = formatAgentName(rawAgent, !!existing.parentId);
            if (rawDirectory) existing.directory = rawDirectory;
            existing.lastHeartbeat = now;
          } else {
            activeSessions.set(data.sessionId, {
              title: title || 'Active Terminal',
              agent: rawAgent ? formatAgentName(rawAgent, false) : 'Build',
              model: rawModel ? formatModelName(rawModel) : 'Claude Haiku 4.5',
              directory: rawDirectory,
              parentId: null,
              status: 'waiting',
              startTime: now,
              statusChangedAt: now,
              lastHeartbeat: now,
              runningSince: null,
              lastRuntimeMs: 0
            });
            log('PRESENCE', `Viewed session announced: ${shortId(data.sessionId)} (${title || 'untitled'})`);
          }
          if (data.dbg === true || !presenceLoggedAt.has(data.sessionId) || now - presenceLoggedAt.get(data.sessionId) > 60000) {
            presenceLoggedAt.set(data.sessionId, now);
            try { fs.appendFileSync(presenceLogFile, `[${new Date().toISOString()}] PRESENCE ${data.sessionId} title=${title || existing?.title || '?'} inst=${data.instance || '?'} owner=${data.owner || '?'}\n`); } catch {}
          }
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ ok: true }));
        } catch (e) {
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ ok: false }));
        }
      });
      return;
    }
    if (req.method === 'POST' && req.url === '/api/heartbeat') {
      if (!tokenMatches(req)) {
        res.writeHead(401, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ ok: false, error: 'unauthorized' }));
        return;
      }
      let body = '';
      req.on('data', chunk => { body += chunk; });
      req.on('end', () => {
        try {
          const data = JSON.parse(body);

          if (data.sessionId && isSessionId(data.sessionId)) {
            const now = Date.now();
            const reportTimestamp = typeof data.timestamp === 'number' && isFinite(data.timestamp) ? data.timestamp : now;
            const existing = activeSessions.get(data.sessionId);

            if (existing && typeof existing.lastReportTimestamp === 'number' && reportTimestamp < existing.lastReportTimestamp) {
              res.writeHead(200, { 'Content-Type': 'application/json' });
              res.end(JSON.stringify({ ok: true }));
              return;
            }

            const lastLog = serverLastLogs.get(data.sessionId) || { time: 0, status: '', title: '' };

            const statusChanged = data.status !== lastLog.status;
            const titleChanged = data.title !== lastLog.title;
            const logTimeElapsed = now - lastLog.time;

            // Console log ONLY when status/title changes or every 10 seconds
            if (statusChanged || titleChanged || logTimeElapsed >= 10000) {
              log('HEARTBEAT-IN', `[${data.agent || 'Main'}] session=${shortId(data.sessionId)} status=${data.status} title="${data.title}" parent=${data.parentId ? shortId(data.parentId) : 'none'}`);
              serverLastLogs.set(data.sessionId, { time: now, status: data.status, title: data.title });
            }

            if (data.parentId && isSessionId(data.parentId) && !isForkTitle(data.title) && !isForkTitle(cleanTitle(data.title))) {
              rememberSubAgentMetrics(data.parentId, data.sessionId, data);
            }

            if (data.status === 'closed') {
              log('CLOSE', `Terminal closed signal received: ${shortId(data.sessionId)}`);
              if (data.remove === true) {
                if (!data.parentId || !isSessionId(data.parentId)) forgetSubAgentMetricsForParent(data.sessionId);
                activeSessions.delete(data.sessionId);
                res.writeHead(200, { 'Content-Type': 'application/json' });
                res.end(JSON.stringify({ ok: true }));
                return;
              }
              if (existing) {
                const wasRunning = existing.status === 'running';
                const runningSince = existing.runningSince || existing.statusChangedAt || existing.startTime || now;
                if (wasRunning) {
                  existing.lastRuntimeMs = Math.max(0, now - runningSince);
                }
                existing.status = 'closed';
                existing.runningSince = null;
                existing.lastHeartbeat = now;
                existing.lastReportTimestamp = reportTimestamp;
                existing.statusChangedAt = now;
                if (!existing.closedAt) existing.closedAt = now;
              } else {
                activeSessions.set(data.sessionId, {
                  title: cleanTitle(data.title) || 'Closed Terminal',
                  agent: data.agent || 'Build',
                  model: data.model || 'Claude Haiku 4.5',
                  parentId: (data.parentId && isSessionId(data.parentId)) ? data.parentId : null,
                  status: 'closed',
                  startTime: now,
                  statusChangedAt: now,
                  closedAt: now,
                  lastHeartbeat: now,
                  lastReportTimestamp: reportTimestamp,
                  runningSince: null,
                  lastRuntimeMs: 0,
                  cost: data.cost,
                  tokens: data.tokens,
                  error: data.error,
                  retryInfo: data.retryInfo,
                  msgCount: data.msgCount || 0,
                  compactionCount: data.compactionCount || 0,
                  todos: data.todos
                });
              }
              res.writeHead(200, { 'Content-Type': 'application/json' });
              res.end(JSON.stringify({ ok: true }));
              return;
            }

            if (data.parentId && isSessionId(data.parentId) && !activeSessions.has(data.parentId)) {
              activeSessions.set(data.parentId, {
                title: 'Active Main Terminal',
                agent: 'Build',
                model: 'Claude Haiku 4.5',
                // Keep an existing openUntil: this placeholder is only created
                // when the parent was unknown, but if presence already marked
                // it open we must not reset that to "not open".
                openUntil: (activeSessions.get(data.parentId) || {}).openUntil,
                parentId: null,
                status: 'running',
                startTime: now,
                statusChangedAt: now,
                lastHeartbeat: now,
                lastReportTimestamp: reportTimestamp,
                runningSince: now,
                lastRuntimeMs: 0
              });
              log('PARENT-AUTO', `Created parent placeholder: ${shortId(data.parentId)}`);
            }

            let validParentId = (data.parentId && isSessionId(data.parentId)) ? data.parentId : null;
            // Forks must never be nested - ignore any parentId if title indicates a fork
            if (validParentId && (isForkTitle(data.title) || isForkTitle(cleanTitle(data.title)))) {
              validParentId = null;
            }
            const isNew = !activeSessions.has(data.sessionId);
            const current = activeSessions.get(data.sessionId);
            
            let rawTitle = cleanTitle(data.title) || (validParentId ? 'Sub-Agent Task' : 'Active Terminal');
            // Final fork guard after title resolution - forks are always top-level
            if (isForkTitle(rawTitle) || isForkTitle(data.title) || isForkTitle(current?.title)) {
              validParentId = null;
            }
            if (current && current.title && current.title !== 'Active Terminal' && current.title !== 'Sub-Agent Task' && (rawTitle === 'Active Terminal' || rawTitle === 'Sub-Agent Task')) {
              rawTitle = current.title;
            }

            const incomingStatus = data.status;
            const incomingError = Object.prototype.hasOwnProperty.call(data, 'error') ? data.error : (current ? current.error : undefined);
            const normalizedStatus = incomingStatus === 'waiting' && isInterruptedError(incomingError) ? 'interrupted' : incomingStatus;
            const prevStatus = current ? current.status : null;
            const isStatusChanged = prevStatus !== normalizedStatus;
            const statusChangedAt = isStatusChanged ? now : (current ? current.statusChangedAt : now);
            const runningSince = (() => {
              if (normalizedStatus === 'running') {
                if (prevStatus === 'running' && current && current.runningSince) return current.runningSince;
                return now;
              }
              return null;
            })();
            const lastRuntimeMs = (() => {
              if (!current) return 0;
              if (prevStatus === 'running' && normalizedStatus !== 'running') {
                const startedAt = current.runningSince || current.statusChangedAt || current.startTime || now;
                return Math.max(0, now - startedAt);
              }
              return current.lastRuntimeMs || 0;
            })();

            const costState = (() => {
              if (typeof data.cost !== 'number' || !isFinite(data.cost)) {
                return {
                  cost: current ? current.cost : undefined,
                  rawCost: current ? current.rawCost : undefined,
                  baseCost: current ? current.baseCost : undefined
                };
              }
              if (data.observedUsage === true) {
                return { cost: data.cost, rawCost: undefined, baseCost: undefined };
              }
              const rawCost = current && typeof current.rawCost === 'number' ? Math.max(current.rawCost, data.cost) : data.cost;
              const baseCost = current && typeof current.baseCost === 'number' ? current.baseCost : rawCost;
              return { cost: Math.max(0, rawCost - baseCost), rawCost: rawCost, baseCost: baseCost };
            })();

            const tokenState = {
              tokens: current ? current.tokens : undefined,
              rawTokens: current ? current.rawTokens : undefined,
              baseTokens: current ? current.baseTokens : undefined
            };

            const nextSession = {
              title: rawTitle,
              // Presence (TUI) may have set a real model/agent: default-valued
              // heartbeats must not clobber them. Real reporter values still win.
              agent: (data.agent && data.agent !== 'Build' && data.agent !== 'General Task') ? data.agent : (current && current.agent ? current.agent : (data.agent || 'Build')),
              model: (data.model && data.model !== 'Claude Haiku 4.5') ? data.model : (current && current.model ? current.model : (data.model || 'Claude Haiku 4.5')),
              // Presence owns the directory: it reads it from the live TUI state.
              // A heartbeat that omits it must not wipe what presence established.
              directory: (current && current.directory) || null,
              // Same for openUntil: this handler REPLACES the whole session
              // object, so a field not listed here is dropped. Dropping it made
              // open tabs blink out between presence pulses, because the card
              // is filtered on openUntil and the next heartbeat wiped it.
              openUntil: current ? current.openUntil : undefined,
              parentId: validParentId,
              status: normalizedStatus,
              alarmEligible: normalizedStatus === 'user_response' && data.alarmEligible === true,
              startTime: current ? current.startTime : now,
              statusChangedAt: statusChangedAt,
              closedAt: null,
              lastHeartbeat: now,
              // Preserved across heartbeats: a heartbeat is not activity.
              lastActivityAt: current && typeof current.lastActivityAt === 'number'
                ? current.lastActivityAt
                : (now),
              lastReportTimestamp: reportTimestamp,
              runningSince: runningSince,
              lastRuntimeMs: lastRuntimeMs,
              cost: costState.cost,
              rawCost: costState.rawCost,
              baseCost: costState.baseCost,
              tokens: tokenState.tokens,
              rawTokens: tokenState.rawTokens,
              baseTokens: tokenState.baseTokens,
              error: incomingError,
              retryInfo: data.retryInfo || (current ? current.retryInfo : undefined),
              msgCount: (typeof data.msgCount === 'number') ? data.msgCount : (current ? current.msgCount : 0),
              compactionCount: (typeof data.compactionCount === 'number') ? data.compactionCount : (current ? current.compactionCount : 0),
              todos: data.todos || (current ? current.todos : undefined)
            };

            activeSessions.set(data.sessionId, nextSession);
            if (validParentId) rememberSubAgentMetrics(validParentId, data.sessionId, nextSession);

            if (isNew) {
              log('HEARTBEAT-NEW', `>>> NEW SESSION CONNECTED: ${rawTitle} (${shortId(data.sessionId)})${validParentId ? ` [Sub-agent of ${shortId(validParentId)}]` : ''}`);
            }
          }
        } catch (e) {}
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ ok: true }));
      });
    } else if (req.url === '/api/version') {
      res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ ok: true, version: PLUGIN_VERSION }));
    } else if (req.url === '/api/data') {
      const cards = getCards();
      res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify(cards));
    } else {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(generateDashboardHTML());
    }
  });

  server.on('error', (e) => {
    log('SERVER-ERR', String((e && e.message) || e));
    process.exit(1);
  });

  server.listen(DASHBOARD_PORT, '0.0.0.0', () => {
    log('INIT', `Ã°Å¸Å¡â‚¬ Server active at http://localhost:${DASHBOARD_PORT}`);
  });
}

if (process.argv[1] && fileURLToPath(import.meta.url) === path.resolve(process.argv[1])) {
  startServer();
}
