import http from "http";
import https from "https";
import fs from "fs";
import path from "path";
import crypto, { X509Certificate } from "crypto";
import dns from "node:dns";
import { WebSocketServer } from "ws";
import { generate } from "selfsigned";

const VERSION = "0.2.0";
const HOST = "::";
const PORT = 8765;
const PUBLIC_HOST = "cloudlinkv4.duckdns.org"; // Change it to your domain
const USE_TLS = true;

const CERT_KEY = path.join(process.cwd(), "cloudlinkv4.duckdns.org-key.pem"); // change it to your certificate file
const CERT_CRT = path.join(process.cwd(), "cloudlinkv4.duckdns.org-crt.pem"); // change it to your key file

const clients = new Map();
const userMap = new Map();
const uuidMap = new Map();
const globalVars = new Map();
const clientRooms = new Map();
const blockedIPs = new Set();
const customCmds = new Map();
const usedIds = new Set();

const motd = { text: "Welcome to the Cloudlink Bridge!", enabled: true };
let globalMsg = "";

function mkUUID() { return crypto.randomUUID(); }
function log() {}
function safeSend(ws, data) {
  if (!ws || ws._closedManually) return;
  if (ws.readyState !== ws.OPEN) return;
  try { ws.send(data); } catch {}
}
function sendJson(ws, obj) { safeSend(ws, JSON.stringify(obj)); }

const STATUS_MAP = {
  OK: [100, "I:100 | OK", "OK"],
  Syntax: [101, "E:101 | Syntax", "Syntax"],
  Datatype: [102, "E:102 | Datatype", "Datatype"],
  IDNotFound: [103, "E:103 | ID Not Found", "ID Not Found"],
  InternalServerError: [104, "E:104 | Internal Server Error", "Internal Server Error"],
  RateLimit: [106, "E:106 | Rate Limit", "Rate Limit"],
  TooLarge: [107, "E:107 | Too Large", "Too Large"],
  EmptyPacket: [109, "E:109 | Empty Packet", "Empty Packet"],
  IDConflict: [110, "E:110 | ID Conflict", "ID Conflict"],
  IDSet: [111, "E:111 | ID Set", "ID Set"],
  Refused: [115, "E:115 | Refused", "Refused"],
  IDRequired: [116, "E:116 | ID Required", "ID Required"],
  Invalid: [118, "E:118 | Invalid", "Invalid"],
};

function sendStatus(ws, code, listener, valPayload) {
  const [id, str, pretty] = STATUS_MAP[code] || STATUS_MAP.Invalid;
  const p = { cmd: "statuscode", val: pretty, code: str, code_id: id };
  if (listener) p.listener = listener;
  if (valPayload !== undefined) p.val = valPayload;
  safeSend(ws, JSON.stringify(p));
}

function getRooms(ws) {
  const r = clientRooms.get(ws);
  return r && r.size ? [...r] : ["default"];
}
function buildRoomUlist(room) {
  const arr = [];
  const names = [];
  for (const [ws, c] of clients) {
    if (!c.username) continue;
    if (getRooms(ws).includes(room)) {
      arr.push({ id: c.snowflake, username: c.username, uuid: c.uuid });
      names.push(c.username);
    }
  }
  return { arr, str: names.length ? names.join(";") + ";" : "" };
}
function sendUlist(ws) {
  for (const room of getRooms(ws)) {
    const { arr, str } = buildRoomUlist(room);
    safeSend(ws, JSON.stringify({ cmd: "ulist", val: str }));
    safeSend(ws, JSON.stringify({ cmd: "ulist", mode: "set", val: arr, rooms: room }));
  }
}
function broadcastAll(raw) {
  for (const [ws] of clients) safeSend(ws, raw);
}
function mkOrigin(c) {
  if (!c.username) return c.ip;
  return { id: c.snowflake, username: c.username, uuid: c.uuid };
}
function findClient(idStr) {
  if (!idStr) return null;
  const s = String(idStr).trim();
  if (userMap.has(s)) return userMap.get(s);
  if (uuidMap.has(s)) return uuidMap.get(s);
  for (const [ws, c] of clients) if (c.snowflake === s) return ws;
  return null;
}
function valOK(v) {
  if (typeof v === "string") return v.length <= 50000;
  if (v !== null && typeof v === "object") {
    try { return JSON.stringify(v).length <= 50000; } catch { return false; }
  }
  return true;
}
function nameOK(n) {
  return typeof n === "string" && n.length > 0 && n.length <= 100;
}
function rateLimit(c) {
  const now = Date.now();
  c.rl = c.rl || [];
  while (c.rl.length && now - c.rl[0] > 1000) c.rl.shift();
  if (c.rl.length >= 100) return true;
  c.rl.push(now);
  return false;
}
function mkClientId() {
  let id;
  do {
    id = "";
    id += Math.floor(Math.random() * 9) + 1;
    for (let i = 1; i < 19; i++) id += Math.floor(Math.random() * 10);
  } while (usedIds.has(id));
  usedIds.add(id);
  return id;
}

function normalizeIp(raw, { keepMapped = false } = {}) {
  if (raw === undefined || raw === null) return null;
  let ip = String(raw).trim();
  if (!ip || ip.toLowerCase() === "unknown") return null;
  if (ip.startsWith("[") && ip.includes("]")) ip = ip.slice(1, ip.indexOf("]"));
  const zone = ip.indexOf("%");
  if (zone !== -1) ip = ip.slice(0, zone);
  if (!keepMapped && ip.startsWith("::ffff:")) ip = ip.slice(7);
  return ip;
}
function parseForwardedHeader(value) {
  const ips = [];
  if (!value) return ips;
  for (const part of String(value).split(",")) {
    for (const piece of part.split(";")) {
      const s = piece.trim();
      if (!s.toLowerCase().startsWith("for=")) continue;
      let v = s.slice(4).trim();
      if ((v.startsWith('"') && v.endsWith('"')) || (v.startsWith("'") && v.endsWith("'"))) v = v.slice(1, -1);
      if (v.toLowerCase().startsWith("for=")) v = v.slice(4);
      ips.push(v);
    }
  }
  return ips;
}
function isIPv4(ip) {
  if (!ip || !/^(\d{1,3}\.){3}\d{1,3}$/.test(ip)) return false;
  return ip.split(".").every((o) => {
    const n = Number(o);
    return n >= 0 && n <= 255;
  });
}
function isIPv6(ip) { return Boolean(ip && ip.includes(":") && !isIPv4(ip)); }
function isPublicIPv4(ip) {
  if (!isIPv4(ip)) return false;
  const [a, b] = ip.split(".").map(Number);
  if (a === 10) return false;
  if (a === 172 && b >= 16 && b <= 31) return false;
  if (a === 192 && b === 168) return false;
  if (a === 127) return false;
  if (a === 0) return false;
  if (a >= 224) return false;
  return true;
}
function isPublicIPv6(ip) {
  if (!isIPv6(ip)) return false;
  const lower = ip.toLowerCase();
  if (lower === "::1") return false;
  if (lower.startsWith("fe80:")) return false;
  if (lower.startsWith("fc") || lower.startsWith("fd")) return false;
  return true;
}

function collectClientIps(req, extra = null) {
  const v4s = new Set();
  const v6s = new Set();
  const add = (raw) => {
    const n = normalizeIp(raw);
    if (!n) return;
    if (isIPv4(n)) v4s.add(n);
    else if (isIPv6(n)) v6s.add(n);
  };
  const rawRemote = req.socket?.remoteAddress;
  const family = req.socket?.remoteFamily;

  if (rawRemote && family === "IPv6" && !String(rawRemote).startsWith("::ffff:")) add(rawRemote);
  else if (rawRemote) add(rawRemote);

  const headers = req.headers || {};
  for (const key of ["cf-connecting-ip", "true-client-ip", "x-real-ip", "x-client-ip", "x-forwarded-for", "forwarded-for", "forwarded"]) {
    const v = headers[key];
    if (!v) continue;
    if (key === "forwarded" || key === "forwarded-for") {
      parseForwardedHeader(v).forEach(add);
      continue;
    }
    String(v).split(",").map((s) => s.trim()).forEach(add);
  }

  if (extra && typeof extra === "object") {
    add(extra.ipv4); add(extra.ipv6); add(extra.ip);
    if (extra.val && typeof extra.val === "object") {
      add(extra.val.ipv4); add(extra.val.ipv6); add(extra.val.ip);
    }
  }
  return { v4s: [...v4s], v6s: [...v6s], rawRemote, family };
}
function selectIpByUserRules(bestV4, bestV6, hasV4, hasV6) {
  if (hasV4 && !hasV6) return bestV4 || "unknown";
  if ((hasV4 && hasV6) || (!hasV4 && hasV6)) return bestV6 || bestV4 || "unknown";
  return bestV4 || bestV6 || "unknown";
}
function pickClientIp(req, extra = null) {
  const collected = collectClientIps(req, extra);
  const v4s = [...collected.v4s];
  const v6s = [...collected.v6s];
  const { rawRemote, family } = collected;
  const pubV4 = v4s.filter(isPublicIPv4);
  const pubV6 = v6s.filter(isPublicIPv6);
  const hasV4 = v4s.length > 0;
  const hasV6 = v6s.length > 0;
  const bestV4 = pubV4[0] || v4s[0] || null;
  const bestV6 = pubV6[0] || v6s[0] || null;
  const selected = selectIpByUserRules(bestV4, bestV6, hasV4, hasV6);
  return { selected, ipv4: bestV4, ipv6: bestV6, hasV4, hasV6, debug: { rawRemote: rawRemote || "", family: family || "", v4s, v6s, hasV4, hasV6, selected } };
}
function logClientIp() {}
function updateClientIp(ws, req, extra = null, reason = "update") {
  const c = clients.get(ws);
  if (!c) return "unknown";
  const picked = pickClientIp(req, extra);
  c.ip = picked.selected;
  c.ipv4 = picked.ipv4;
  c.ipv6 = picked.ipv6;
  c.hasIpv4 = picked.hasV4;
  c.hasIpv6 = picked.hasV6;
  logClientIp(picked, reason);
  return picked.selected;
}
function sendClientIp(ws, c) {
  sendJson(ws, { cmd: "client_ip", val: String(c.ip || "unknown") });
}
function mergeReportedExtra(c, report) {
  if (!report) return false;
  c.reportedExtra = c.reportedExtra || {};
  let changed = false;
  const applyOne = (raw) => {
    const n = normalizeIp(raw);
    if (!n) return;
    if (isIPv4(n)) { c.reportedExtra.ipv4 = n; changed = true; }
    else if (isIPv6(n)) { c.reportedExtra.ipv6 = n; changed = true; }
  };
  if (typeof report === "string") { applyOne(report); return changed; }
  if (typeof report !== "object") return false;
  if (report.ipv4) applyOne(report.ipv4);
  if (report.ipv6) applyOne(report.ipv6);
  if (report.ip) applyOne(report.ip);
  if (report.val !== undefined && report.val !== null) {
    if (typeof report.val === "object") {
      if (report.val.ipv4) applyOne(report.val.ipv4);
      if (report.val.ipv6) applyOne(report.val.ipv6);
      if (report.val.ip) applyOne(report.val.ip);
    } else {
      applyOne(report.val);
    }
  }
  return changed;
}
function applyReportedIps(ws, report, reason = "report") {
  const c = clients.get(ws);
  if (!c || !mergeReportedExtra(c, report)) return;
  updateClientIp(ws, ws._req || {}, c.reportedExtra, reason);
}
async function resolvePublicIpv6FromHostname(hostname) {
  if (!hostname) return null;
  try { const v6s = await dns.promises.resolve6(String(hostname)); return v6s.find(isPublicIPv6) || null; }
  catch { return null; }
}
async function probeClientIpv6(ipv4) {
  if (!ipv4 || !isPublicIPv4(ipv4)) return null;
  try {
    const r = await fetch(`https://ipinfo.io/${ipv4}/json`, { headers: { Accept: "application/json" }, signal: AbortSignal.timeout(4000) });
    if (r.ok) {
      const j = await r.json();
      const fromHost = await resolvePublicIpv6FromHostname(j.hostname);
      if (fromHost) return fromHost;
    }
  } catch {}
  try {
    const r = await fetch(`http://ip-api.com/json/${ipv4}?fields=status,reverse,query`, { signal: AbortSignal.timeout(4000) });
    if (r.ok) {
      const j = await r.json();
      if (j.reverse) {
        const fromHost = await resolvePublicIpv6FromHostname(j.reverse);
        if (fromHost) return fromHost;
      }
    }
  } catch {}
  try {
    const hosts = await dns.promises.reverse(ipv4);
    for (const host of hosts) {
      const v6 = await resolvePublicIpv6FromHostname(host);
      if (v6) return v6;
    }
  } catch {}
  return null;
}
async function finalizeClientIp(ws, reason = "final") {
  const c = clients.get(ws);
  if (!c) return;
  const req = ws._req || {};
  let picked = pickClientIp(req, c.reportedExtra);
  if (!picked.hasV6 && picked.ipv4 && isPublicIPv4(picked.ipv4)) {
    const v6 = await probeClientIpv6(picked.ipv4);
    if (v6) {
      mergeReportedExtra(c, { ipv4: picked.ipv4, ipv6: v6 });
      picked = pickClientIp(req, c.reportedExtra);
    }
  }
  c.ip = picked.selected;
  c.ipv4 = picked.ipv4;
  c.ipv6 = picked.ipv6;
  c.hasIpv4 = picked.hasV4;
  c.hasIpv6 = picked.hasV6;
  sendClientIp(ws, c);
}

async function doHandshake(ws, c) {
  sendJson(ws, { cmd: "direct", val: { cmd: "vers", val: VERSION } });
  sendJson(ws, { cmd: "server_version", val: VERSION });
  if (motd.enabled && motd.text) {
    sendJson(ws, { cmd: "direct", val: { cmd: "motd", val: motd.text } });
    sendJson(ws, { cmd: "motd", val: motd.text });
  }
  sendJson(ws, { cmd: "client_obj", val: { id: c.snowflake, uuid: c.uuid } });
  void finalizeClientIp(ws, "handshake");
  sendUlist(ws);
  for (const [name, val] of globalVars) sendJson(ws, { cmd: "gvar", val, name });
}
function cmdSetid(ws, c, val, lsn) {
  if (c.username) return sendStatus(ws, "IDSet", lsn);
  const u = String(val ?? "").trim();
  if (!u) return sendStatus(ws, "Datatype", lsn);
  if (u.length > 20) return sendStatus(ws, "TooLarge", lsn);
  if (userMap.has(u)) return sendStatus(ws, "IDConflict", lsn);
  c.username = u;
  userMap.set(u, ws);
  uuidMap.set(c.uuid, ws);
  sendStatus(ws, "OK", lsn || "username_cfg", { id: c.snowflake, username: u, uuid: c.uuid });
  for (const room of getRooms(ws)) {
    const { arr, str } = buildRoomUlist(room);
    for (const [ow] of clients) {
      if (getRooms(ow).includes(room)) {
        safeSend(ow, JSON.stringify({ cmd: "ulist", val: str }));
        safeSend(ow, JSON.stringify({ cmd: "ulist", mode: "set", val: arr, rooms: room }));
      }
    }
  }
}
function cmdGmsg(ws, c, val, lsn) {
  if (!valOK(val)) return sendStatus(ws, "TooLarge", lsn);
  globalMsg = typeof val === "string" ? val : JSON.stringify(val);
  broadcastAll(JSON.stringify({ cmd: "gmsg", val, origin: mkOrigin(c) }));
  sendStatus(ws, "OK", lsn);
}
function cmdPmsg(ws, c, val, id, lsn) {
  if (!c.username) return sendStatus(ws, "IDRequired", lsn);
  if (!id) return sendStatus(ws, "Syntax", lsn);
  const tw = findClient(id);
  if (!tw) return sendStatus(ws, "IDNotFound", lsn);
  if (!valOK(val)) return sendStatus(ws, "TooLarge", lsn);
  sendJson(tw, { cmd: "pmsg", val, origin: mkOrigin(c), originID: c.username });
  sendStatus(ws, "OK", lsn);
}
function cmdGvar(ws, c, val, name, lsn) {
  if (!nameOK(name)) return sendStatus(ws, "Syntax", lsn);
  if (!valOK(val)) return sendStatus(ws, "TooLarge", lsn);
  globalVars.set(name, val);
  broadcastAll(JSON.stringify({ cmd: "gvar", val, name, origin: mkOrigin(c) }));
  sendStatus(ws, "OK", lsn);
}
function cmdPvar(ws, c, val, id, name, lsn) {
  if (!c.username) return sendStatus(ws, "IDRequired", lsn);
  if (!nameOK(name)) return sendStatus(ws, "Syntax", lsn);
  const tw = findClient(id);
  if (!tw) return sendStatus(ws, "IDNotFound", lsn);
  if (!valOK(val)) return sendStatus(ws, "TooLarge", lsn);
  sendJson(tw, { cmd: "pvar", val, name, origin: mkOrigin(c), originID: c.username });
  sendStatus(ws, "OK", lsn);
}
function cmdDirect(ws, c, val, id, lsn) {
  if (val && typeof val === "object" && val.cmd === "ip") {
    applyReportedIps(ws, val, "direct-ip");
    sendStatus(ws, "OK", lsn);
    void finalizeClientIp(ws, "direct-ip");
    return;
  }
  if (val && typeof val === "object" && val.cmd) {
    if (customCmds.has(String(val.cmd))) {
      try { customCmds.get(String(val.cmd))(ws, c, val.val ?? "", id); }
      catch { sendStatus(ws, "InternalServerError", lsn); }
      return;
    }
    sendStatus(ws, "OK", lsn);
    return;
  }
  const pkt = JSON.stringify({ cmd: "direct", val, origin: mkOrigin(c), originID: c.username || c.ip });
  if (id) {
    const tw = findClient(id);
    if (!tw) return sendStatus(ws, "IDNotFound", lsn);
    safeSend(tw, pkt);
  } else {
    broadcastAll(pkt);
  }
  sendStatus(ws, "OK", lsn);
}
function cmdLink(ws, c, val, lsn) {
  const rooms = Array.isArray(val) ? val.map(String).filter(Boolean) : typeof val === "string" ? val.split(";").map(s => s.trim()).filter(Boolean) : ["default"];
  clientRooms.set(ws, new Set(rooms.length ? rooms : ["default"]));
  sendUlist(ws);
  sendStatus(ws, "OK", lsn || "link");
}
function cmdUnlink(ws, c, val, lsn) {
  clientRooms.delete(ws);
  sendStatus(ws, "OK", lsn || "unlink");
}

function setupWebSocket(server) {
  const wss = new WebSocketServer({ server, perMessageDeflate: false });
  wss.on("connection", (ws, req) => {
    void (async () => {
      ws._req = req;
      const picked = pickClientIp(req);
      if (blockedIPs.has(picked.selected) || (picked.ipv4 && blockedIPs.has(picked.ipv4)) || (picked.ipv6 && blockedIPs.has(picked.ipv6))) {
        try { ws.close(1008, "Blocked"); } catch {}
        return;
      }
      const c = {
        ip: picked.selected, ipv4: picked.ipv4, ipv6: picked.ipv6, hasIpv4: picked.hasV4, hasIpv6: picked.hasV6,
        reportedExtra: null, username: null, clientType: "native", rl: [], snowflake: mkClientId(), uuid: mkUUID(), lastMsg: 0,
      };
      clients.set(ws, c);
      await doHandshake(ws, c);
    })().catch((err) => log("[connect-error]", err?.message || err));

    ws.on("message", raw => {
      const c2 = clients.get(ws);
      if (!c2) return;
      const rawStr = Buffer.isBuffer(raw) ? raw.toString("utf8") : String(raw);
      let pkt;
      try { pkt = JSON.parse(rawStr); } catch { return; }
      if (!pkt || typeof pkt !== "object") return sendStatus(ws, "Datatype");
      if (!pkt.cmd) return sendStatus(ws, "EmptyPacket");
      if (rateLimit(c2)) return sendStatus(ws, "RateLimit");
      const { cmd, val, id, name, t, listener: lsn } = pkt;

      switch (String(cmd)) {
        case "handshake":
          mergeReportedExtra(c2, val);
          sendStatus(ws, "OK", lsn || "handshake_cfg");
          void finalizeClientIp(ws, "handshake-rx");
          return;
        case "report_ip":
          applyReportedIps(ws, typeof val === "object" ? val : { val }, "report_ip");
          sendStatus(ws, "OK", lsn);
          void finalizeClientIp(ws, "report_ip");
          return;
        case "setid":
        case "setusername":
        case "username":
        case "set_username": return cmdSetid(ws, c2, val, lsn);
        case "gmsg":
        case "setgmsg":
        case "message":
        case "global_msg": return cmdGmsg(ws, c2, val, lsn);
        case "pmsg":
        case "sendto":
        case "sendmsg":
        case "private_msg": return cmdPmsg(ws, c2, val, id, lsn);
        case "gvar":
        case "setgvar":
        case "global_var": return cmdGvar(ws, c2, val, name, lsn);
        case "pvar":
        case "setpvar":
        case "private_var": return cmdPvar(ws, c2, val, id, name, lsn);
        case "direct":
        case "send":
        case "data": return cmdDirect(ws, c2, val, id, lsn);
        case "link":
        case "linktorooms":
        case "join": return cmdLink(ws, c2, val, lsn);
        case "unlink":
        case "unlinkfromrooms":
        case "leave": return cmdUnlink(ws, c2, val, lsn);
        case "ping":
        case "keepalive":
          sendStatus(ws, "OK", lsn);
          return sendJson(ws, typeof t === "number" ? { cmd: "pong", t, server: Date.now() } : { cmd: "pong", server: Date.now() });
        case "getulist":
        case "ulist":
        case "get_ulist":
        case "online":
          sendStatus(ws, "OK", lsn);
          return sendUlist(ws);
        case "gmsg_get":
        case "get_gmsg":
          sendStatus(ws, "OK", lsn);
          return sendJson(ws, { cmd: "gmsg", val: globalMsg });
        case "client_ip":
        case "get_client_ip":
        case "get_ip":
        case "my_ip":
          mergeReportedExtra(c2, val);
          sendStatus(ws, "OK", lsn);
          void finalizeClientIp(ws, "request");
          return;
        case "gvar_get":
        case "get_gvar":
          if (name && globalVars.has(name)) {
            sendStatus(ws, "OK", lsn);
            sendJson(ws, { cmd: "gvar", val: globalVars.get(name), name });
          } else {
            sendStatus(ws, "IDNotFound", lsn);
          }
          return;
        default:
          if (customCmds.has(String(cmd))) {
            try { customCmds.get(String(cmd))(ws, c2, val, id); } catch { sendStatus(ws, "InternalServerError", lsn); }
          } else sendStatus(ws, "Invalid", lsn);
      }
    });

    ws.on("close", () => {
      const c2 = clients.get(ws);
      if (!c2) return;
      const departedUsername = c2.username;
      const departedRooms = getRooms(ws);
      if (c2.username) userMap.delete(c2.username);
      if (c2.uuid) uuidMap.delete(c2.uuid);
      usedIds.delete(c2.snowflake);
      clientRooms.delete(ws);
      clients.delete(ws);
      if (departedUsername) {
        for (const room of departedRooms) {
          const { arr, str } = buildRoomUlist(room);
          for (const [ow] of clients) {
            if (getRooms(ow).includes(room)) {
              safeSend(ow, JSON.stringify({ cmd: "ulist", val: str }));
              safeSend(ow, JSON.stringify({ cmd: "ulist", mode: "set", val: arr, rooms: room }));
            }
          }
        }
      }
    });
  });
  return wss;
}

function httpHandler(req, res) {
  const scheme = USE_TLS ? "wss" : "ws";
  const host = req.headers.host || (HOST + ":" + PORT);
  if (req.url.startsWith("/status")) {
    const connectedIps = [...clients.values()].map(c => ({ ip: c.ip || "unknown", username: c.username || "", id: c.snowflake, uuid: c.uuid }));
    const data = JSON.stringify({
      version: VERSION, pid: process.pid, uptime: Math.floor(process.uptime()), tls: USE_TLS, clients: clients.size,
      users: userMap.size, globalVars: globalVars.size, userList: [...userMap.keys()], connectedIps, motd: motd.enabled ? motd.text : "",
      motdEnabled: motd.enabled, endpoint: scheme + "://" + host,
    });
    res.writeHead(200, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store, no-cache, must-revalidate, proxy-revalidate", "Pragma": "no-cache", "Expires": "0", "Access-Control-Allow-Origin": "*" });
    return res.end(data);
  }

  const html = `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width,initial-scale=1" />
  <meta http-equiv="Content-Security-Policy" content="default-src 'self'; script-src 'self' 'unsafe-inline'; connect-src 'self' ws: wss:; style-src 'self' 'unsafe-inline'; img-src 'self' data:; object-src 'none'; base-uri 'none'; frame-ancestors 'none'">
  <title>CloudLink V4 Server</title>
  <style>
    *{box-sizing:border-box;margin:0;padding:0}
    body{
      background:#0d1117;
      color:#e6edf3;
      font-family:Consolas,"DejaVu Sans Mono","Lucida Console",monospace;
      padding:32px;
      min-height:100vh;
      position:relative;
    }
    h1{color:#58a6ff;font-size:1.5rem;margin-bottom:8px}
    .badge{display:inline-block;padding:2px 10px;border-radius:12px;font-size:.75rem;font-weight:700;background:#1a4731;color:#3fb950}
    .card{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:20px;margin:16px 0}
    .row{display:flex;justify-content:space-between;gap:16px;padding:6px 0;border-bottom:1px solid #21262d}
    .row:last-child{border-bottom:none}
    .label{color:#8b949e}
    .value{color:#e6edf3;font-weight:700;word-break:break-word;text-align:right;max-width:70%}
    .users{margin-top:8px;display:flex;flex-wrap:wrap;gap:6px}
    .user{background:#21262d;padding:2px 10px;border-radius:12px;font-size:.85rem;color:#79c0ff}
    .empty{color:#8b949e;font-size:.85rem;font-style:italic}
    .wss{color:#3fb950;word-break:break-all}
    .pulse{animation:blink 1s step-start infinite}
    @keyframes blink{50%{opacity:.4}}

    .lang-box{
      position:absolute;
      top:16px;
      right:16px;
      z-index:9999;
      user-select:none;
      min-width:180px;
    }
    .lang-box > summary{
      cursor:pointer;
      list-style:none;
      color:#e6edf3;
      font-weight:700;
      padding:8px 12px;
      background:#161b22;
      border:1px solid #30363d;
      border-radius:10px;
    }
    .lang-box > summary::-webkit-details-marker{display:none}
    .lang-list{
      margin-top:8px;
      display:flex;
      flex-direction:column;
      gap:8px;
      padding:10px;
      background:#161b22;
      border:1px solid #30363d;
      border-radius:10px;
      box-shadow:0 8px 24px rgba(0,0,0,.35);
    }
    .lang-item{
      border:1px solid #30363d;
      background:#21262d;
      color:#e6edf3;
      border-radius:8px;
      padding:8px 10px;
      cursor:pointer;
      font-family:inherit;
      font-size:.9rem;
      text-align:left;
    }
    .lang-item:hover{background:#30363d}
  </style>
</head>
<body>
  <details class="lang-box">
    <summary id="langSummary">Language</summary>
    <div class="lang-list" id="langList"></div>
  </details>

  <h1 id="title">⚡ CloudLink V4 Universal Server</h1>
  <span class="badge">● ONLINE</span>

  <div class="card">
    <div class="row"><span class="label" id="lblVersion">Version</span><span class="value" id="version">…</span></div>
    <div class="row"><span class="label" id="lblPid">PID</span><span class="value" id="pid">…</span></div>
    <div class="row"><span class="label" id="lblUptime">Uptime</span><span class="value" id="uptime">…</span></div>
    <div class="row"><span class="label" id="lblTls">TLS</span><span class="value" id="tls">…</span></div>
    <div class="row"><span class="label" id="lblClients">Clients</span><span class="value" id="clients">…</span></div>
    <div class="row"><span class="label" id="lblUsers">Users</span><span class="value" id="users">…</span></div>
    <div class="row"><span class="label" id="lblGvars">Global vars</span><span class="value" id="gvars">…</span></div>
    <div class="row"><span class="label" id="lblMotd">MOTD</span><span class="value" id="motd" style="color:#e3b341;">…</span></div>
    <div class="row"><span class="label" id="lblSupports">Supports</span><span class="value" id="supports">TurboWarp · PenguinMod · Scratch · All forks</span></div>
    <div class="row"><span class="label" id="lblEndpoint">Endpoint</span><span class="value wss" id="endpoint">…</span></div>
  </div>

  <div class="card">
    <div class="label" id="usersOnlineLabel">Users online: <span id="ucount" style="color:#3fb950">0</span></div>
    <div class="users" id="ulist"><span class="empty pulse">Loading…</span></div>
  </div>

  <div class="card">
    <div class="label" id="connectedIpsLabel" style="margin-bottom:8px">Connected IPs:</div>
    <div class="users" id="ips"><span class="empty pulse">Loading…</span></div>
  </div>

  <div class="card">
    <div class="label" id="connectLabel" style="margin-bottom:8px">Connect from any CloudLink extension:</div>
    <code class="wss" id="endpoint2">…</code>
  </div>

  <script>
  (() => {
    const setText = (id, v) => {
      const el = document.getElementById(id);
      if (el) el.textContent = String(v ?? "");
    };
    const esc = (s) => String(s).replace(/[&<>"]/g, c => ({
      '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'
    }[c]));

    const labels = {
      en: { title:"⚡ CloudLink V4 Universal Server", lang:"Language", version:"Version", pid:"PID", uptime:"Uptime", tls:"TLS", clients:"Clients", users:"Users", gvars:"Global vars", motd:"MOTD", supports:"Supports", endpoint:"Endpoint", online:"Users online", ips:"Connected IPs:", connect:"Connect from any CloudLink extension:", noUsers:"No users connected", noIps:"No IPs connected" },
      vi: { title:"⚡ CloudLink V4 Universal Server", lang:"Ngôn ngữ", version:"Phiên bản", pid:"PID", uptime:"Thời gian chạy", tls:"TLS", clients:"Client", users:"Người dùng", gvars:"Biến toàn cục", motd:"MOTD", supports:"Hỗ trợ", endpoint:"Điểm kết nối", online:"Người đang online", ips:"IP đang kết nối:", connect:"Kết nối từ bất kỳ CloudLink extension nào:", noUsers:"Chưa có người dùng", noIps:"Chưa có IP nào" },
      ja: { title:"⚡ CloudLink V4 Universal Server", lang:"言語", version:"バージョン", pid:"PID", uptime:"稼働時間", tls:"TLS", clients:"クライアント", users:"ユーザー", gvars:"グローバル変数", motd:"MOTD", supports:"対応", endpoint:"エンドポイント", online:"オンラインユーザー", ips:"接続中の IP:", connect:"任意の CloudLink 拡張機能から接続:", noUsers:"接続中のユーザーなし", noIps:"接続中の IP なし" },
      ko: { title:"⚡ CloudLink V4 Universal Server", lang:"언어", version:"버전", pid:"PID", uptime:"가동 시간", tls:"TLS", clients:"클라이언트", users:"사용자", gvars:"전역 변수", motd:"MOTD", supports:"지원", endpoint:"엔드포인트", online:"온라인 사용자", ips:"연결된 IP:", connect:"CloudLink 확장 프로그램으로 연결:", noUsers:"연결된 사용자가 없습니다", noIps:"연결된 IP가 없습니다" },
      zh: { title:"⚡ CloudLink V4 Universal Server", lang:"语言", version:"版本", pid:"PID", uptime:"运行时间", tls:"TLS", clients:"客户端", users:"用户", gvars:"全局变量", motd:"MOTD", supports:"支持", endpoint:"端点", online:"在线用户", ips:"连接中的 IP:", connect:"从任何 CloudLink 扩展连接:", noUsers:"没有用户连接", noIps:"没有 IP 连接" },
      fr: { title:"⚡ CloudLink V4 Universal Server", lang:"Langue", version:"Version", pid:"PID", uptime:"Temps de fonctionnement", tls:"TLS", clients:"Clients", users:"Utilisateurs", gvars:"Variables globales", motd:"MOTD", supports:"Prend en charge", endpoint:"Point de terminaison", online:"Utilisateurs en ligne", ips:"IP connectées :", connect:"Se connecter depuis n'importe quelle extension CloudLink :", noUsers:"Aucun utilisateur connecté", noIps:"Aucune IP connectée" },
      de: { title:"⚡ CloudLink V4 Universal Server", lang:"Sprache", version:"Version", pid:"PID", uptime:"Laufzeit", tls:"TLS", clients:"Clients", users:"Benutzer", gvars:"Globale Variablen", motd:"MOTD", supports:"Unterstützt", endpoint:"Endpunkt", online:"Benutzer online", ips:"Verbundene IPs:", connect:"Mit einer beliebigen CloudLink-Erweiterung verbinden:", noUsers:"Keine Benutzer verbunden", noIps:"Keine IPs verbunden" },
      es: { title:"⚡ CloudLink V4 Universal Server", lang:"Idioma", version:"Versión", pid:"PID", uptime:"Tiempo activo", tls:"TLS", clients:"Clientes", users:"Usuarios", gvars:"Variables globales", motd:"MOTD", supports:"Compatibilidad", endpoint:"Punto final", online:"Usuarios en línea", ips:"IPs conectadas:", connect:"Conectar desde cualquier extensión CloudLink:", noUsers:"No hay usuarios conectados", noIps:"No hay IPs conectadas" },
      ru: { title:"⚡ CloudLink V4 Universal Server", lang:"Язык", version:"Версия", pid:"PID", uptime:"Время работы", tls:"TLS", clients:"Клиенты", users:"Пользователи", gvars:"Глобальные переменные", motd:"MOTD", supports:"Поддержка", endpoint:"Конечная точка", online:"Пользователи онлайн", ips:"Подключенные IP:", connect:"Подключиться из любого расширения CloudLink:", noUsers:"Нет подключенных пользователей", noIps:"Нет подключенных IP" },
      ar: { title:"⚡ CloudLink V4 Universal Server", lang:"اللغة", version:"الإصدار", pid:"PID", uptime:"مدة التشغيل", tls:"TLS", clients:"العملاء", users:"المستخدمون", gvars:"المتغيرات العامة", motd:"MOTD", supports:"الدعم", endpoint:"نقطة النهاية", online:"المستخدمون المتصلون", ips:"عناوين IP المتصلة:", connect:"الاتصال من أي إضافة CloudLink:", noUsers:"لا يوجد مستخدمون متصلون", noIps:"لا توجد عناوين IP متصلة" }
    };

    const languages = [
      ["vi","Tiếng Việt"],
      ["en","English"],
      ["ja","日本語"],
      ["ko","한국어"],
      ["zh","中文"],
      ["fr","Français"],
      ["de","Deutsch"],
      ["es","Español"],
      ["ru","Русский"],
      ["ar","العربية"]
    ];

    function buildLangList() {
      const box = document.getElementById("langList");
      box.innerHTML = languages.map(([code, name]) =>
        '<button class="lang-item" type="button" data-lang="' + code + '">' + name + '</button>'
      ).join("");
    }

    function applyLang(lang) {
      const t = labels[lang] || labels.en;
      localStorage.setItem("ui_lang", lang);
      document.documentElement.lang = lang;
      document.documentElement.dir = lang === "ar" ? "rtl" : "ltr";
      setText("langSummary", t.lang);
      setText("title", t.title);
      setText("lblVersion", t.version);
      setText("lblPid", t.pid);
      setText("lblUptime", t.uptime);
      setText("lblTls", t.tls);
      setText("lblClients", t.clients);
      setText("lblUsers", t.users);
      setText("lblGvars", t.gvars);
      setText("lblMotd", t.motd);
      setText("lblSupports", t.supports);
      setText("lblEndpoint", t.endpoint);
      setText("usersOnlineLabel", t.online + ":");
      setText("connectedIpsLabel", t.ips);
      setText("connectLabel", t.connect);
    }

    buildLangList();
    document.getElementById("langList").addEventListener("click", (e) => {
      const btn = e.target.closest(".lang-item");
      if (!btn) return;
      applyLang(btn.dataset.lang);
    });

    applyLang(localStorage.getItem("ui_lang") || "en");

    async function refresh() {
      const r = await fetch("/status?t=" + Date.now(), { cache: "no-store" });
      const d = await r.json();
      setText("version", d.version);
      setText("pid", d.pid);
      setText("uptime", d.uptime);
      setText("tls", d.tls ? "ON" : "OFF");
      setText("clients", d.clients);
      setText("users", d.users);
      setText("gvars", d.globalVars);
      setText("motd", d.motdEnabled ? d.motd : "");
      setText("endpoint", d.endpoint);
      setText("endpoint2", d.endpoint);
      setText("ucount", Array.isArray(d.userList) ? d.userList.length : 0);

      const t = labels[localStorage.getItem("ui_lang") || "en"] || labels.en;

      const list = Array.isArray(d.userList) ? d.userList : [];
      const ulist = document.getElementById("ulist");
      if (ulist) {
        ulist.innerHTML = list.length
          ? list.map(u => '<span class="user">' + esc(u) + '</span>').join('')
          : '<span class="empty pulse">' + esc(t.noUsers) + '</span>';
      }

      const ips = Array.isArray(d.connectedIps) ? d.connectedIps : [];
      const ipsEl = document.getElementById("ips");
      if (ipsEl) {
        ipsEl.innerHTML = ips.length
          ? ips.map(x => '<span class="user">' + esc(x.ip) + (x.username ? ' • ' + esc(x.username) : '') + '</span>').join('')
          : '<span class="empty pulse">' + esc(t.noIps) + '</span>';
      }
    }

    refresh().catch(() => {});
    setInterval(() => refresh().catch(() => {}), 900);
  })();
  </script>
</body>
</html>`;

  res.writeHead(200, { "Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-store" });
  res.end(html);
}

function logCertExpiry(certPem, label = "certificate") {
  try {
    const x509 = new X509Certificate(certPem);
    const expiry = new Date(x509.validTo);
    const diffMs = expiry.getTime() - Date.now();
    const diffDays = Math.ceil(diffMs / (1000 * 60 * 60 * 24));
    const dateText = expiry.toLocaleString("vi-VN", { dateStyle: "full", timeStyle: "long" });
    console.log(`[cert] ${label} hết hạn lúc: ${dateText} (còn ${diffDays} ngày)`);
    if (diffDays < 0) console.warn(`[cert] ${label} đã hết hạn`);
    else if (diffDays <= 14) console.warn(`[cert] ${label} sắp hết hạn`);
  } catch (e) {
    console.warn(`[cert] không đọc được hạn ${label}:`, e?.message || e);
  }
}

async function start() {
  let server;
  console.log("[cloudlink] booting...");
  try {
    if (USE_TLS) {
      let tlsOpts;
      if (fs.existsSync(CERT_KEY) && fs.existsSync(CERT_CRT)) {
        const certPem = fs.readFileSync(CERT_CRT);
        tlsOpts = { key: fs.readFileSync(CERT_KEY), cert: certPem, minVersion: "TLSv1.2" };
        logCertExpiry(certPem, "TLS cert");
      } else {
        console.warn("[cloudlink] cert files not found, generating self-signed certificate...");
        const pems = await generate([{ name: "commonName", value: PUBLIC_HOST }], { keySize: 2048, algorithm: "sha256", days: 3650 });
        tlsOpts = { key: pems.private, cert: pems.cert, minVersion: "TLSv1.2" };
      }
      server = https.createServer(tlsOpts, httpHandler);
    } else {
      server = http.createServer(httpHandler);
    }

    server.keepAliveTimeout = 20_000;
    server.headersTimeout = 25_000;

    setupWebSocket(server);

    server.on("error", (err) => {
      console.error("[listen error]", err?.stack || err?.message || err);
      process.exit(1);
    });

    const shutdown = () => {
      console.log("\n[shutdown] Closing...");
      for (const [ws] of clients) {
        try { ws.close(4000, "Shutdown"); } catch {}
      }
      server.close(() => process.exit(0));
    };
    process.on("SIGINT", shutdown);
    process.on("SIGTERM", shutdown);

    process.on("uncaughtException", (err) => {
      console.error("[uncaught]", err?.stack || err?.message || err);
    });
    process.on("unhandledRejection", (err) => {
      console.error("[unhandledRejection]", err?.stack || err?.message || err);
    });

    await new Promise((resolve) => {
      server.listen({ port: PORT, host: HOST, ipv6Only: false }, resolve);
    });

    const scheme = USE_TLS ? "wss" : "ws";
    console.log("──────────────────────────────────────────────────────────────");
    console.log(`  CloudLink V4 Universal  v${VERSION}  PID ${process.pid}`);
    console.log(`  ${scheme}://${PUBLIC_HOST}:${PORT}`);
    console.log(`  TLS : ${USE_TLS ? "ON" : "OFF"}`);
    console.log(`  Debug: ON`);
    console.log("──────────────────────────────────────────────────────────────");
  } catch (err) {
    console.error("[fatal]", err?.stack || err?.message || err);
    process.exit(1);
  }
}

start().catch((err) => {
  console.error("[fatal]", err?.stack || err?.message || err);
  process.exit(1);
});