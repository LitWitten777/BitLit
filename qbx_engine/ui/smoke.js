// Smoke test of the UI script against a running server, without a browser.
//
//   cd QBX/src && python -m qbx_engine serve --port 8799 &
//   node qbx_engine/ui/smoke.js http://127.0.0.1:8799
//
// A minimal fake DOM records what the page does; every button is clicked and every
// view drawn.  Exits non-zero if the script throws or the page shows an error.
"use strict";
const fs = require("fs");
const path = require("path");
const base = process.argv[2] || "http://127.0.0.1:8799";
const html = fs.readFileSync(path.join(__dirname, "index.html"), "utf8");
const script = html.match(/<script>([\s\S]*)<\/script>/)[1];

const defaults = {};
for (const m of html.matchAll(/<(input|textarea|select)[^>]*id="([^"]+)"[^>]*>/g)) {
  const v = m[0].match(/value="([^"]*)"/);
  defaults[m[2]] = v ? v[1] : "";
}
defaults.program = (html.match(/<textarea id="program">([\s\S]*?)<\/textarea>/) || [])[1] || "";
defaults.channel = "value"; defaults.alpha = "hebrew";

let draws = 0;
const ctx = new Proxy({}, { get: (t, k) => (k in t ? t[k] : () => { draws++; }), set: (t, k, v) => { t[k] = v; return true; } });
const els = {};
function el(id) {
  if (!els[id]) els[id] = { id, value: defaults[id] ?? "", textContent: "", innerHTML: "", style: {}, dataset: {},
    width: 560, height: 380, scrollTop: 0, classList: { toggle() {} }, addEventListener() {}, appendChild() {},
    getContext: () => ctx };
  return els[id];
}
const ctlButtons = ["turnX", "turnY", "turnZ", "diag", "invert", "spin"].map(c => ({ ...el("ctl_" + c), dataset: { ctl: c } }));
const document = { getElementById: el, querySelectorAll: () => ctlButtons, createElement: () => el("tmp" + Math.random()) };
const window = { addEventListener() {} };
const frames = [];
const sandbox = {
  document, window, performance: { now: () => Date.now() }, requestAnimationFrame: f => frames.push(f),
  fetch: (p, o) => fetch(base + p, o), setInterval, clearInterval, console, Math, JSON,
};
const run = new Function(...Object.keys(sandbox), script + "\nreturn {loadSession, advance, setPlaying, render};");
const api = run(...Object.values(sandbox));
const sleep = ms => new Promise(r => setTimeout(r, ms));

(async () => {
  const fail = msg => { console.error("FAIL", msg); process.exit(1); };
  await sleep(800);
  if (el("err").textContent) fail("load: " + el("err").textContent);
  for (const b of ctlButtons) { await b.onclick(); }
  await el("run").onclick();
  await el("step").onclick();
  el("play").onclick(); await sleep(1200); el("play").onclick();
  for (const v of ["v_stand", "v_spec", "v_torus"]) el(v).onclick();
  el("alpha").value = "greek"; await el("alpha").onchange();
  await el("bbgo").onclick();
  await el("reset").onclick();
  for (let i = 0; i < 5 && frames.length; i++) frames.shift()(Date.now());
  if (el("err").textContent) fail(el("err").textContent);
  const checks = el("checks").innerHTML;
  if (!checks.includes("run_clock") || checks.includes("✘")) fail("checks panel: " + checks);
  if (!el("letters").innerHTML.includes("card")) fail("letters panel empty");
  if (!el("bbres").innerHTML.includes("side by side")) fail("braids panel empty");
  if (draws < 100) fail("too few canvas calls: " + draws);
  console.log("UI smoke OK: frame", el("frame").textContent, "canvas calls", draws);
  process.exit(0);
})().catch(e => { console.error("FAIL", e); process.exit(1); });
