"""Local web UI and JSON API for the engine (standard library only).

    python -m qbx_engine serve [--port 8765] [--host 127.0.0.1]

then open http://127.0.0.1:8765/ .  One session is kept in memory.

API (JSON in, JSON out):

  GET  /api/state                       current session state
  POST /api/session   {text, N, M, p, q, read_every, merkaba_every, merkaba_cycle, channel}
  POST /api/run       {program}         run command-language text
  POST /api/advance   {frames}          play scheduled frames
  POST /api/control   {control}         one merkaba control (turnX ... spin)
  POST /api/reset                       reset the session state (same input)
  GET  /api/letters?text=...            letter detail cards
  GET  /api/alphabet?name=hebrew        cards for a whole alphabet
  POST /api/braids    {a: [...], b: [...], mode}   two bundles of texts as braids
  GET  /api/checks                      every re-derived Lean statement
  GET  /api/merkaba.svg                 figure of the merkaba in its current orientation
  POST /api/outset    {name}            write an output set to QBX/data/outsets/<name>
"""

import json
import os
import re
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

from . import braidbraid, letters, merkaba, outsets
from .controls import Session

UI_DIR = os.path.join(os.path.dirname(__file__), "ui")
OUT_ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "..", "data", "outsets"))

_lock = threading.Lock()
_state = {"session": Session()}


def _session():
    return _state["session"]


def handle(method, path, query, body):
    """Dispatch one API call; returns (status, content_type, payload)."""
    s = _session()
    if path == "/api/state":
        return 200, "json", s.state()
    if path == "/api/session" and method == "POST":
        kw = {k: body[k] for k in ("text", "N", "M", "p", "q", "read_every", "merkaba_every",
                                   "channel") if k in body}
        for k in ("N", "M", "p", "q", "read_every", "merkaba_every"):
            if k in kw:
                kw[k] = int(kw[k])
        if not (2 <= kw.get("N", 16) <= 64 and 2 <= kw.get("M", 25) <= 64):
            return 400, "json", {"error": "torus sides must be between 2 and 64"}
        if "merkaba_cycle" in body:
            cyc = [c for c in body["merkaba_cycle"] if c]
            bad = [c for c in cyc if c not in merkaba.CONTROLS]
            if bad:
                return 400, "json", {"error": "unknown merkaba control(s): %s" % bad}
            kw["merkaba_cycle"] = cyc
        _state["session"] = Session(**kw)
        return 200, "json", _session().state()
    if path == "/api/run" and method == "POST":
        try:
            return 200, "json", s.run(body.get("program", ""))
        except (ValueError, IndexError) as e:
            return 400, "json", {"error": str(e), "state": s.state(grids=False)}
    if path == "/api/advance" and method == "POST":
        n = max(0, min(int(body.get("frames", 1)), 5000))
        return 200, "json", s.advance(n)
    if path == "/api/control" and method == "POST":
        c = body.get("control")
        if c not in merkaba.CONTROLS:
            return 400, "json", {"error": "unknown control %r" % c}
        s.execute(c)
        return 200, "json", s.state()
    if path == "/api/reset" and method == "POST":
        s.reset()
        return 200, "json", s.state()
    if path == "/api/letters":
        return 200, "json", letters.cards(query.get("text", [""])[0], s.N, s.M)
    if path == "/api/alphabet":
        name = query.get("name", ["hebrew"])[0]
        if name not in ("hebrew", "greek", "latin"):
            return 400, "json", {"error": "unknown alphabet"}
        return 200, "json", letters.alphabet_cards(name, s.N, s.M)
    if path == "/api/braids" and method == "POST":
        a, b = list(body.get("a", [])), list(body.get("b", []))
        if len(a) < 1 or len(b) < 1:
            return 400, "json", {"error": "need at least one text in each bundle"}
        a = a if len(a) > 1 else a + [a[0][::-1]]
        b = b if len(b) > 1 else b + [b[0][::-1]]
        return 200, "json", braidbraid.interact(a[:6], b[:6], body.get("mode", "written"))
    if path == "/api/checks":
        return 200, "json", outsets.all_checks(s)
    if path == "/api/merkaba.svg":
        return 200, "svg", merkaba.svg(s.merk)
    if path == "/api/outset" and method == "POST":
        name = re.sub(r"[^A-Za-z0-9_.-]", "_", body.get("name") or "session")[:64]
        out = os.path.join(OUT_ROOT, name)
        res = outsets.outset(s.text, out, frames=max(1, s.frame) if s.frame else None, N=s.N, M=s.M)
        res["dir"] = os.path.relpath(out, os.path.join(OUT_ROOT, "..", ".."))
        return 200, "json", res
    return 404, "json", {"error": "no such endpoint %s %s" % (method, path)}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):  # quiet
        pass

    def _send(self, status, ctype, payload):
        if ctype == "json":
            data = json.dumps(payload, ensure_ascii=False, default=str).encode("utf-8")
            ct = "application/json; charset=utf-8"
        elif ctype == "svg":
            data, ct = payload.encode("utf-8"), "image/svg+xml"
        else:
            data, ct = payload, ctype
        self.send_response(status)
        self.send_header("Content-Type", ct)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _dispatch(self, method):
        raw = self.path
        try:  # raw UTF-8 in the request line arrives as latin-1 text
            raw = raw.encode("latin-1").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass
        u = urlparse(raw)
        if not u.path.startswith("/api/"):
            name = "index.html" if u.path in ("/", "") else u.path.lstrip("/")
            fp = os.path.normpath(os.path.join(UI_DIR, name))
            if not fp.startswith(UI_DIR) or not os.path.isfile(fp):
                return self._send(404, "text/plain", b"not found")
            ct = {"html": "text/html; charset=utf-8", "js": "text/javascript", "css": "text/css"}.get(
                fp.rsplit(".", 1)[-1], "application/octet-stream")
            with open(fp, "rb") as fh:
                return self._send(200, ct, fh.read())
        body = {}
        if method == "POST":
            n = int(self.headers.get("Content-Length") or 0)
            if n:
                try:
                    body = json.loads(self.rfile.read(n).decode("utf-8"))
                except ValueError:
                    return self._send(400, "json", {"error": "invalid JSON"})
        with _lock:
            try:
                status, ctype, payload = handle(method, u.path, parse_qs(u.query), body)
            except Exception as e:  # report, keep serving
                status, ctype, payload = 500, "json", {"error": "%s: %s" % (type(e).__name__, e)}
        self._send(status, ctype, payload)

    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")


def serve(host="127.0.0.1", port=8765):
    httpd = ThreadingHTTPServer((host, port), Handler)
    print("QBX engine UI on http://%s:%d/  (Ctrl-C to stop)" % (host, port))
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()
