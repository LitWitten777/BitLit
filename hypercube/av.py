"""Simple audio and visual views of the model.

* `svg(state)`   - the 64 cells laid out as the sky (columns: the eight 3-hour RA sectors
  from 0h to 24h; rows: declination bands north to south, each split bright/faint), the bodies
  drawn in their cells and the house stars as dots.
* `wav(frames)`  - each frame is a chord: every body sounds the tone of its cell (RA sector ->
  scale degree, declination band -> octave); a low drone marks eclipse seasons.
* `html(frames)` - a self-contained page: the same grid animated over the frames, with a
  slider and WebAudio tones.  No external files or network access.
"""
import json
import math
import struct
import wave

from . import cells, state as st_mod

GLYPH = {"Sun": "☉", "Moon": "☾", "Mercury": "☿", "Venus": "♀", "Mars": "♂", "Jupiter": "♃",
         "Saturn": "♄", "Uranus": "♅", "Neptune": "♆", "Pluto": "♇"}
ROW_LABELS = ["N≥30 bright", "N≥30", "N0–30 bright", "N0–30", "S0–30 bright", "S0–30", "S≤−30 bright", "S≤−30"]


def _cell_xy(c, size, top):
    r, col = cells.grid_position(c)
    return 90 + col * size, top + r * size


def svg(state, size=72):
    top = 60
    w, h = 90 + 8 * size + 20, top + 8 * size + 60
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" font-family="sans-serif">',
           f'<rect width="{w}" height="{h}" fill="#0b0d17"/>',
           f'<text x="10" y="24" fill="#eee" font-size="16">Hypercube sky — {state["time"]["ut"]} UT '
           f'(moon {state["moon"]["phase"]}, {state["moon"]["illuminated"]:.0%} lit)</text>']
    if state["moon"]["solar_eclipse_season"] or state["moon"]["lunar_eclipse_season"]:
        out.append(f'<text x="10" y="44" fill="#ff6060" font-size="13">eclipse season: Sun '
                   f'{state["moon"]["sun_from_node_deg"]:.1f}° from a lunar node</text>')
    for k in range(8):
        out.append(f'<text x="{90 + k * size + size / 2}" y="{top - 6}" fill="#aaa" font-size="11" '
                   f'text-anchor="middle">{3 * k}–{3 * k + 3}h</text>')
        out.append(f'<text x="84" y="{top + k * size + size / 2 + 4}" fill="#aaa" font-size="10" '
                   f'text-anchor="end">{ROW_LABELS[k]}</text>')
    for c in range(64):
        x, y = _cell_xy(c, size, top)
        out.append(f'<rect x="{x}" y="{y}" width="{size - 2}" height="{size - 2}" fill="{cells.colour(c)}" '
                   f'fill-opacity="0.28" stroke="#333"/>')
        out.append(f'<text x="{x + 3}" y="{y + 11}" fill="#ccc" font-size="9">{c} {cells.codon(c)}</text>')
    for name, ra, dec, mag, c in st_mod.house_stars():
        x, y = _cell_xy(c, size, top)
        fx = (ra % 3) / 3
        out.append(f'<circle cx="{x + 4 + fx * (size - 10)}" cy="{y + size - 8}" r="1.6" fill="#fff" '
                   f'fill-opacity="0.7"><title>{name}</title></circle>')
    slots = {}
    for b, row in state["bodies"].items():
        c = row["cell"]
        i = slots.get(c, 0)
        slots[c] = i + 1
        x, y = _cell_xy(c, size, top)
        cx, cy = x + 16 + (i % 3) * 20, y + 30 + (i // 3) * 20
        out.append(f'<circle cx="{cx}" cy="{cy}" r="9" fill="{row["colour"]}"><title>{b}: RA '
                   f'{row["ra_j2000_h"]:.3f}h Dec {row["dec_j2000"]:.2f}° cell {c}</title></circle>')
        out.append(f'<text x="{cx}" y="{cy + 4}" font-size="12" text-anchor="middle" fill="#000">{GLYPH[b]}</text>')
    out.append(f'<text x="10" y="{h - 30}" fill="#888" font-size="11">Cell = HouseSky address (J2000). '
               f'Earth (anti-solar) cell = Sun cell XOR 3 = {state["earth"]["anti_solar_cell"]}.</text>')
    out.append(f'<text x="10" y="{h - 14}" fill="#888" font-size="11">Codon labels are a chosen bijection '
               f'(CodonCells.lean convention), not an observation.</text>')
    out.append("</svg>")
    return "\n".join(out)


def wav(frames, path, seconds_per_frame=0.25, rate=22050):
    loud = {"Sun": 0.22, "Moon": 0.18}
    n = int(seconds_per_frame * rate)
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        phase = {}
        for f in frames:
            buf = []
            tones = [(b, cells.tone_hz(c)) for b, c in f["cells"].items()]
            season = f["moon"]["solar_eclipse_season"] or f["moon"]["lunar_eclipse_season"]
            for i in range(n):
                env = min(1.0, i / (0.02 * rate), (n - i) / (0.02 * rate))
                v = 0.0
                for b, hz in tones:
                    p = phase.get(b, 0.0) + 2 * math.pi * hz / rate
                    phase[b] = p
                    v += loud.get(b, 0.06) * math.sin(p)
                if season:
                    p = phase.get("_drone", 0.0) + 2 * math.pi * 55.0 / rate
                    phase["_drone"] = p
                    v += 0.15 * math.sin(p)
                buf.append(struct.pack("<h", int(max(-1, min(1, v * env)) * 32000)))
            w.writeframes(b"".join(buf))
    return path


HTML = """<!doctype html><html><head><meta charset="utf-8"><title>Hypercube sky</title>
<style>body{background:#0b0d17;color:#ddd;font-family:sans-serif}canvas{display:block;margin:8px 0}</style>
</head><body><h3>Hypercube sky — %(title)s</h3>
<div><button id="play">play / pause</button> <button id="snd">sound on/off</button>
<input id="t" type="range" min="0" max="%(last)d" value="0" style="width:640px"> <span id="lab"></span></div>
<canvas id="c" width="720" height="640"></canvas>
<p style="font-size:12px;color:#888">Columns: RA sectors 0–24h. Rows: north ≥30°, north 0–30°, south 0–30°,
south ≤−30°, each bright/faint. Cell numbers are HouseSky addresses; colours and tones are conventions.
Red border: eclipse season.</p>
<script>
const F=%(frames)s, CELLS=%(cells)s, G=%(glyph)s, COL=%(colour)s;
const cv=document.getElementById('c'),cx=cv.getContext('2d'),S=76,X0=60,Y0=20;
let i=0,run=false,snd=false,ac=null,osc={};
function draw(){const f=F[i];cx.fillStyle='#0b0d17';cx.fillRect(0,0,cv.width,cv.height);
 for(const c of CELLS){cx.fillStyle=c.colour+'55';cx.fillRect(X0+c.grid[1]*S,Y0+c.grid[0]*S,S-2,S-2);
  cx.fillStyle='#bbb';cx.font='9px sans-serif';cx.fillText(c.cell+' '+c.codon,X0+c.grid[1]*S+3,Y0+c.grid[0]*S+11);}
 const slot={};for(const b in f.cells){const c=CELLS[f.cells[b]],k=slot[c.cell]||0;slot[c.cell]=k+1;
  const x=X0+c.grid[1]*S+16+(k%%3)*20,y=Y0+c.grid[0]*S+30+Math.floor(k/3)*20;
  cx.fillStyle=COL[b];cx.beginPath();cx.arc(x,y,9,0,7);cx.fill();cx.fillStyle='#000';cx.font='12px sans-serif';
  cx.fillText(G[b],x-5,y+4);}
 if(f.moon.solar_eclipse_season||f.moon.lunar_eclipse_season){cx.strokeStyle='#f44';cx.lineWidth=4;cx.strokeRect(2,2,cv.width-4,cv.height-4);}
 document.getElementById('lab').textContent=f.ut+' UT, moon '+f.moon.phase;document.getElementById('t').value=i;
 if(snd){for(const b in f.cells){if(!osc[b]){const o=ac.createOscillator(),g=ac.createGain();g.gain.value=(b=='Sun'||b=='Moon')?0.08:0.025;
  o.connect(g).connect(ac.destination);o.start();osc[b]=o;}osc[b].frequency.setTargetAtTime(CELLS[f.cells[b]].tone_hz,ac.currentTime,0.03);}}}
document.getElementById('t').oninput=e=>{i=+e.target.value;draw();};
document.getElementById('play').onclick=()=>{run=!run;};
document.getElementById('snd').onclick=()=>{snd=!snd;if(snd&&!ac)ac=new AudioContext();if(!snd){for(const b in osc)osc[b].stop();osc={};}};
setInterval(()=>{if(run){i=(i+1)%%F.length;draw();}},120);draw();
</script></body></html>"""


def html(frames, title=""):
    tab = [{"cell": c["cell"], "grid": c["grid"], "colour": c["colour"], "codon": c["codon"],
            "tone_hz": c["tone_hz"]} for c in cells.table()]
    return HTML % {"title": title, "last": len(frames) - 1,
                   "frames": json.dumps(frames, ensure_ascii=False, separators=(",", ":")),
                   "cells": json.dumps(tab, separators=(",", ":")),
                   "glyph": json.dumps(GLYPH, ensure_ascii=False), "colour": json.dumps(st_mod.BODY_COLOUR)}
