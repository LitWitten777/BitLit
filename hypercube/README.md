# `hypercube/` — the QBX hypercube model, stage 1

One engine and one data file for the project's geometric, temporal and textual structure. Full
description, checks and caveats: [`docs/HYPERCUBE_MODEL_2026-10-23.md`](../docs/HYPERCUBE_MODEL_2026-10-23.md).
Proved facts: `sovereign/Sovereign/Organism/HypercubeModel.lean`.

Python 3 standard library only. Run from the repository root:

```
python3 -m hypercube fetch                       # unpack sources/*.tar.lzma into .cache/ (MD5-checked)
python3 -m hypercube state 2026-10-23T12:00 --place 31.778,35.235 --eclipses
python3 -m hypercube state "763-06-15 BC"        # any date 4202 BC - AD 2400 (UT)
python3 -m hypercube eclipses 2026 2028 --place 31.778,35.235
python3 -m hypercube encode "text" --style codon # base64 | codon | amino | cells | hexagram
python3 -m hypercube decode "CUA CCA" --style codon
python3 -m hypercube profile "בְּרֵאשִׁית"        # gematria, braid walk, cells
python3 -m hypercube deobfuscate "Va gur ortvaavat jnf gur Jbeq"
python3 -m hypercube svg 2026-08-12T17:46        # -> hypercube/out/sky.svg
python3 -m hypercube html 2026-07-01 2027-03-01 1
python3 -m hypercube wav 2026-08-01 2026-08-31 0.25
python3 -m hypercube build --ancient             # regenerate data/system.json and data/eclipses_-0800_0100.json
python3 -m hypercube selftest
python3 -m hypercube gears                        # the cycles and how well they mesh
python3 -m hypercube wind 2026-08-12T17:46 --kind solar --steps=-3,3   # wind the real sky by Saros
python3 -m hypercube lattice                      # Q6 vs E8 vs E8^3 vs Leech (stage 2)
python3 -m hypercube gauge                        # Z/2 lattice gauge theory on the cube
python3 -m hypercube crossdomain                  # stage 3: crystals, circuits, cocycles, topology, sky braid
python3 -m hypercube crystal-svg                  # -> hypercube/out/codon_crystal.svg
python3 -m hypercube hebrew 2017-08-21            # 29 Av 5777  (reverse: --to-civil 5805 5 29)
python3 -m hypercube calibrate                    # the ten documents' statements, recomputed
python3 -m hypercube patterns                     # factorions, n-cube nets, Curtis's MOG
python3 -m hypercube hopf                         # the four finite Hopf fibrations of Q6 and the GF(8) bundle
python3 -m hypercube music --wav artifacts/hypercube/music_vortex.wav --svg artifacts/hypercube/music_vortex.svg
                                                  # music vortexes (octave vortex on the bundle, Tonnetz, lattices)
```

| module | role |
|---|---|
| `store.py` | committed archives -> `.cache/` |
| `timescale.py` | calendars, Delta T, sidereal time |
| `sky.py` | Swiss Ephemeris (DE441) positions, frames, alt/az, magnitudes |
| `eclipses.py` | eclipse search, types, Saros, contacts, local circumstances |
| `cells.py` | the 64 cells and their correspondences |
| `scripture.py` | canon, verse text, chapter-circle placement |
| `state.py` | `state(time, place)`, `series(...)` |
| `codec.py` | text <-> cells, letters, gematria, deobfuscation |
| `av.py` | SVG / WAV / HTML |
| `build_data.py` | `data/system.json` |
| `gears.py` | cycle table, winding forward/backward, reversibility |
| `lattice.py` | Q6 shells, E8 roots, Golay code, Leech minimal vectors, theta series |
| `gauge.py` | Z/2 lattice gauge theory on Q_n (exact for Q3, Monte Carlo for Q6) |
| `crossdomain.py` | Kashiwara crystals (quarks, codons), Kirchhoff circuits, Cayley–Dickson cocycles, cube homology, sky braid windings |
| `hebcal.py` | arithmetic Hebrew calendar (Dershowitz–Reingold) |
| `calibrate.py` | calibration ledger: 103 statements of the ten documents recomputed |
| `patterns.py` | factorions, hypercube nets, hexacode / MOG Golay code, sextets, trios |
| `hopf.py` | Hopf fibrations of Q6 over GF(2), GF(4), GF(8), GF(64); fibre map, quotient graph, atlas |
| `music.py` | music vortexes: octave = squaring on the Hopf bundle (circuit 1-2-4-8-7-5, axis 3-6-9), Tonnetz vortices, scales, commas, octave classes of Z^6 and E8, audio/SVG (Lean `MusicVortex.lean`, `MusicTonnetz.lean`, `MusicLattices.lean`) |
| `selftest.py` | end-to-end checks |
| `mirror.py` | mirror code: 9 GF(8) fibres, any 2 recover a cell (Lean `MirrorCode.lean`) |
| `archive.py` | file archive on the mirror code: 9 shards + manifest, any 2 restore (`pack`/`unpack`/`damage`/`selftest`) |
| `store_heal.py` | mirror code × [6,3,3] code: lose 7 shards and flip 1 bit per codeword in the rest (Lean `healMirrorCorrect`) |
| `codec_walsh.py` | lossless Walsh band codec (shells / octaves / hopf) and universal-threshold denoiser (needs numpy) |
| `dht.py` | 9-way bucket DHT on the GF(8) fibres (Lean `bucketInvariant`) |
| `cdcheck.py` | pentagon checksum for Cayley–Dickson products; `manifold/cd.py` calls it when `Q6_CDCHECK=1` |
| `erase.py` | irreversible 4-of-16 sector erasure with the 84 sedenion zero divisors (needs numpy) |
| `hashrounds.py` | test battery T0–T8: how much information survives rounds of hashing and how much the tools / CD tower recover (needs numpy; Lean `HashRounds.lean`, `HashRoundsLamb.lean`, `HashRoundsModTwo.lean`) |

Verdicts and commands for these seven tools: `docs/ENGINEERING_TOOLS_2026-10-25.md`.

Hash-rounds battery: plan `docs/PREREG_HASH_ROUNDS_2026-10-25.md`, results `docs/HASH_ROUNDS_RESULTS_2026-10-25.md`, log `artifacts/hypercube/hashrounds_report.txt`.

Calibration (2026-10-23): `docs/HYPERCUBE_CALIBRATION_2026-10-23.md`; Lean:
`sovereign/Sovereign/Organism/HypercubeCalibration.lean`, `sovereign/Sovereign/Organism/HypercubePatterns.lean`,
`QBX/Forensics/Inert/TorahGematriaCalibration.lean`; ledger `artifacts/hypercube/calibration_ledger.tsv`.

Stage 3 write-up: `docs/HYPERCUBE_CROSSDOMAIN_2026-10-23.md`; Lean: `sovereign/Sovereign/Organism/HypercubeCrystals.lean`.

Stage 2 write-up: `docs/HYPERCUBE_LATTICES_2026-10-23.md`; Lean: `sovereign/Sovereign/Organism/HypercubeLattices.lean`.

Samples: `artifacts/hypercube/sky_2026-07_2027-03.html` (open in a browser; includes the
2026-08-12 total solar eclipse season) and `artifacts/hypercube/sky_2026-08.wav`.

Hopf fibrations (2026-10-23): `docs/HYPERCUBE_HOPF_2026-10-23.md`; Lean: `RequestProject/HypercubeHopf.lean` (module `RequestProject.HypercubeHopf`; goes in `sovereign/RequestProject/`).

Music vortexes (2026-10-25): `docs/MUSIC_VORTEX_2026-10-25.md`; Lean: `RequestProject/MusicVortex.lean`, `RequestProject/MusicTonnetz.lean`, `RequestProject/MusicLattices.lean`; outputs `artifacts/hypercube/music_report.json`, `music_vortex.wav`, `music_vortex.svg`.
