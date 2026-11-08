"""
qbx_live — the living layer of QBX: harmonic healing, Fano UV completion,
gap filling, and visual/audible output.

* :mod:`qbx_live.healing` — spectral energy, healing flows, Fano completion,
  Hamming syndrome decoding, gap filling with anchor verification, and the
  optional geometric (point-cloud) layer.
* :mod:`qbx_live.output` — plots (braid diagram, permutohedron path,
  eigenvalue trajectories, energy heat map, Fano plane, linkage) and
  sonification (WAV synthesis).
* :mod:`qbx_live.wire` — canonical CBOR/JSON wire format for chunk summaries.
* :mod:`qbx_live.window_cache` — content-addressed cache of window summaries
  (verify-on-write and on read), composed with map–reduce.
* :mod:`qbx_live.routing` — three-fold-way routing: exact real-type refuters
  first, the harmonic sweep folded in half.
* :mod:`qbx_live.evaluate` — single-node five-channel evaluator (CLI).

Every exact statement used here is proved in Lean under
``QBX/Formal/Sovereign`` and ``QBX/Formal/MultiProver``; see
``QBX/docs/design/HARMONIC_HEALING.md`` for the correspondence table.
"""

__all__ = ["healing", "output", "wire", "window_cache", "routing", "evaluate"]
