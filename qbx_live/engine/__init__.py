"""Phase 4 engine layer (Sprints 3–4 of ``docs/phase_4_fast_track.md``), first cut.

* :mod:`qbx_live.engine.fixed_point` — lattice states, order-independent merging of worker
  states, synchronous (Kleene) and asynchronous (chaotic) fixed-point iteration with round and
  update counts.
* :mod:`qbx_live.engine.coded` — polynomial-coded products of representation-matrix blocks
  over ``n`` workers with straggler injection, decoded from the first ``k`` answers; an exact
  (``Fraction``) path and a floating-point path that is checked against it.

Both modules are thin runtime layers over :mod:`qbx_engine.seal`, whose functions compute
exactly the objects of the seal-lane theorems S3–S5 (``QBX/Formal/Seal/``).  No dependencies
beyond the standard library, so they run without the locked ``numpy`` environment.
"""

__all__ = ["fixed_point", "coded"]
