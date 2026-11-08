"""qbx_micro: the six-channel core in exact, dependency-free Python.

Modules (all MicroPython-compatible except `grade`, the desktop corpus grader):
  cliff  exact Clifford algebra Cl(p,q,r) on hypercube bitmask blades
  braid  the six channels and the Lean-backed integrity checks
  laws   law profiles of identities in the Cayley-Dickson tower
  cert   prover-neutral failure certificates (Lean 4 / Coq / Isabelle)
  chern  integer Chern numbers of two-band models (two independent methods)
  grade  corpus grader for theorem-graph exports (CPython)
See QBX/docs/design/SIX_CHANNEL_GRADING.md.
"""
