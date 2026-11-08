# `qbxlang/`: the QBX verifier language

`.qbx` source → AST → IR (`.qbxir`, JSON) → signed certificate (`.qbxcert`). Claims that fall in
the kernel's language are also emitted as Lean, and **Lean's kernel re-checks them**. So the
Python results are trusted only where Lean agrees with them.

It is a *verifier* language, not a general-purpose one. There are no loops and no recursion,
every program terminates, and every check is decided by computation. Python 3 standard library,
plus `cryptography` for Ed25519 signatures.

```
python3 -m qbxlang run     qbxlang/examples/structure.qbx        # report
python3 -m qbxlang compile qbxlang/examples/genesis_1_1.qbx -o g.qbxir
python3 -m qbxlang keygen  ~/.qbx/key                            # key pair
python3 -m qbxlang sign    qbxlang/examples/genesis_1_1.qbx --key ~/.qbx/key
python3 -m qbxlang verify  qbxlang/examples/genesis_1_1.qbxcert qbxlang/examples/genesis_1_1.qbx --pub ~/.qbx/key.pub
python3 -m qbxlang lean    qbxlang/examples/genesis_1_1.qbx -o RequestProject/Certs/Genesis.lean
python3 -m qbxlang layers                                        # the one-line map
python3 -m qbxlang selftest
```

## The pipeline

| stage | file | what it does | trusted? |
|---|---|---|---|
| lexer, parser | `parser.py` | `.qbx` text → AST; every node keeps its line number | no (syntax only) |
| front end | `hypercube/codec.py` (`letters`, `braid_word`) | text → letters → braid word (letter `i` → `σ_{i mod 5 + 1}`, final forms inverted) | **no**: this is the one unverified step, named in every IR under `trusted_base` |
| evaluator | `compiler.py` | evaluates every check; gives it a status (`pass` / `fail` / `undecided`) and a layer; lowers it to a kernel claim where possible | no: re-checked below |
| IR | `.qbxir` | canonical JSON; SHA-256 digest | — |
| certificate | `cert.py` | binds the source digest and IR digest to an Ed25519 signature; `verify` recompiles and compares | crypto |
| kernel | `lean_emit.py` → `RequestProject/QBXCheck.lean` | the claims become a `List QBX.Claim`; `checkAll cert = true` is closed by `decide +kernel`; `checkAll_sound` turns it into the statements | **yes** (Lean kernel) |

## The language

```
source NAME { text: "..."; encoding: letter-ordinal-v1; strands: 6 }
def NAME = EXPR
check EXPR == EXPR  [as "label"]
check EXPR != EXPR  [as "label"]
convention NAME { labels: "codon"; ... }                  # a labelling choice: recorded, not evidence
interpret "TITLE" { claims: "..."; support: ["label", ...] }   # a reading: recorded, never proved
```

Expressions: `braid(src)`, `word(1, 1, -2, -2)`, `concat(a, b)`, `inverse(b)`, `walk(b, cell)`,
`parity(b, cell)`, `writhe(b)`, `perm(b)`, `length(b)`, `gematria(src, standard|sofit|ordinal|katan|milui|complete)`,
`dist(x, y)`, `burau(b)` (Burau matrix at `t = -1`; computed only), and the constants `identity` and `one`.

## What goes to the Lean kernel

| `.qbx` check | kernel claim | what Lean proves when it accepts it |
|---|---|---|
| `walk(b, s) == t` | `.walkEnd` | `b` uses only letters `±1…±5`, `s < 64`, and the walk from `s` ends at `t` |
| `parity(b, s) == p` | `.parity` | the end cell has parity `p` |
| `writhe(b) == k` | `.writhe` | writhe is `k` |
| `perm(b) == p` / `identity` | `.perm` | strand permutation is `p` |
| `a != b` (braids) | `.braidNe` | **`a` and `b` are different elements of the braid group `B₆`** (Artin presentation) |
| `dist(x, y) == d` | `.cellDist` | Hamming distance in `Q₆` |
| `gematria(src, m) == v` (Hebrew text, m ∈ standard/sofit/ordinal/katan) | `.gematria` | the letter-value sum of the letter sequence is `v` |

To decide `a != b`, the checker looks for a cell of `Q₆` where the two walks end in different
places. This is sound because the walk is an action of `B₆` (`QBX.domeAction`). Braid
**equality** is never claimed: when the dome action does not separate two words, the check is
reported `undecided`. Deciding equality would need a normal form (Garside), which is not in the
kernel yet.

## Layers: the one-line map, enforced

Every check, convention and interpretation is tagged with one layer: `model`, `boundary`,
`symmetry`, `comparison`, `convention`, `calibration`, `geodesy` or `interpretation`. Run
`python3 -m qbxlang layers` to see what each layer contains and where it is proved. So a
certificate always shows what kind of statement it carries. Interpretations (Logos,
Christ/antichrist, Lilith, Adam Kadmon, …) are carried with their cited checks and flagged
`interpretation`. They are never counted as passes.

## Results of the examples (checked by Lean)

* `examples/structure.qbx`: the Lilith word `σ₁²σ₂⁻²` has trivial permutation and writhe 0, yet it
  is not the identity of `B₆`; it moves cell 0 to cell 5. 8 kernel claims
  (`RequestProject/Certs/Structure.lean`).
* `examples/genesis_1_1.qbx`: Genesis 1:1 has standard gematria 2701 and ordinal 298. Its braid word
  has 28 letters and writhe 22 (the 3 final letters count negative), and it ends on an even cell
  (parity law). It is a different element of `B₆` from John 1:1. 5 kernel claims
  (`RequestProject/Certs/Genesis.lean`).

## Correction to the structure summary

The braid walk's transitivity diameter is **6**, not ≤ 12. Any cell reaches any other in at most
6 letters, and antipodes need exactly 6 (`QBX.Q6.braid_diameter`). The bound 12 comes from
routing through a hub cell (≤ 6 there, ≤ 6 back).
