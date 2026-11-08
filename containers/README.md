# QBX containers (CNT-001)

A **container** is a declared geometric object with a carrier, a curvature, a metric, an algebra,
a boundary and a version. Containers compose by the rules of the underlying geometry. So the
system's architecture *is* its geometry, and both can be checked.

This directory is the coordination layer that sits over Lean, Python and the database. It does
not replace any of them. A descriptor is metadata about existing code and theorems. Three tools
check it:

```bash
cd QBX
.venv/bin/python -m qbx_containers check     # validate every descriptor and composite
.venv/bin/python -m qbx_containers list
.venv/bin/python -m qbx_containers show hebrew_pipeline
./health.sh --only containers                # same check, part of the health suite
.venv/bin/python -m pytest tests/test_containers.py
```

On the Lean side, `QBX/Formal/Foundations/Container.lean` proves the curvature claims the
descriptors cite.

## What "curvature" means here

Curvature is the **large-scale class** of a carrier, measured by how fast balls grow. The volume
`V(r)` is the number of states within distance `r` of a base point. This is the coarse notion of
curvature that makes sense for discrete carriers such as hypercubes, lattices, trees and word
spaces. It is proved, not just asserted:

| class | volume growth | geometry | examples | Lean |
|---|---|---|---|---|
| `positive` | bounded | closed, compressive | hypercube `{0,1}ⁿ`, finite codes, finite groups | `hypercube_correct` |
| `flat` | unbounded, at most polynomial | translational | `ℤᵏ`, torus (via its universal cover) | `lattice_correct`, `torusCover_surjective` |
| `negative` | at least exponential | growing, hierarchical | trees, free monoids (word spaces), hyperbolic graphs | `tree_correct` |

`Holds.unique` shows that a carrier has exactly one class, so the declaration is not a matter of
taste. `poly_not_dominates_exp` is the reason a tree cannot be embedded in a flat container.
Finite carriers (a torus `ℤ/m × ℤ/n`, for example) are classified through their **development**,
meaning the cover whose growth they model: the torus is developed as `lattice(2)`. Without that,
every finite object would count as "positive".

Finer notions, such as Ollivier–Ricci or sectional curvature, are open work (see below). The
volume class is the part that is proved now.

## Descriptor (`descriptors/<name>.json`)

| field | required | meaning |
|---|---|---|
| `name` | yes | unique id, equal to the file name |
| `version` | yes | `MAJOR.MINOR.PATCH` (see versioning rule) |
| `curvature` | yes | `positive` / `flat` / `negative` |
| `carrier` | yes | `hypercube(n)`, `lattice(k)`, `torus(m,n)`, `cycle(m)`, `tree(b)`, `free(X)`, `finite(N)`, `product(A;B)` |
| `development` | no | cover whose growth defines the curvature (default derived from carrier) |
| `metric` | yes | `{"formula": ..., "lean": <theorem/def name>}`; the only thing consumers see |
| `algebra` | yes | list of supported operations; operations forbidden for the curvature are rejected |
| `boundary` | yes | `{"kind": none/closed/leaves/edge/port, "attaches": [...]}` |
| `address` | no | defaults: positive→`codeword`, flat→`coordinates`, negative→`path` |
| `time` | no | defaults: positive→`layered`, flat→`uniform_steps`, negative→`causal` |
| `hosting` | no | `{"preserve": [...], "substrates": [cpu, fpga, dht, esp32, ...]}` |
| `lean` | no | named theorems: `correctness`, plus any others |
| `code` | no | implementing files; they must exist |
| `adaptive` | no | `{"trigger": ..., "to": <curvature>, "new_container": <name>}`; see "as needed" |
| `override_reason` | no | required when `address`/`time` differ from the curvature defaults |

### Interface rejections (checked statically)

The checker rejects these at the interface, before anything runs:

* A `positive` container that declares `translation`, `exponential_capacity` or
  `unbounded_growth`.
* A `flat` container that declares `exponential_capacity` or `unbounded_branching`.
* A `negative` container that declares `o1_random_access`, `uniform_indexing` or
  `translation_invariance`.
* A declared curvature that disagrees with the volume profile computed for the carrier (or its
  development). This is always an error.
* Address or time semantics that differ from the curvature defaults without an `override_reason`.
* Lean names, code paths and boundary attachments that do not resolve.

The library function `qbx_containers.curvature.can_embed` checks embeddings separately. It
reports the first radius at which the volume obstruction rules out an embedding into the target.
Example: a tree with `2^20` leaves cannot go into a flat container of diameter 40.

## Composites (`composites/<name>.json`)

| kind | rule | status |
|---|---|---|
| `product` | `A × B` with the sum metric: negative absorbs everything, flat absorbs positive | **theorem** (`Container.prod_correct`) |
| `bundle` | `F → E → B`: base and fiber may differ, and a `connection` field is required; the total class equals the product class | theorem for trivial bundles; **declared convention** for twisted bundles with compact structure group |
| `sum` | `A ⊔ B`: the worst component dominates; requires equal algebras | checked |
| `pipeline` | ordered stages. Every transition that changes curvature must say so (`curvature_changing`, `to`) and should cite Lean. A transition that joins a container with no boundary to a bounded one needs a `connection` | checked |

Worked examples:

* `hebrew_pipeline` goes text (flat) → reading frame (positive) → encoding bundle (positive) →
  braid words (negative) → invariants (flat). Every change of curvature is declared at its
  interface. `qbx.process` is the code that runs it.
* `hebrew_encoding` is a bundle: the base is the letters, the fiber is the generator assignment.
* `torus_hypercube_bundle` has a toroidal base (flat) and a hypercube fiber (positive). It is the
  container form of the torus/hypercube/lattice coordinate system.
* `codeword_cache` is a negative-curvature cache tree whose leaves are positive codewords.

## Versioning rule (decision CNT-001)

* A **curvature change** means a **new container**, with a new name. Consumers rely on curvature
  through address and time semantics, so changing it breaks the interface.
* A **metric change** means a **MAJOR** version bump.
* An **algebra change** means a MINOR bump if operations are only added, and a MAJOR bump if any
  are removed.
* Notes, code paths and Lean references mean a PATCH bump.

## The "as needed" part (adaptive curvature)

A container may declare `adaptive: {trigger, to, new_container}`. This is a **hand-authored phase
transition**. When the trigger fires, for example "depth > 20" or "load factor > 0.8", the host
re-hosts the state into `new_container`, which has the target curvature. Under the versioning rule
that is a new container, so the change is explicit and auditable rather than silent. Continuous
adaptation, such as a Ricci-flow-like rule driven by the workload, is deferred (see the open
questions below).

## Open questions (tracked, not resolved)

1. **Cross-curvature invariants.** The linking matrix survives the move from flat to bundle. What
   survives the move from flat to hyperbolic?
2. **Boundary connections.** Composing a container with no boundary (a torus) with one that has a
   boundary (a disk, or a tree with leaves) needs a connection at the boundary. How does that
   connection determine the composite's class beyond the volume rule?
3. **Twisted bundles.** Prove the bundle rule (total class = product class) when the structure
   group is compact and the distortion is bounded, not only for products.
4. **Finer curvature.** Add Ollivier–Ricci for graph carriers, so `positive` can tell spheres apart
   from mere finiteness.
5. **Hosting contracts.** Which of metric, algebra and boundary must be preserved when a
   container is re-hosted (CPU → FPGA → ESP32 → DHT)? The descriptor records `hosting.preserve`.
   Nothing enforces it yet.
6. **Lean modules as containers.** Give Lean modules descriptors, so the build graph can be checked
   for curvature-respecting dependencies.

## Two forms of QBX

The design asks for a "boring, stiff" form and an improved form. The container layer is what
separates them. The **stiff form** is the existing stack: flat namespaces, a linear sequence of
migrations, Python modules. It keeps working unchanged. The **container form** is the same code,
described by descriptors that carry geometry. New work, such as the language-evolution, script
geometry and hardware layers, should be written container-first.
