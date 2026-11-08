# Phase D — Integration procedure (after the agents finish)

Integration is one serial step, done by the owner or by a single integration
agent once all workstreams have handed off. During the parallel run nothing
outside `phase_d/<ID>_*/` changes, so this is the only point where shared
files are edited.

## 0. Collect

Merge every workstream branch. Each branch adds files only under its own
folder, so the merges cannot conflict. If one does, a hard rule was broken:
reject that branch's out-of-folder changes.

```
cd QBX && ./health.sh            # must be green with all six folders present
```

## 1. Review each STATUS.md

For every workstream, check that each claim in `STATUS.md` is proved, tested,
or explicitly marked open. Lean claims: the file checks in step 0, and the
named theorems exist (`grep` the names). Downgrade any claim that is not
backed.

## 2. Apply manifests in dependency order

Order: **D1 → D2 → D3 → D6 → D5 → D4**. Formal results go first so the docs
can cite them. D4 goes last because it may cite all the others and may want a
new layer.

For each `integration/MANIFEST.md` entry:

* **new**: copy to the destination (Lean files to `QBX/Formal/`, and add the
  `public import` line to `QBX/Formal.lean`).
* **patch** / **replace**: apply, then re-run the owning workstream's
  property tests.
* New Python layers (for example `ws9_protocol/`) need a row in
  `ws8_spec/LAYER_MAP.md` **and** in `LAYERS` of
  `tests/test_fnd_contracts.py`, plus a `PROPERTIES.md` with
  `tests/test_prop_<layer>.py`.
* Registry rows (H-0xx) go into `QBX/Formal/HYPOTHESIS_REGISTRY.md`; SPEC rows
  go into `ws6_certificates/SPEC.md`.

After each workstream: `./health.sh`, then commit.

## 3. Contract amendments (one seal at the end)

1. For each approved draft `FA-NNN`, copy it to
   `ws6_certificates/amendments/`, apply it to `contracts/`, bump
   `INTERFACE_VERSION`, and add a history row in `INTERFACE_FREEZE.md`.
2. Queue the changed files:
   `./seal.sh amend foundation/contracts/<file>.py --amendment FA-NNN --queue-only`.
   The queue refuses conflicting requests, and the seal refuses files that
   changed after they were queued. So queue only after the final edit.
3. Run `./seal.sh` once, review the plan, and enter the key.

Rejected drafts stay in their workstream folder with a one-line reason
appended.

## 4. Close Phase D

* Check the four criteria in `README.md` ("The Phase D goal"), each with a
  pointer to evidence (theorem name, report section, health run).
* Update `MASTER_PLAN.md` (Phase D result), `AGENT_WORKSTREAMS.md` (backlog),
  and `README.md` (layout table).
* Leave `phase_d/` in place as the record, or move it to `phase_d/ARCHIVE/`.
  Code that was integrated should then exist only at its destination.
