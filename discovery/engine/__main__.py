"""Command line driver of the discovery loop.

    python3 -m discovery.engine run [--domains cd_signs,quad_forms,prime_poly]
                                    [--generations 200] [--chains 3] [--max-burn 40]
                                    [--entropy-device /dev/ttyACM0 --device-h 1.0]
                                    [--seed-hex HEX] [--dry-run] [--no-rebuild]
    python3 -m discovery.engine entropy [--entropy-device PATH]   # health-test the sources only
    python3 -m discovery.engine ledger                            # list burned claims

``run`` harvests the entropy pool (or replays ``--seed-hex``), runs the annealing chains, stages
survivors in Lean, burns accepted theorems into ``discovery/Discovery/Ledger/<run>.lean`` and
finally re-checks that module with ``lake build`` (unless ``--no-rebuild``).
"""

from __future__ import annotations

import argparse
import json
import sys
import time

from . import entropy, stager
from .domains import ALL_DOMAINS
from .loop import DiscoveryLoop, RunConfig


def build_seed(args) -> entropy.EntropySeed:
    if args.seed_hex:
        return entropy.replay(args.seed_hex)
    sources = [entropy.OsUrandomSource()]
    if args.entropy_device:
        sources.append(entropy.StreamSource(args.entropy_device, args.device_h))
    return entropy.harvest(sources, n_bytes=args.pool_bytes)


def cmd_entropy(args) -> int:
    seed = build_seed(args)
    print(json.dumps(seed.summary(), indent=2))
    return 0


def cmd_ledger(args) -> int:
    known = stager.Ledger.load_known(stager.LEDGER_JSONL)
    for (kind, _key), rec in sorted(known.items(), key=lambda kv: kv[1]["name"]):
        print(f"[{kind:10s}] {rec['name']}\n             {rec['doc']}")
    print(f"{len(known)} burned claims")
    return 0


def cmd_run(args) -> int:
    names = [n.strip() for n in args.domains.split(",") if n.strip()]
    unknown = [n for n in names if n not in ALL_DOMAINS]
    if unknown:
        print(f"unknown domains: {unknown}; available: {sorted(ALL_DOMAINS)}", file=sys.stderr)
        return 2
    seed = build_seed(args)
    run_name = args.run_name or time.strftime("Run%Y%m%d_%H%M%S_", time.gmtime()) + seed.hex[:8]
    doc = (f"# Discovery run `{run_name}`\n\nClaims burned in by the automated discovery loop "
           f"(`python3 -m discovery.engine run`).  Entropy seed `{seed.hex}` "
           f"(replay with `--seed-hex`); domains: {', '.join(names)}.  Every theorem is a "
           f"closed bounded statement over `Discovery.Kernel`, decided by the Lean kernel.")
    ledger = stager.Ledger(run_name, doc)
    cfg = RunConfig(generations=args.generations, chains_per_domain=args.chains,
                    max_burn=args.max_burn, dry_run=args.dry_run, lake=args.lake,
                    fuzz_samples=args.fuzz)
    loop = DiscoveryLoop([ALL_DOMAINS[n] for n in names], seed, cfg, run_name, ledger)
    stats = loop.run()
    print(json.dumps({"run": run_name, "seed_hex": seed.hex, "stats": stats.__dict__,
                      "journal": str(loop.journal_path.relative_to(stager.REPO_ROOT))}, indent=2))
    for rec in ledger.burned:
        print(f"  burned [{rec['kind']}] {rec['name']}: {rec['doc']}")
    if ledger.burned and not args.no_rebuild and not args.dry_run:
        ok, out = ledger.rebuild(lake=args.lake)
        print(f"lake build {ledger.module}: {'OK' if ok else 'FAILED'}")
        if not ok:
            print(out)
            return 1
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="python3 -m discovery.engine")
    sub = p.add_subparsers(dest="cmd", required=True)
    for name in ("run", "entropy"):
        sp = sub.add_parser(name)
        sp.add_argument("--entropy-device", default=None)
        sp.add_argument("--device-h", type=float, default=1.0,
                        help="declared min-entropy per byte of the device stream")
        sp.add_argument("--pool-bytes", type=int, default=4096)
        sp.add_argument("--seed-hex", default=None)
        if name == "run":
            sp.add_argument("--domains", default=",".join(ALL_DOMAINS))
            sp.add_argument("--generations", type=int, default=200)
            sp.add_argument("--chains", type=int, default=3)
            sp.add_argument("--max-burn", type=int, default=40)
            sp.add_argument("--fuzz", type=int, default=64)
            sp.add_argument("--run-name", default=None)
            sp.add_argument("--lake", default="lake")
            sp.add_argument("--dry-run", action="store_true")
            sp.add_argument("--no-rebuild", action="store_true")
    sub.add_parser("ledger")
    args = p.parse_args(argv)
    return {"run": cmd_run, "entropy": cmd_entropy, "ledger": cmd_ledger}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
