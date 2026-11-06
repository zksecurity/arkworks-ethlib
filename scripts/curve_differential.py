#!/usr/bin/env python3
"""Three-way executable checks: concrete minimal Rust, arkworks, and EthLib."""
from collections import Counter
import hashlib
import json
import random
from pathlib import Path

from differential import run, verify_vendor

ROOT = Path(__file__).resolve().parents[1]
R = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def main():
    path = ROOT / "build/curve-differential.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps({"status": "running", "full_arkworks_equivalence_proved": False}) + "\n")
    revision = verify_vendor()["revision"]
    commands = []
    for n in [0, 1, 2, 3, 17, 63, 2**63, 2**64-1]:
        commands.extend([f"neg\t{n}", f"double\t{n}"])
        for m in [0, 1, n, 73]:
            commands.append(f"add\t{n}\t{m}")
        for k in [0, 1, 2, 3, 2**64-1]:
            commands.append(f"mul\t{n}\t{k}")
    rng = random.Random(0xEC_AEEA5)
    for _ in range(16):
        commands.append(f"add\t{rng.getrandbits(64)}\t{rng.getrandbits(64)}")
        commands.append(f"mul\t{rng.getrandbits(64)}\t{rng.getrandbits(64)}")
    for k in [0, 1, R-1, R, R+1, 2**255, 2**256-1] + [rng.getrandbits(256) for _ in range(8)]:
        commands.append(f"mul256\t17\t{k:064x}")
    rust = ROOT / "rust/target/release/curve_codec"
    lean = ROOT / "lean/.lake/build/bin/ethlib_codec"
    actual = run(rust, commands)
    expected = run(lean, ["curve\t" + c for c in commands])
    failures = []
    raw_checks = 0
    arkworks_raw_checks = 0
    for command, a, b in zip(commands, actual, expected):
        aa, bb = a.split("\t"), b.split("\t")
        good = len(aa) == 9 and len(bb) == 5 and aa[0] == bb[0] == "ok"
        if good:
            good = aa[1] == aa[2] == bb[1]
            arkworks_raw_checks += 1
            good = good and aa[3:6] == aa[6:9]
            if command.split("\t")[0] in ("neg", "double", "add"):
                raw_checks += 1
                good = good and aa[3:6] == bb[2:]
        if not good:
            failures.append({"command": command, "rust": a, "ethlib": b})
    report = {"status": "failed" if failures else "passed", "cases": len(commands),
              "operations": dict(Counter(c.split("\t")[0] for c in commands)),
              "raw_jacobian_comparisons": raw_checks, "arkworks_raw_jacobian_comparisons": arkworks_raw_checks, "ethlib_revision": revision,
              "full_arkworks_equivalence_proved": False, "failures": failures,
              "binaries_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in (rust, lean)}}
    path.write_text(json.dumps(report, indent=2) + "\n")
    if failures:
        raise AssertionError(json.dumps(failures[:3], indent=2))
    print(f"PASS: {len(commands)} curve operations agree across minimal Rust, arkworks, and EthLib.")
    print(f"Compared {arkworks_raw_checks} raw Jacobian triples with arkworks and {raw_checks} nonscalar triples with EthLib. Scalar schedules retain source coordinates; their EthLib group/encoding bridges are proved separately.")


if __name__ == "__main__":
    main()
