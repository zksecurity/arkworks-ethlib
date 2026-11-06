#!/usr/bin/env python3
"""Generate literal vector statements and prove them with Lean's kernel evaluator."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from differential import verify_vendor
from rfc9380_vectors import fixtures as rfc_fixtures
from eip2537_vectors import fixtures as eip_fixtures
from published_vectors import digest, fixtures, FIXTURES, ROOT

HEADER = """-- Generated from hash-checked published fixtures; do not edit expectations.
import ArkEth
open EthLib.Cryptography.Bls
namespace PublishedVectors
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
"""
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def byte_literal(encoded):
    return "ByteArray.mk #[" + ", ".join(str(b) for b in bytes.fromhex(encoded)) + "]"


def generate(work, encodings, decoding, rfc_points, multiplication_vectors):
    modules = []
    for start in range(0, len(encodings), 25):
        body, names = [], []
        for n in range(start, min(start + 25, len(encodings))):
            name = f"zkcrypto_{n:04d}"
            body.append(f"def {name} : ByteArray := {byte_literal(encodings[n])}\n")
            for suffix, proposition in (
                ("encoding", f"G1.compress (G1.mulNat G1.generator {n}) = {name}"),
                ("decoding", f"ArkEth.decodeObservation {name} = some {name}"),
            ):
                theorem = f"{name}_{suffix}"
                body.append(f"theorem {theorem} : {proposition} := by decide +kernel\n"
                            f"#print axioms {theorem}\n")
                names.append(f"PublishedVectors.{theorem}")
        modules.append((f"Zkcrypto{start // 25:02d}", body, names))
    body, names = [], []
    for case, encoded, accepted in decoding:
        # Only identifiers from fixture filenames enter Lean source.
        if not re.fullmatch(r"[a-zA-Z_][a-zA-Z0-9_]*", case):
            raise ValueError(f"Invalid fixture identifier: {case}")
        name = f"ethereum_{case}"
        body.append(f"def {name} : ByteArray := {byte_literal(encoded)}\n")
        expected = f"some {name}" if accepted else "none"
        theorem = f"{name}_correct"
        body.append(f"theorem {theorem} : ArkEth.decodeObservation {name} = {expected} := by decide +kernel\n"
                    f"#print axioms {theorem}\n")
        names.append(f"PublishedVectors.{theorem}")
    modules.append(("Ethereum", body, names))
    body, names = [], []
    for section, case, label, x, y in rfc_points:
        name = f"rfc9380_{section.replace('.', '_')}_{case}_{label}"
        body.append(f"def {name} : G1 := ⟨Fp.ofNat 0x{x}, Fp.ofNat 0x{y}, Fp.one⟩\n")
        theorem = f"{name}_curve"
        proposition = (f"0x{x} < Fp.modulus ∧ 0x{y} < Fp.modulus ∧ "
                       f"{name}.y * {name}.y = {name}.x * {name}.x * {name}.x + Fp.ofNat 4")
        body.append(f"theorem {theorem} : {proposition} := by decide +kernel\n#print axioms {theorem}\n")
        names.append(f"PublishedVectors.{theorem}")
        if label == "P":
            theorem = f"{name}_subgroup"
            body.append(f"theorem {theorem} : G1.inSubgroup {name} = true := by decide +kernel\n"
                        f"#print axioms {theorem}\n")
            names.append(f"PublishedVectors.{theorem}")
    # Appendix J.9 gives the inputs and expected outputs of these group operations.
    for section in ("J.9.1", "J.9.2"):
        for case in range(5):
            prefix = f"rfc9380_{section.replace('.', '_')}_{case}"
            argument = f"G1.add {prefix}_Q0 {prefix}_Q1" if section == "J.9.1" else f"{prefix}_Q"
            theorem = f"{prefix}_cofactor_result"
            proposition = (f"G1.toAffine (G1.mulNat ({argument}) 0xd201000000010001) = "
                           f"({prefix}_P.x, {prefix}_P.y)")
            body.append(f"theorem {theorem} : {proposition} := by decide +kernel\n"
                        f"#print axioms {theorem}\n")
            names.append(f"PublishedVectors.{theorem}")
    modules.append(("Rfc9380", body, names))
    body, names = [], []
    for index, case in enumerate(multiplication_vectors):
        data = bytes.fromhex(case["Input"])
        expected = bytes.fromhex(case["Expected"])
        x, y = int.from_bytes(data[:64], "big"), int.from_bytes(data[64:128], "big")
        scalar = int.from_bytes(data[128:], "big")
        ex, ey = int.from_bytes(expected[:64], "big"), int.from_bytes(expected[64:], "big")
        name = f"eip2537_mul_{index:02d}"
        point = "G1.zero" if x == y == 0 else f"⟨Fp.ofNat {x}, Fp.ofNat {y}, Fp.one⟩"
        body.append(f"def {name} : G1 := {point}\n")
        theorem = f"{name}_result"
        proposition = (f"G1.toAffine (G1.mulNat {name} {scalar}) = "
                       f"(Fp.ofNat {ex}, Fp.ofNat {ey})")
        body.append(f"theorem {theorem} : {proposition} := by decide +kernel\n#print axioms {theorem}\n")
        names.append(f"PublishedVectors.{theorem}")
    modules.append(("Eip2537", body, names))
    result = []
    for module, body, names in modules:
        path = work / f"{module}.lean"
        path.write_text(HEADER + "\n".join(body) + "\nend PublishedVectors\n")
        result.append((path, set(names)))
    (work / "PublishedVectors.lean").write_text(
        "-- Import the complete checked corpus.\n" +
        "\n".join(f"import {p.stem}" for p, _ in result) + "\n")
    return result


def audit(log, required):
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    found += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    if len(found) != len(required) or {name for name, _ in found} != required:
        raise AssertionError("Missing or duplicate theorem axiom audit")
    result = {}
    for name, axioms in found:
        used = set(re.findall(r"[\w.]+", axioms))
        if not used <= ALLOWED_AXIOMS:
            raise AssertionError(f"Unexpected axioms in {name}: {used}")
        result[name] = sorted(used)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4, help="parallel Lean processes (default: 4)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="vector-proof-", dir=build))
    report_path = build / "vector-proof.json"
    report = {"status": "running", "work_directory": str(work.relative_to(ROOT)),
              "kernel_checked": False, "ietf_conformance_proved": False,
              "method": "decide +kernel", "jobs": args.jobs}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    started = time.monotonic()
    try:
        manifest, encodings, decoding = fixtures()
        report["ethlib_revision"] = verify_vendor()["revision"]
        report["sources"] = [{k: s[k] for k in ("repository", "revision")}
                             for s in manifest["sources"]]
        report["manifest_sha256"] = digest(FIXTURES / "provenance.json")
        report["generator_sha256"] = digest(Path(__file__))
        report["lean_toolchain"] = (ROOT / "lean/lean-toolchain").read_text().strip()
        rfc_points = rfc_fixtures()
        modules = generate(work, encodings, decoding, rfc_points, eip_fixtures()["mul"])
        report["generated_sha256"] = {p.name: digest(p) for p in work.glob("*.lean")}
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(
            (str(work), str(ROOT / "lean/.lake/build/lib/lean"))))

        def compile_module(path):
            log_path = path.with_suffix(".log")
            with log_path.open("w") as log:
                subprocess.run(["lake", "env", "lean", f"--root={work}",
                                "-o", str(path.with_suffix(".olean")), str(path)],
                               cwd=ROOT / "lean", env=env, stdout=log,
                               stderr=subprocess.STDOUT, timeout=600, check=True)
            return log_path.read_text()

        subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True, timeout=180)
        audits = {}
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            pending = {executor.submit(compile_module, p): (p, names) for p, names in modules}
            for count, future in enumerate(as_completed(pending), 1):
                path, required = pending[future]
                audits.update(audit(future.result(), required))
                print(f"Checked {count}/{len(modules)} modules; {len(audits)} theorems audited.", flush=True)
        # Check that the individual modules can be imported together without collisions.
        compile_module(work / "PublishedVectors.lean")
        if len(audits) != 2069:
            raise AssertionError(f"Expected 2069 vector theorems, got {len(audits)}")
        report.update(status="passed", kernel_checked=True,
                      encoding_theorems=len(encodings), decoding_theorems=len(encodings) + len(decoding),
                      rfc9380_curve_theorems=25, rfc9380_subgroup_theorems=10, rfc9380_group_operation_theorems=10,
                      eip2537_multiplication_theorems=11, pairing_refinement_proved=False,
                      hash_to_curve_implemented=False, axiom_audit=audits, checked_theorems=len(audits))
        print("PASS: all 2069 published-vector theorems checked by Lean's kernel.")
        print("Axiom audit: propext and Quot.sound only.")
        print(f"Importable proofs: {work.relative_to(ROOT)}/PublishedVectors.lean")
    except Exception as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 2)
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
