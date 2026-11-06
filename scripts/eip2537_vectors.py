#!/usr/bin/env python3
"""Executable EIP-2537 multiplication and pairing comparisons; not pairing proofs."""
import json
import subprocess

from differential import run, verify_vendor
from published_vectors import ROOT, FIXTURES, digest, fixtures as verify_fixtures


def fixtures():
    result = {}
    for operation, filename, count in (("mul", "mul_G1_bls.json", 11),
                                       ("pair", "pairing_check_bls.json", 15)):
        cases = json.loads((FIXTURES / "eip2537" / filename).read_text())
        if len(cases) != count:
            raise AssertionError(f"Expected {count} official {operation} vectors")
        for case in cases:
            data, expected = bytes.fromhex(case["Input"]), bytes.fromhex(case["Expected"])
            if operation == "mul":
                if len(data) != 160 or len(expected) != 128:
                    raise AssertionError("Unexpected G1 multiplication vector framing")
            elif not data or len(data) % 384 or len(expected) != 32 or int.from_bytes(expected, "big") not in (0, 1):
                raise AssertionError("Unexpected pairing vector framing")
        result[operation] = cases
    return result


def main():
    path = ROOT / "build/eip2537-vectors.json"
    path.parent.mkdir(exist_ok=True)
    report = {"status": "running", "rust_to_ethlib_proof_report": "build/curve-proof.json", "minimal_rust_pairing_checked": False, "prepared_rust_pairing_checked": False, "prepared_pairing_proof_source": "curve/PreparedPairingEquivalence.lean",
              "prepared_pairing_proof_domain": "canonical coordinates; finite G2 points normalize to on-curve r-torsion points; see the separate fresh proof report",
              "gas_checked": False, "full_precompile_conformance_proved": False}
    path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        manifest, _, _ = verify_fixtures()
        report["ethlib_revision"] = verify_vendor()["revision"]
        report["source"] = next(s for s in manifest["sources"] if s["directory"] == "eip2537")
        cases = fixtures()
        rust = ROOT / "rust/target/release/pairing_example"
        lean = ROOT / "lean/.lake/build/bin/pairing_example"
        report["binaries_sha256"] = {str(p.relative_to(ROOT)): digest(p) for p in (rust, lean)}
        failures = []
        for operation, vectors in cases.items():
            commands = [f"{operation}\t{c['Input']}" for c in vectors]
            for implementation, binary in (("rust", rust), ("ethlib", lean)):
                for case, actual in zip(vectors, run(binary, commands)):
                    if operation == "mul":
                        expected = case["Expected"].lower()
                        wanted = f"mul\t{expected}\t{expected}" if implementation == "rust" else f"mul\t{expected}"
                    else:
                        expected = str(bool(int(case["Expected"], 16))).lower()
                        wanted = f"pair\t{expected}"
                    if actual != wanted:
                        failures.append({"case": case["Name"], "implementation": implementation,
                                         "expected": wanted, "actual": actual})
        expected_demo = ["cancellation\ttrue", "non_degeneracy\tfalse", "bilinearity\ttrue",
                         "wrong_scalar\tfalse", "identity\ttrue"]
        for binary in (rust, lean):
            actual = subprocess.run([str(binary), "--demo"], text=True, capture_output=True,
                                    timeout=180, check=True).stdout.splitlines()
            if actual != expected_demo:
                failures.append({"example": str(binary), "expected": expected_demo, "actual": actual})
        malformed = ["pair\t", "pair\t" + "00" * 385, "pair\tzz", "mul\t" + "00" * 159]
        for binary in (rust, lean):
            if run(binary, malformed) != ["invalid"] * len(malformed):
                failures.append({"malformed_input": str(binary)})
        report.update(multiplication_vectors=11, pairing_vectors=15, demo_cases=5, failures=failures)
        if failures:
            raise AssertionError(json.dumps(failures[:10], indent=2))
        report.update(status="passed", minimal_rust_pairing_checked=True, prepared_rust_pairing_checked=True)
        print("PASS: 11 EIP-2537 G1 multiplication vectors match minimal Rust, arkworks, and current EthLib.")
        print("PASS: 15 published pairing checks and 5 example checks match the default prepared Rust path, arkworks and EthLib.")
        print("Executable comparisons only; prepared Rust/EthLib equivalence on the finite-G2 subgroup domain is audited separately in build/curve-proof.json.")
    except Exception as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
