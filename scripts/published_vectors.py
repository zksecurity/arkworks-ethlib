#!/usr/bin/env python3
"""Check implementations against pinned external G1 bytes and acceptance results."""
import hashlib
import json
from pathlib import Path

from differential import run, verify_vendor

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "test-vectors"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixtures():
    manifest = json.loads((FIXTURES / "provenance.json").read_text())
    for source in manifest["sources"]:
        for name, entry in source["files"].items():
            path = FIXTURES / source["directory"] / name
            if digest(path) != entry["sha256"]:
                raise AssertionError(f"Published fixture changed: {path}")
    data = (FIXTURES / "zkcrypto/g1_compressed_valid_test_vectors.dat").read_bytes()
    if len(data) != 1000 * 48:
        raise AssertionError("Expected 1000 published 48-byte G1 encodings")
    # Upstream src/tests/mod.rs starts at identity and repeatedly adds the generator.
    encodings = [data[i:i + 48].hex() for i in range(0, len(data), 48)]
    decoding = []
    for path in sorted((FIXTURES / "ethereum").glob("*.json")):
        case = json.loads(path.read_text())
        encoded = case["input"]["pubkey"].removeprefix("0x")
        if not isinstance(case["output"], bool):
            raise AssertionError(f"Invalid acceptance expectation: {path}")
        decoding.append((path.stem, encoded, case["output"]))
    if len(decoding) != 13:
        raise AssertionError("Expected all 13 Ethereum v0.1.2 G1 deserialization cases")
    return manifest, encodings, decoding


def main():
    report_path = ROOT / "build/published-vectors.json"
    report_path.parent.mkdir(exist_ok=True)
    report = {"status": "running", "ietf_conformance_proved": False,
              "minimal_decoder_exists": True}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        manifest, encodings, decoding = fixtures()
        report["ethlib_revision"] = verify_vendor()["revision"]
        report["sources"] = [{k: s[k] for k in ("repository", "revision")}
                             for s in manifest["sources"]]
        report["manifest_sha256"] = digest(FIXTURES / "provenance.json")
        curve = ROOT / "rust/target/release/curve_codec"
        rust = ROOT / "rust/target/release/codec"
        lean = ROOT / "lean/.lake/build/bin/ethlib_codec"
        report["binaries_sha256"] = {str(p.relative_to(ROOT)): digest(p)
                                     for p in (curve, rust, lean)}
        failures = []
        # This uses the concrete minimal scalar multiplication, affine conversion,
        # and formatter. The second output column is independent arkworks output.
        actual = run(curve, [f"mul256\t1\t{n:064x}" for n in range(1000)])
        spec = run(lean, [f"encode\t{n}" for n in range(1000)])
        for n, (expected, a, b) in enumerate(zip(encodings, actual, spec)):
            aa, bb = a.split("\t"), b.split("\t")
            if not (len(aa) == 9 and aa[0] == "ok" and aa[3:6] == aa[6:9] and
                    aa[1] == aa[2] == expected and
                    len(bb) == 4 and bb[0] == "ok" and bb[3] == expected):
                failures.append({"case": f"zkcrypto/{n}", "expected": expected,
                                 "minimal_and_arkworks": a, "ethlib": b})
        # Decoders accept infinity as a group element. This is not BLS KeyValidate,
        # which rejects infinity.
        cases = [(f"zkcrypto/{n}", b, True) for n, b in enumerate(encodings)] + decoding
        for implementation, binary, command in (("arkworks", rust, "decode"),
                                                 ("ethlib", lean, "decode"),
                                                 ("minimal", rust, "decode_minimal")):
            commands = [f"{command}\t{encoded}" for _, encoded, _ in cases]
            for (name, encoded, accepted), actual in zip(cases, run(binary, commands)):
                expected = f"ok\t{encoded}" if accepted else "invalid"
                if actual != expected:
                    failures.append({"case": name, "implementation": implementation,
                                     "expected": expected, "actual": actual})
        report.update(encoding_vectors=len(encodings), decoding_vectors=len(cases),
                      ethereum_acceptances=sum(ok for _, _, ok in decoding),
                      ethereum_rejections=sum(not ok for _, _, ok in decoding),
                      failures=failures)
        if failures:
            raise AssertionError(json.dumps(failures[:10], indent=2))
        report["status"] = "passed"
        print("PASS: 1000 published zkcrypto encodings match concrete Rust, arkworks, and EthLib.")
        print("PASS: minimal Rust, arkworks and EthLib decode/re-encode all 1000 vectors and match all 13 Ethereum cases.")
    except Exception as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
