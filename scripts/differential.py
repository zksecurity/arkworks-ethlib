#!/usr/bin/env python3
"""Compare executable implementations; this is testing, not a universal proof."""
import hashlib
import json
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
P = int("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624"
        "1eabfffeb153ffffb9feffffffffaaab", 16)
GENERATOR = "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
INFINITY = "c0" + "00" * 47


def run(binary, commands):
    result = subprocess.run([str(binary)], input="\n".join(commands) + "\n",
                            text=True, capture_output=True, timeout=180, check=True)
    lines = result.stdout.splitlines()
    if len(lines) != len(commands):
        raise AssertionError(f"{binary}: expected {len(commands)} results, got {len(lines)}")
    return lines


def verify_vendor():
    base = ROOT / "lean/vendor/ethlib"
    manifest = json.loads((base / "provenance.json").read_text())
    for name, digest in manifest["files"].items():
        if hashlib.sha256((base / name).read_bytes()).hexdigest() != digest:
            raise AssertionError(f"Vendored upstream file changed: {name}")
    return manifest


def main():
    report_path = ROOT / "build/differential.json"
    report_path.parent.mkdir(exist_ok=True)
    # A failed rerun must not leave an old passing report behind.
    report_path.write_text(json.dumps({"status": "running", "equivalence_proved": False}) + "\n")
    manifest = verify_vendor()
    rust = ROOT / "rust/target/release/codec"
    lean = ROOT / "lean/.lake/build/bin/ethlib_codec"
    rng = random.Random(0xAEEA5)
    scalars = list(range(128)) + [2**k for k in range(7, 64)]
    scalars += [2**64 - 1] + [rng.getrandbits(64) for _ in range(64)]
    commands = [f"encode\t{n}" for n in scalars]
    rust_enc, lean_enc = run(rust, commands), run(lean, commands)
    minimal_enc = run(rust, [f"encode_minimal\t{n}" for n in scalars])
    for cmd, actual, reference in zip(commands, minimal_enc, rust_enc):
        if actual != reference:
            raise AssertionError(f"Minimal serializer mismatch: {cmd}\n{actual}\n{reference}")
    for cmd, a, b in zip(commands, rust_enc, lean_enc):
        if a != b or not a.startswith("ok\t"):
            raise AssertionError(f"{cmd}\nRust: {a}\nLean: {b}")
    if rust_enc[0].split("\t")[-1] != INFINITY:
        raise AssertionError("Unexpected infinity vector")
    if rust_enc[1].split("\t")[-1] != GENERATOR:
        raise AssertionError("Unexpected standard generator vector")

    cases = []

    def add(name, encoded, expected=None):
        cases.append((name, f"decode\t{encoded}", expected))

    for n, result in zip(scalars, rust_enc):
        encoded = result.split("\t")[-1]
        add(f"roundtrip_{n}", encoded, f"ok\t{encoded}")
    negative = bytes([int(GENERATOR[:2], 16) ^ 0x20]).hex() + GENERATOR[2:]
    add("negative_generator", negative, f"ok\t{negative}")
    for length in [0, 1, 31, 47, 49, 64, 96, 192]:
        add(f"wrong_length_{length}", "00" * length, "invalid")
    add("trailing_byte", GENERATOR + "00", "invalid")
    add("truncated_point", GENERATOR[:-2], "invalid")
    add("not_hex", "zz" * 48, "invalid")
    add("odd_hex", GENERATOR[:-1], "invalid")
    for first in range(0, 256, 32):
        encoded = f"{first:02x}" + "00" * 47
        # Compressed x=0 gives a curve point outside the prime-order subgroup.
        add(f"zero_payload_flags_{first:02x}", encoded,
            f"ok\t{INFINITY}" if first == 0xc0 else "invalid")
    add("infinity_nonzero_tail", "c0" + "00" * 46 + "01", "invalid")
    add("infinity_nonzero_coordinate", "c1" + "00" * 47, "invalid")
    for coordinate in [P, P + 1, 2**381 - 1]:
        for sign in [0, 0x20]:
            data = bytearray(coordinate.to_bytes(48, "big"))
            data[0] |= 0x80 | sign
            add(f"noncanonical_{coordinate}_{sign}", data.hex(), "invalid")
    # Every individual bit of a valid encoding, including all three flags.
    for i in range(48):
        for bit in range(8):
            data = bytearray.fromhex(GENERATOR)
            data[i] ^= 1 << bit
            add(f"mutate_{i}_{bit}", data.hex())
    for i in range(128):
        data = bytearray(rng.randbytes(48))
        data[0] = (data[0] & 0x1f) | 0x80
        add(f"random_compressed_{i}", data.hex())
    for i in range(64):
        coordinate = rng.randrange(P)
        data = bytearray(coordinate.to_bytes(48, "big"))
        data[0] |= 0x80 | (rng.randrange(2) << 5)
        add(f"canonical_random_x_{i}", data.hex())

    decode_commands = [cmd for _, cmd, _ in cases]
    rust_dec, lean_dec = run(rust, decode_commands), run(lean, decode_commands)
    minimal_dec = run(rust, [cmd.replace("decode\t", "decode_minimal\t", 1) for cmd in decode_commands])
    failures = []
    for (name, cmd, expected), a, b, c in zip(cases, rust_dec, lean_dec, minimal_dec):
        if a != b or a != c or (expected is not None and a != expected):
            failures.append({"case": name, "command": cmd, "rust": a,
                             "lean": b, "minimal": c, "expected": expected})
    report = {
        "status": "failed" if failures else "passed",
        "kind": "executable differential tests; not a proof of equivalence",
        "ethlib_revision": manifest["revision"],
        "arkworks_version": "0.5.0",
        "encode_cases": len(commands),
        "minimal_encode_cases": len(commands),
        "decode_cases": len(cases),
        "minimal_decode_cases": len(cases),
        "decode_accepted": sum(x.startswith("ok\t") for x in rust_dec),
        "decode_rejected": sum(x == "invalid" for x in rust_dec),
        "failures": failures,
        "binaries_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in (rust, lean)},
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if failures:
        raise AssertionError(json.dumps(failures[:5], indent=2))
    print(f"PASS: {len(commands)} encodings and {len(cases)} decodings agree.")
    print(f"Minimal Rust agrees on all {len(commands)} encoding and {len(cases)} decoding cases.")
    print(f"Decoder: {report['decode_accepted']} accepted, {report['decode_rejected']} rejected.")
    print("Report: build/differential.json. Aeneas equivalence is NOT established by these tests.")


if __name__ == "__main__":
    main()
