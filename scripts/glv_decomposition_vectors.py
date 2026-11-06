"""Turn actual arkworks GLV outputs into kernel-checked arithmetic statements."""
import hashlib
import json
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def generate(work):
    # These values select inputs; all expected outputs come from arkworks.
    a = 228988810152649578064853576960394133504
    r = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    values = {0, 1, r - 1, r // 2, (r + 1) // 2, a - 1, a, a + 1}
    for bit in (1, 63, 64, 65, 126, 127, 128, 129, 191, 192, 253, 254):
        values.update((2**bit + delta) % r for delta in (-1, 0, 1))
    rng = random.Random(0xB1_512_381)
    quotients = [0, 1, a // 2, a - 2] + [rng.randrange(a - 1) for _ in range(32)]
    for q in quotients:
        boundary = ((2 * q + 1) * r) // (2 * (a - 1))
        values.update(k for delta in (-1, 0, 1) if 0 <= (k := boundary + delta) < r)
    values.update(rng.randrange(r) for _ in range(64))
    inputs = sorted(values)
    oracle = ROOT / "rust/target/release/glv_decomposition_vectors"
    result = subprocess.run([str(oracle)], input="".join(f"{k}\n" for k in inputs),
                            text=True, capture_output=True, check=True, timeout=60)
    lines = result.stdout.splitlines()
    if len(lines) != len(inputs):
        raise RuntimeError("GLV oracle output count mismatch")
    statements, names, records = [], [], []
    for i, (k, line) in enumerate(zip(inputs, lines)):
        scalar, sign1, mag1, sign2, mag2 = line.split("\t")
        if scalar != str(k) or sign1 not in ("true", "false") or sign2 not in ("true", "false"):
            raise RuntimeError("Malformed GLV oracle record")
        m1, m2 = int(mag1, 16), int(mag2, 16)
        if not 0 <= m1 < r or not 0 <= m2 < r:
            raise RuntimeError("Noncanonical GLV magnitude")
        name = f"case{i:03d}"
        statements.append(
            f"theorem {name} :\n"
            f"  GLVDecomposition.signedMagnitude (GLVDecomposition.components {k}).1 = ({sign1}, {m1}) ∧\n"
            f"  GLVDecomposition.signedMagnitude (GLVDecomposition.components {k}).2 = ({sign2}, {m2}) :=\n"
            f"  by decide +kernel\n#print axioms {name}\n")
        names.append(f"GLVDecompositionVectors.{name}")
        records.append(dict(scalar=k, positive1=sign1 == "true", magnitude1=m1,
                            positive2=sign2 == "true", magnitude2=m2))
    modules = []
    for start in range(0, len(statements), 32):
        path = work / f"GLVDecompositionVectors{start // 32:02d}.lean"
        path.write_text("import GLVDecompositionProof\nnamespace GLVDecompositionVectors\n" +
                        "\n".join(statements[start:start + 32]) +
                        "\nend GLVDecompositionVectors\n")
        modules.append(path)
    fixture = work / "glv-decomposition-arkworks.json"
    fixture.write_text(json.dumps(records, indent=2) + "\n")
    fingerprints = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (
        ROOT / "rust/src/bin/glv_decomposition_vectors.rs",
        ROOT / "curve/GLVDecompositionProof.lean",
        ROOT / "curve/src/glv.rs", ROOT / "curve/src/glv/arithmetic.rs",
        ROOT / "curve/src/field.rs", ROOT / "curve/src/montgomery.rs", Path(__file__).resolve(),
        ROOT / "rust/Cargo.lock", ROOT / "provenance/arkworks-0.5.0.json")}
    return modules, names, dict(cases=len(inputs), minimal_rust_compared=True, source_sha256=fingerprints,
                               fixture=str(fixture.relative_to(ROOT)),
                               fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest())
