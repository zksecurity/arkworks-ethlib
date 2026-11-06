#!/usr/bin/env python3
"""Extract the dependency-free formatter and check its EthLib refinement proof."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from differential import verify_vendor

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    tool = Path(os.environ.get("AENEAS_DIR", ROOT / ".tools/aeneas")).resolve()
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="minimal-", dir=build))
    rust = work / "rust"
    rust.mkdir()
    for name in ("Cargo.toml", "Cargo.lock"):
        shutil.copyfile(ROOT / "minimal" / name, rust / name)
    shutil.copytree(ROOT / "minimal/src", rust / "src")
    shutil.copyfile(ROOT / "minimal/Proof.lean", work / "Proof.lean")
    report_path = build / "minimal.json"
    report = {
        "status": "running",
        "scope": "48-byte formatter from canonical x bytes, y-sign, and infinity",
        "minimal_refines_ethlib": False,
        "full_arkworks_equivalence_proved": False,
        "work_directory": str(work.relative_to(ROOT)),
        "rust_sha256": sha256(rust / "src/lib.rs"),
        "proof_sha256": sha256(work / "Proof.lean"),
        "boundary": "x bytes equal EthLib x.toBytesBE; sign equals EthLib Fp.signBit y",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    env = dict(os.environ, CARGO_HOME=str(ROOT / ".cache/cargo"),
               LEAN_PATH=os.pathsep.join((str(work), str(ROOT / "lean/.lake/build/lib/lean"))))
    generated = work / "Generated/MinimalG1.lean"
    log_path = build / "minimal.log"
    try:
        report["ethlib_revision"] = verify_vendor()["revision"]
        with log_path.open("w") as log:
            def run(cwd, command):
                print("Running:", " ".join(map(str, command)), file=log, flush=True)
                subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                               stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)

            run(ROOT, [sys.executable, "scripts/extract.py", "--check"])
            run(ROOT / "lean", ["lake", "build"])
            run(rust, [tool / "charon/bin/charon", "cargo", "--preset=aeneas",
                       "--error-on-warnings", "--dest-file", work / "minimal_g1.llbc",
                       "--", "--lib", "--offline", "--locked"])
            run(work, [tool / "bin/aeneas", "-backend", "lean", work / "minimal_g1.llbc",
                       "-dest", work, "-subdir", "Generated", "-namespace", "MinimalG1"])
            files = list((work / "Generated").glob("*.lean"))
            if files != [generated]:
                raise RuntimeError(f"Unexpected generated files: {files}")
            for source in (generated, work / "Proof.lean"):
                if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source.read_text()):
                    raise RuntimeError(f"Unreviewed proof shortcut in {source}")
            run(tool / "backends/lean", ["lake", "env", "lean", f"--root={work}",
                                        "-o", generated.with_suffix(".olean"), generated])
            run(tool / "backends/lean", ["lake", "env", "lean", "-DautoImplicit=false",
                                        "-DwarningAsError=true", f"--root={work}",
                                        "-o", work / "Proof.olean", work / "Proof.lean"])
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_path.read_text())
        required = {"MinimalProof.encode_flags_total", "MinimalProof.compress_total", "MinimalProof.compress_refines_ethlib"}
        if {name for name, _ in audits} != required:
            raise RuntimeError("Missing theorem axiom audit")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for name, axioms in audits:
            if not set(axioms.split(", ")).issubset(allowed):
                raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
        report.update(status="passed", minimal_refines_ethlib=True,
                      generated_sha256=sha256(generated), axiom_audit=dict(audits))
        print("PASS: extracted minimal Rust formatter is total and refines EthLib under the affine input contract.")
        print(f"Generated Lean and checked proof: {work.relative_to(ROOT)}")
        print("Montgomery conversion, sign computation, and full arkworks equivalence are outside this proof.")
    except Exception as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
