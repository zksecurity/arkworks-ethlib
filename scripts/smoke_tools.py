#!/usr/bin/env python3
"""Check installation by translating real Rust and checking a theorem about it."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    tool = Path(os.environ.get("AENEAS_DIR", ROOT / ".tools/aeneas")).resolve()
    backend = tool / "backends/lean"
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="smoke-", dir=build))
    shutil.copytree(ROOT / "smoke", work / "rust")
    shutil.copyfile(ROOT / "smoke/Proof.lean", work / "Proof.lean")
    env = dict(os.environ, CARGO_HOME=str(ROOT / ".cache/cargo"), LEAN_PATH=str(work))
    report_path = build / "smoke.json"
    report = {"status": "running", "scope": "compression-flag smoke test, not arkworks equivalence",
              "work_directory": str(work.relative_to(ROOT)),
              "rust_sha256": hashlib.sha256((ROOT / "smoke/src/lib.rs").read_bytes()).hexdigest()}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    commands = [
        (work / "rust", [tool / "charon/bin/charon", "cargo", "--preset=aeneas",
                         "--dest-file", work / "smoke.llbc", "--", "--lib"]),
        (work, [tool / "bin/aeneas", "-backend", "lean", work / "smoke.llbc", "-dest", work,
                "-subdir", "Generated", "-namespace", "ToolSmoke"]),
        (backend, ["lake", "env", "lean", f"--root={work}", "-o",
                   work / "Generated/Smoke.olean", work / "Generated/Smoke.lean"]),
        (backend, ["lake", "env", "lean", f"--root={work}", work / "Proof.lean"]),
    ]
    try:
        with (build / "smoke.log").open("w") as log:
            for cwd, command in commands:
                print("Running:", " ".join(map(str, command)), file=log, flush=True)
                subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                               stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)
        report["status"] = "passed"
        report["generated_sha256"] = hashlib.sha256((work / "Generated/Smoke.lean").read_bytes()).hexdigest()
        print("PASS: Rust → Charon → Aeneas → Lean, with a checked compression-flag theorem.")
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        report.update(status="failed", reason=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
