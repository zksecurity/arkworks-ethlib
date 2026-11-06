#!/usr/bin/env python3
"""Attempt genuine Charon/Aeneas extraction. Never synthesize missing Rust models."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def git_revision(path):
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()


def save_report(report):
    (ROOT / "build").mkdir(exist_ok=True)
    name = "toolchain-check.json" if report.get("kind") == "toolchain_check" else "extraction.json"
    (ROOT / "build" / name).write_text(json.dumps(report, indent=2) + "\n")


def run(command, cwd, report):
    command = list(map(str, command))
    report.setdefault("commands", []).append(command)
    save_report(report)
    print("Running:", " ".join(command), flush=True)
    env = dict(os.environ)
    if (ROOT / ".cache/cargo/registry").is_dir():
        env["CARGO_HOME"] = str(ROOT / ".cache/cargo")
    subprocess.run(command, cwd=cwd, check=True, env=env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check tools without extracting")
    args = parser.parse_args()
    report = {"status": "checking", "equivalence_proved": False,
              "kind": "toolchain_check" if args.check else "extraction"}
    local_tools = ROOT / ".tools/aeneas"
    location = os.environ.get("AENEAS_DIR") or (str(local_tools) if local_tools.is_dir() else None)
    if not location:
        report.update(status="blocked", reason="AENEAS_DIR is unset; no installed translator was found.")
        save_report(report)
        sys.exit("Run make install-tools with network access, or set AENEAS_DIR to a built Aeneas checkout.\n"
                 "No Rust extraction or equivalence proof has run. See README.md.")
    aeneas_dir = Path(location).expanduser().resolve()
    charon_dir = aeneas_dir / "charon"
    aeneas, charon = aeneas_dir / "bin/aeneas", charon_dir / "bin/charon"
    required = [aeneas, charon, aeneas_dir / "charon-pin",
                aeneas_dir / "backends/lean/lean-toolchain"]
    missing = [str(p) for p in required if not p.exists()]
    if missing:
        report.update(status="blocked", reason="Missing toolchain files", missing=missing)
        save_report(report)
        sys.exit("Missing: " + ", ".join(missing))
    for p in [aeneas, charon]:
        if not os.access(p, os.X_OK):
            sys.exit(f"Not executable: {p}")
    expected = json.loads((ROOT / "toolchain.json").read_text())
    actual = {
        "aeneas_revision": git_revision(aeneas_dir),
        "charon_revision": git_revision(charon_dir),
        "lean_toolchain": (aeneas_dir / "backends/lean/lean-toolchain").read_text().strip(),
    }
    mismatches = {key: {"expected": expected[key], "actual": value}
                  for key, value in actual.items() if value != expected[key]}
    if mismatches:
        report.update(status="blocked", reason="Installed tools do not match toolchain.json",
                      mismatches=mismatches)
        save_report(report)
        sys.exit(report["reason"])
    pins = (aeneas_dir / "charon-pin").read_text().splitlines()
    pin = next(s.strip() for s in pins if s.strip() and not s.startswith("#"))
    charon_rev = git_revision(charon_dir)
    if charon_rev != pin:
        report.update(status="blocked", reason="Charon does not match Aeneas charon-pin",
                      expected=pin, actual=charon_rev)
        save_report(report)
        sys.exit(report["reason"])
    report.update(aeneas_revision=git_revision(aeneas_dir), charon_revision=charon_rev,
                  lean_toolchain=(aeneas_dir / "backends/lean/lean-toolchain").read_text().strip())
    if args.check:
        report["status"] = "tools_found_extraction_not_run"
        save_report(report)
        print("Compatible tool checkouts found. This check does not establish extraction or equivalence.")
        return

    # Use a fresh directory per attempt so stale generated files cannot pass.
    import tempfile
    work = Path(tempfile.mkdtemp(prefix="extraction-", dir=ROOT / "build"))
    llbc = work / "ark_eth_bridge.llbc"
    report["work_directory"] = str(work.relative_to(ROOT))
    report["rust_sources_sha256"] = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [ROOT / "rust/Cargo.toml", ROOT / "rust/Cargo.lock", ROOT / "rust/src/lib.rs"]
    }
    try:
        # The CLI runner is excluded: only the library's encode_g1 call graph is translated.
        # Keep dependency bodies visible. Do not make ark_ff or ark_ec opaque.
        run([charon, "cargo", "--preset=aeneas", "--error-on-warnings", "--start-from", "crate::encode_g1",
             "--include", "ark_bls12_381", "--include", "ark_ec", "--include", "ark_ff",
             "--include", "ark_serialize", "--dest-file", llbc,
             "--", "--lib", "--locked"], ROOT / "rust", report)
        if not llbc.is_file():
            raise RuntimeError("Charon did not produce the requested LLBC file")
        run([aeneas, "-backend", "lean", llbc, "-dest", work, "-subdir", "Generated",
             "-namespace", "ArkEthRust"], ROOT / "rust", report)
        files = list((work / "Generated").rglob("*.lean"))
        if not files:
            raise RuntimeError("No Lean output in Generated/; inspect translator output layout")
        unresolved = [str(p.relative_to(work)) for p in files
                      if "External" in p.name or "Template" in p.name
                      or re.search(r"\b(sorry|admit)\b|^\s*axiom\s", p.read_text(), re.MULTILINE)]
        if unresolved:
            report["unresolved_models"] = unresolved
            raise RuntimeError("Generated output needs external models or contains proof holes; "
                               "no assumptions were inserted. Inspect work_directory.")

        # Build the generated model and the real EthLib specification under the
        # Aeneas backend's Lean version, in the same Lake package graph.
        (work / "lean-toolchain").write_text(report["lean_toolchain"] + "\n")
        imports = "import ArkEth\n" + "".join(
            f"import {'.'.join(p.relative_to(work).with_suffix('').parts)}\n"
            for p in sorted(files))
        (work / "Extracted.lean").write_text(imports)
        backend = json.dumps(str(aeneas_dir / "backends/lean"))
        spec = json.dumps(str(ROOT / "lean"))
        (work / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage arkEthExtraction\n"
            f"require aeneas from {backend}\nrequire arkEth from {spec}\n"
            "lean_lib Generated where\n  globs := #[.submodules `Generated]\n"
            "@[default_target]\nlean_lib Extracted\n")
        run(["lake", "build"], work, report)
        report["status"] = "generated_model_and_spec_compile_equivalence_still_unproved"
        report["generated_sha256"] = {
            str(p.relative_to(work)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
        save_report(report)
        print("Extracted Rust model and EthLib compile together. The refinement theorem remains to be proved.")
    except (subprocess.CalledProcessError, RuntimeError) as error:
        report.update(status="failed", reason=str(error))
        save_report(report)
        sys.exit(str(error))


if __name__ == "__main__":
    main()
