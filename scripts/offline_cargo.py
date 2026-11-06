#!/usr/bin/env python3
"""Build using a project-local Cargo home, seeded from already cached dependencies."""
import os
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    source = Path(os.environ.get("UPSTREAM_CARGO_HOME", Path.home() / ".cargo"))
    local = ROOT / ".cache/cargo"
    packages = tomllib.loads((ROOT / "rust/Cargo.lock").read_text())["package"]
    indices = list((source / "registry/index").glob("index.crates.io-*"))
    if not indices:
        sys.exit("No cached crates.io index. Run cargo fetch --locked in rust/ with network access.")
    index = indices[0]
    for package in packages:
        if not package.get("source", "").startswith("registry+"):
            continue
        name, version = package["name"], package["version"]
        key = name.lower()
        prefix = (key[:2] + "/" + key[2:4]) if len(key) >= 4 else (
            "3/" + key[0] if len(key) == 3 else str(len(key)))
        relative = Path("registry/index") / index.name / ".cache" / prefix / key
        archive = Path("registry/cache") / index.name / f"{name}-{version}.crate"
        for rel in [relative, archive]:
            dst = local / rel
            if not dst.exists():
                if not (source / rel).exists():
                    sys.exit(f"Missing cached {rel}. Run cargo fetch --locked in rust/ with network access.")
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source / rel, dst)
    config = local / "registry/index" / index.name / "config.json"
    if not config.exists():
        shutil.copyfile(index / "config.json", config)
    env = dict(os.environ, CARGO_HOME=str(local))
    sys.exit(subprocess.call(["cargo", *sys.argv[1:], "--offline", "--locked"],
                            cwd=ROOT / "rust", env=env))


if __name__ == "__main__":
    main()
