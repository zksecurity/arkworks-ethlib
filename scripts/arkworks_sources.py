#!/usr/bin/env python3
"""Check source mappings against the checksum-pinned published arkworks crates."""
import hashlib
import json
import os
from pathlib import Path
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def verify():
    manifest = json.loads((ROOT / "provenance/arkworks-0.5.0.json").read_text())
    packages = tomllib.loads((ROOT / "rust/Cargo.lock").read_text())["package"]
    homes = [ROOT / ".cache/cargo", Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))]
    checked = 0
    for source in manifest["sources"]:
        name, version = source["crate"], source["version"]
        package = next(p for p in packages if p["name"] == name and p["version"] == version)
        archives = [p for home in homes for p in
                    (home / "registry/cache").glob(f"*/{name}-{version}.crate")]
        if not archives:
            raise RuntimeError(f"Missing {name}-{version}.crate; run cargo fetch --locked in rust/")
        archive = archives[0]
        if hashlib.sha256(archive.read_bytes()).hexdigest() != package["checksum"]:
            raise RuntimeError(f"Cargo checksum mismatch for {name}-{version}")
        with tarfile.open(archive) as crate:
            def read(path):
                member = crate.extractfile(f"{name}-{version}/{path}")
                if member is None:
                    raise RuntimeError(f"Missing source {name}/{path}")
                return member.read()

            vcs = json.loads(read(".cargo_vcs_info.json"))
            if vcs["git"]["sha1"] != source["revision"] or vcs["path_in_vcs"] != source["path_in_vcs"]:
                raise RuntimeError(f"Upstream revision mismatch for {name}")
            for path, expected in source["files"].items():
                if hashlib.sha256(read(path)).hexdigest() != expected:
                    raise RuntimeError(f"Source mapping hash mismatch: {name}/{path}")
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"PASS: {verify()} upstream source files match checksum-pinned arkworks 0.5.0 crates.")
