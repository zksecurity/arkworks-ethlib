#!/usr/bin/env bash
# Run in a terminal with network access. Uses the upstream source build targets.
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tool_dir="$project_dir/.tools"
aeneas_dir="$tool_dir/aeneas"
python_bin="${PYTHON:-python3.11}"

for program in git opam rustup cargo lake "$python_bin"; do
    command -v "$program" >/dev/null || { echo "Missing prerequisite: $program" >&2; exit 1; }
done

# Aeneas rejects Apple's make 3.81; recursive upstream builds invoke `make` too.
if [[ "$(uname -s)" == Darwin ]]; then
    if ! command -v gmake >/dev/null; then
        command -v brew >/dev/null || { echo "Install GNU make (gmake) first." >&2; exit 1; }
        brew install make
    fi
    mkdir -p "$tool_dir/bin"
    ln -sfn "$(command -v gmake)" "$tool_dir/bin/make"
    export PATH="$tool_dir/bin:$PATH"
fi

mkdir -p "$tool_dir"
aeneas_revision="$("$python_bin" -c 'import json,sys; print(json.load(open(sys.argv[1]))["aeneas_revision"])' "$project_dir/toolchain.json")"
if [[ ! -e "$aeneas_dir" ]]; then
    git clone https://github.com/AeneasVerif/aeneas.git "$aeneas_dir"
    git -C "$aeneas_dir" checkout --detach "$aeneas_revision"
fi
if [[ "$(git -C "$aeneas_dir" rev-parse HEAD)" != "$aeneas_revision" ]]; then
    echo "Existing Aeneas checkout does not match toolchain.json; refusing to change it." >&2
    exit 1
fi
# Existing checkouts are reused; no pull/reset or automatic Aeneas revision change.
charon_pin="$(awk '!/^#/ && NF {print $1; exit}' "$aeneas_dir/charon-pin")"
charon_dir="$aeneas_dir/charon"
if [[ ! -e "$charon_dir" ]]; then
    git clone https://github.com/AeneasVerif/charon.git "$charon_dir"
fi
if [[ "$(git -C "$charon_dir" rev-parse HEAD)" != "$charon_pin" ]]; then
    if [[ -n "$(git -C "$charon_dir" status --porcelain)" ]]; then
        echo "Charon has local changes and is not at Aeneas' pin; refusing to change it." >&2
        exit 1
    fi
    git -C "$charon_dir" fetch origin "$charon_pin"
    git -C "$charon_dir" checkout --detach "$charon_pin"
fi
git -C "$charon_dir" submodule update --init --recursive

# Keep OCaml packages and Cargo downloads inside this project. Rustup manages
# the compiler required by Charon in the user's existing Rustup home.
export OPAMROOT="$tool_dir/opam"
export CARGO_HOME="$project_dir/.cache/cargo"
if [[ ! -f "$OPAMROOT/config" ]]; then
    opam init --bare --no-setup --yes
fi
if ! opam switch list --short | grep -Fxq '5.3.0'; then
    opam switch create 5.3.0 ocaml-base-compiler.5.3.0 --yes
fi
eval "$(opam env --switch=5.3.0 --set-switch --shell=bash)"
opam install "$aeneas_dir/src" "$charon_dir" --deps-only --with-test --with-doc --yes
# Charon's build runs cargo fmt, but its toolchain file omits rustfmt.
rust_toolchain="$("$python_bin" -c 'import json,sys; print(json.load(open(sys.argv[1]))["rust_toolchain"])' "$project_dir/toolchain.json")"
rustup toolchain install "$rust_toolchain" --profile minimal \
    --component rustfmt,rustc-dev,llvm-tools,rust-src,miri
make -C "$charon_dir" build
make -C "$aeneas_dir" build

# Upstream make uses in-place cp. On macOS, overwriting a previously executed
# Mach-O can leave a stale code-signature cache (SIGKILL on the next launch).
# Replace the installed executable inodes atomically after building instead.
"$python_bin" - "$aeneas_dir" <<'PY'
from pathlib import Path
import shutil
import sys

root = Path(sys.argv[1])
for source, target in [
    (root / "charon/charon/target/release/charon", root / "charon/bin/charon"),
    (root / "charon/charon/target/release/charon-driver", root / "charon/bin/charon-driver"),
    (root / "src/_build/default/main.exe", root / "bin/aeneas"),
]:
    temporary = target.with_suffix(".new")
    shutil.copy2(source, temporary)
    temporary.replace(target)
PY

"$aeneas_dir/bin/aeneas" -version
"$charon_dir/bin/charon" version
(cd "$aeneas_dir/backends/lean" && lake exe cache get && lake build)
AENEAS_DIR="$aeneas_dir" "$python_bin" "$project_dir/scripts/extract.py" --check
AENEAS_DIR="$aeneas_dir" "$python_bin" "$project_dir/scripts/smoke_tools.py"
echo "Tools installed. Run make extract in $project_dir to attempt the arkworks extraction."
