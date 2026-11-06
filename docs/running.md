# Running the project

## Setup and verification

Requires Rust/Cargo through rustup, Lean **v4.35.0** through elan, Python
**3.11+**, **opam 2.x**, Git, and native build tools. On Ubuntu 24.04, install
`build-essential opam pkg-config libgmp-dev libffi-dev bubblewrap unzip zstd`.
On macOS, install Xcode command-line tools, opam, and GNU make (`brew install
opam make`). Install rustup and elan separately and ensure their binaries are
on `PATH`. The installer creates an isolated OCaml 5.3 switch and installs the
pinned Charon Rust toolchain; it does not install opam or elan.

```sh
cargo fetch --locked --manifest-path rust/Cargo.toml
make install-tools    # Install pinned Charon/Aeneas and their Lean backend
make curve            # Fresh extraction, proofs, vector checks, and comparisons
make compare-intermediates # Compare Montgomery round states with instrumented arkworks
make verify-vectors   # Only the 2,069 kernel-checked vector proofs (~3 minutes)
make test             # Codec comparisons and published-vector checks
```

Cargo uses the project-local offline cache; missing dependencies must first be
fetched with `cargo fetch --locked` in `rust/`. Reports, generated Lean proofs,
and axiom audits are written under `build/`.


## Pairing example

```sh
make pairing
rust/target/release/pairing_example --demo
lean/.lake/build/bin/pairing_example --demo
```

Both demos evaluate pairing products for cancellation, non-degeneracy,
`e(2P,3Q) · e(-6P,Q) = 1`, a wrong-scalar counterexample, and identity inputs.
Each printed Boolean asks whether the product is one; `false` is expected for
the single nonzero pair and the wrong-scalar case.

`make pairing` checks all **15 published EIP-2537 pairing vectors** against
minimal Rust, arkworks, and unchanged EthLib, plus **11 G1 multiplication vectors**.
The entire minimal pairing extracts through Aeneas.
[`ConcretePreparedMiller.default_pairing_check_ethlib_spec`](../curve/PreparedPairingEquivalence.lean) proves that
Rust's `pairing_check` terminates and returns exactly the Boolean from unchanged
EthLib `pairingCheck` for canonical coordinates whose finite G2 points normalize
to on-curve points killed by the subgroup order.
The field, curve, compression and subgroup proofs also target that same pinned EthLib.
See [the proof scope](pairing-proof.md).
The example uses a 64 MiB stack. Gas and full precompile error semantics are outside these checks.

