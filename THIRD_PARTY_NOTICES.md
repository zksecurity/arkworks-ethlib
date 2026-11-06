# Third-party code

Parts of `curve/src/lib.rs`, `curve/src/field.rs`, `curve/src/montgomery.rs`,
`curve/src/pairing.rs`, `curve/src/field/inversion.rs` and `curve/src/decoder.rs` are adapted from arkworks 0.5.0 (`ark-ec`, `ark-ff`,
`ark-ff-macros` and `ark-bls12-381`).

Copyright 2022 arkworks contributors.

These adaptations use the Apache-2.0 option of upstream's MIT/Apache-2.0 dual
license. The source revisions and file hashes are recorded in
[the provenance manifest](provenance/arkworks-0.5.0.json). Changes include BLS12-381
specialization, fixed arrays, returned values in place of mutable borrowed
scalars, `Option` results in place of deserialization errors, and a total zero
result in place of an absent extension-field inverse. The remaining
implementation differences are listed in [the alignment ledger](docs/arkworks-alignment.md).

Vendored EthLib retains its [license](lean/vendor/ethlib/LICENSE) and
[provenance](lean/vendor/ethlib/provenance.json). Published test vectors retain
licenses in their respective `test-vectors/` directories.
