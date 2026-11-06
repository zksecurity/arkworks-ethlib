import Lake
open Lake DSL

package arkEth

@[default_target]
lean_lib ArkEth

@[default_target]
lean_exe ethlib_codec where
  root := `Main

lean_exe pairing_example where
  root := `PairingMain

-- Build every proof dependency on clean checkouts, including the pairing tower.
@[default_target]
lean_lib EthLib where
  srcDir := "vendor/ethlib"
  roots := #[`EthLib.Cryptography.Bls.Errors, `EthLib.Cryptography.Hash.Sha256,
    `EthLib.Cryptography.Bls.Fp, `EthLib.Cryptography.Bls.Fp2, `EthLib.Cryptography.Bls.Fr,
    `EthLib.Cryptography.Bls.G1, `EthLib.Cryptography.Bls.G2, `EthLib.Cryptography.Bls.Fp6,
    `EthLib.Cryptography.Bls.Fp12, `EthLib.Cryptography.Bls.Pairing, `EthLib.Cryptography.Bls.Compress]
