#!/usr/bin/env python3
"""Instrument pinned arkworks in an isolated copy and compare actual round states."""
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

from arkworks_sources import verify
from differential import ROOT

TRACE_OBSERVER = """
extern crate std;
pub mod migration_trace {
    pub struct Snapshot {
        pub limbs: std::vec::Vec<u64>,
        pub factor: u64,
        pub product_carry: u64,
        pub reduction_carry: u64,
    }
    pub struct InverseSnapshot {
        pub words: std::vec::Vec<u64>,
        pub phase: u64,
    }
    std::thread_local! {
        static INVERSE_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
        static INVERSE_ROUNDS: std::cell::RefCell<std::vec::Vec<InverseSnapshot>> =
            std::cell::RefCell::new(std::vec::Vec::new());
        static ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
        static ROUNDS: std::cell::RefCell<std::vec::Vec<Snapshot>> =
            std::cell::RefCell::new(std::vec::Vec::new());
    }
    pub fn record(limbs: &[u64], factor: u64, product_carry: u64, reduction_carry: u64) {
        if !ENABLED.with(|enabled| enabled.get()) { return; }
        ROUNDS.with(|r| r.borrow_mut().push(Snapshot {
            limbs: limbs.to_vec(), factor, product_carry, reduction_carry
        }));
    }
    pub fn record_inverse(u: &[u64], v: &[u64], b: &[u64], c: &[u64], phase: u64) {
        if !INVERSE_ENABLED.with(|enabled| enabled.get()) { return; }
        let words = [u,v,b,c].concat();
        INVERSE_ROUNDS.with(|r| r.borrow_mut().push(InverseSnapshot { words, phase }));
    }
    pub fn start_inverse() {
        INVERSE_ROUNDS.with(|r| r.borrow_mut().clear());
        INVERSE_ENABLED.with(|enabled| enabled.set(true));
    }
    pub fn take_inverse() -> std::vec::Vec<InverseSnapshot> {
        INVERSE_ENABLED.with(|enabled| enabled.set(false));
        INVERSE_ROUNDS.with(|r| std::mem::take(&mut *r.borrow_mut()))
    }
    pub fn without_recording<T>(f: impl FnOnce() -> T) -> T {
        let previous = ENABLED.with(|enabled| enabled.replace(false));
        let result = f();
        ENABLED.with(|enabled| enabled.set(previous));
        result
    }
    pub fn take() -> std::vec::Vec<Snapshot> {
        ROUNDS.with(|r| std::mem::take(&mut *r.borrow_mut()))
    }
}
"""


def function_body(source, name, public=True):
    """Find the reviewed function body in the fixed minimal Rust source."""
    prefix = "pub " if public else ""
    start = source.index("{", source.index(f"{prefix}fn {name}("))
    depth = 1
    end = start + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return start, end - 1


def instrument_minimal(work):
    library = work / "curve/src/lib.rs"
    library_original = library.read_text()
    library_changed = library_original + TRACE_OBSERVER
    library.write_text(library_changed)
    source = work / "curve/src/montgomery.rs"
    original = source.read_text()
    changed = original
    hooks = [
        ("conversion_round", "ConversionRound", "&out.limbs, out.factor, 0, out.carry"),
        ("round", "Round", "&out.limbs, out.factor, out.product_carry, out.reduction_carry"),
        ("accumulate_product", "ProductAccumulation", "&out.limbs, 0, out.carry_a, out.carry_b"),
        ("sum_product_round", "SumProductRound", "&out.limbs, out.factor, out.second.carry_a, out.reduction_carry"),
        ("square_diagonal", "SquareDiagonal", "&out.limbs, 0, 0, out.carry"),
        ("square_reduction_round", "SquareReductionRound", "&out.limbs, out.factor, out.mac_carry, out.carry"),
    ]
    for name, result_type, arguments in hooks:
        start, end = function_body(changed, name)
        body = changed[start+1:end]
        marker = f"\n    {result_type} {{"
        if body.count(marker) != 1:
            raise RuntimeError(f"Minimal {name} return no longer matches the reviewed observer site")
        body = body.replace(marker, f"\n    let out = {result_type} {{", 1)
        body = body.rstrip() + f";\n    crate::migration_trace::record({arguments});\n    out\n"
        changed = changed[:start+1] + body + changed[end:]
    for name in ("square_cross", "square_double"):
        start, end = function_body(changed, name)
        body = changed[start+1:end]
        if not body.endswith("\n    r\n"):
            raise RuntimeError(f"Minimal {name} return no longer matches the reviewed observer site")
        body = body[:-len("\n    r\n")] + "\n    crate::migration_trace::record(&r, 0, 0, 0);\n    r\n"
        changed = changed[:start+1] + body + changed[end:]
    source.write_text(changed)
    patch = "".join(difflib.unified_diff(
        library_original.splitlines(keepends=True), library_changed.splitlines(keepends=True),
        fromfile="minimal/lib.rs", tofile="instrumented-minimal/lib.rs"))
    patch += "".join(difflib.unified_diff(
        original.splitlines(keepends=True), changed.splitlines(keepends=True),
        fromfile="minimal/montgomery.rs", tofile="instrumented-minimal/montgomery.rs"))
    inverse = work / "curve/src/field/inversion.rs"
    original = inverse.read_text()
    changed = original
    native_state = "crate::migration_trace::record_inverse(&u, &v, &b.limbs, &c.limbs, {phase});"
    hooks = [
        ("    while !is_one(u) && !is_one(v) {", "    " + native_state.format(phase=0) + "\n    while !is_one(u) && !is_one(v) {"),
        ("            b = half_coefficient(b);", "            b = half_coefficient(b);\n            " + native_state.format(phase=1)),
        ("            c = half_coefficient(c);", "            c = half_coefficient(c);\n            " + native_state.format(phase=2)),
        ("            c = c.minus(b);\n        }\n    }", "            c = c.minus(b);\n        }\n        " + native_state.format(phase=3) + "\n    }"),
        ("    if is_one(u) {", "    " + native_state.format(phase=4) + "\n    if is_one(u) {"),
    ]
    for before, after in hooks:
        if changed.count(before) != 1:
            raise RuntimeError("Minimal binary inverse no longer matches a reviewed observer site")
        changed = changed.replace(before, after)
    inverse.write_text(changed)
    patch += "".join(difflib.unified_diff(
        original.splitlines(keepends=True), changed.splitlines(keepends=True),
        fromfile="minimal/inversion.rs", tofile="instrumented-minimal/inversion.rs"))
    return patch


def archive(name):
    homes = (ROOT / ".cache/cargo", Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")))
    for home in homes:
        found = list((home / "registry/cache").glob(f"*/{name}-0.5.0.crate"))
        if found:
            return found[0]
    raise RuntimeError(f"Missing published crate archive: {name}")


def main():
    # Validates the archive Cargo checksums, upstream revisions and mapped source hashes.
    verify()
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="arkworks-trace-", dir=build))
    report_path = build / "arkworks-intermediates.json"
    log_path = build / "arkworks-intermediates.log"
    report = {
        "status": "running",
        "work_directory": str(work.relative_to(ROOT)),
        "scope": "source G1 scalar APIs, fast subgroup checks, field powers/square roots, compressed serialization and point recovery; portable Montgomery multiplication, squaring, fused products and conversion; actual upstream loops and derive-macro-generated path; Fp2/Fp6/Fp12 dense and sparse arithmetic schedules; live binary-inverse state traces including tower inversions; Fp2/Fp6/Fp12 Frobenius coefficient multiplication; Granger-Scott cyclotomic square, signed-NAF parameter exponent and live optimized final exponentiation; homogeneous G2 double/add, M-twist line evaluation and full affine/projective G2 and G1 preparation; complete four-pair prepared Miller schedule",
        "inverse_source_sha256": hashlib.sha256((ROOT / "curve/src/field/inversion.rs").read_bytes()).hexdigest(),
        "affine_scalar_source_sha256": hashlib.sha256((ROOT / "curve/src/scalar.rs").read_bytes()).hexdigest(),
        "g1_source_sha256": hashlib.sha256((ROOT / "curve/src/lib.rs").read_bytes()).hexdigest(),
        "glv_arithmetic_source_sha256": hashlib.sha256((ROOT / "curve/src/glv/arithmetic.rs").read_bytes()).hexdigest(),
        "endomorphism_source_sha256": hashlib.sha256((ROOT / "curve/src/glv.rs").read_bytes()).hexdigest(),
        "alternative_power_source_sha256": hashlib.sha256((ROOT / "curve/src/alternative/field_power.rs").read_bytes()).hexdigest(),
        "optimized_power_source_sha256": hashlib.sha256((ROOT / "curve/src/optimized/field_power.rs").read_bytes()).hexdigest(),
        "decoder_source_sha256": hashlib.sha256((ROOT / "curve/src/decoder.rs").read_bytes()).hexdigest(),
        "formatter_source_sha256": hashlib.sha256((ROOT / "minimal/src/lib.rs").read_bytes()).hexdigest(),
        "field_source_sha256": hashlib.sha256((ROOT / "curve/src/field.rs").read_bytes()).hexdigest(),
        "prepared_miller_source_sha256": hashlib.sha256((ROOT / "curve/src/pairing/prepared_miller.rs").read_bytes()).hexdigest(),
        "prepared_source_sha256": hashlib.sha256((ROOT / "curve/src/pairing/prepared.rs").read_bytes()).hexdigest(),
        "extension_source_sha256": hashlib.sha256((ROOT / "curve/src/pairing.rs").read_bytes()).hexdigest(),
        "minimal_source_sha256": hashlib.sha256((ROOT / "curve/src/montgomery.rs").read_bytes()).hexdigest(),
        "test_source_sha256": hashlib.sha256((ROOT / "migration-tests/montgomery_trace.rs").read_bytes()).hexdigest(),
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        for name in ("ark-ff", "ark-ff-macros", "ark-ec"):
            with tarfile.open(archive(name)) as package:
                package.extractall(work, filter="data")
        ff = work / "ark-ff-0.5.0"
        macros = work / "ark-ff-macros-0.5.0"
        ec = work / "ark-ec-0.5.0"
        lib = ff / "src/lib.rs"
        lib.write_text(lib.read_text() + TRACE_OBSERVER)
        source = macros / "src/montgomery/mul.rs"
        original = source.read_text()
        needle = "default.extend(quote!(r[#num_limbs - 1] = carry1 + carry2;));"
        if original.count(needle) != 1:
            raise RuntimeError("Upstream multiplication no longer matches the reviewed instrumentation site")
        # Keep every upstream arithmetic statement; append only an observer after each round.
        changed = original.replace(needle, """default.extend(quote! {
            r[#num_limbs - 1] = carry1 + carry2;
            ark_ff::migration_trace::record(&r, k, carry1, carry2);
        });""")
        source.write_text(changed)
        patch = "".join(difflib.unified_diff(
            original.splitlines(keepends=True), changed.splitlines(keepends=True),
            fromfile="upstream/mul.rs", tofile="instrumented/mul.rs"))
        backend = ff / "src/fields/models/fp/montgomery_backend.rs"
        backend_original = backend.read_text()
        conversion_site = "r[i % N] = carry;"
        if backend_original.count(conversion_site) != 1:
            raise RuntimeError("Upstream conversion no longer matches the reviewed instrumentation site")
        backend_changed = backend_original.replace(conversion_site, conversion_site +
            "\n            crate::migration_trace::record(&r, k, 0, carry);")
        start, end = function_body(backend_changed, "inverse", public=False)
        inverse_body = backend_changed[start+1:end]
        state = "crate::migration_trace::record_inverse(&u.0, &v.0, &(b.0).0, &(c.0).0, {phase});"
        inverse_hooks = [
            ("        let mut c = Fp::zero();", "        let mut c = Fp::zero();\n        " + state.format(phase=0)),
            ("                }\n            }\n\n            while v.is_even() {", "                }\n                " + state.format(phase=1) + "\n            }\n\n            while v.is_even() {"),
            ("                }\n            }\n\n            if v < u {", "                }\n                " + state.format(phase=2) + "\n            }\n\n            if v < u {"),
            ("                c -= &b;\n            }\n        }", "                c -= &b;\n            }\n            " + state.format(phase=3) + "\n        }"),
            ("        if u == one {", "        " + state.format(phase=4) + "\n        if u == one {"),
        ]
        for before, after in inverse_hooks:
            if inverse_body.count(before) != 1:
                raise RuntimeError("Upstream binary inverse no longer matches a reviewed observer site")
            inverse_body = inverse_body.replace(before, after)
        backend_changed = backend_changed[:start+1] + inverse_body + backend_changed[end:]
        backend.write_text(backend_changed)
        patch += "".join(difflib.unified_diff(
            backend_original.splitlines(keepends=True), backend_changed.splitlines(keepends=True),
            fromfile="upstream/montgomery_backend.rs", tofile="instrumented/montgomery_backend.rs"))
        square = macros / "src/montgomery/square.rs"
        square_original = square.read_text()
        square_changed = square_original
        hooks = [
            ("default.extend(quote! { r[#double_num_limbs - 1] = r[#double_num_limbs - 2] >> 63; });",
             "default.extend(quote! { ark_ff::migration_trace::record(&r, 0, 0, 0); r[#double_num_limbs - 1] = r[#double_num_limbs - 2] >> 63; });"),
            ("default.extend(quote! { r[1] <<= 1; });",
             "default.extend(quote! { r[1] <<= 1; ark_ff::migration_trace::record(&r, 0, 0, 0); });"),
            ("default.extend(quote! { let mut carry2 = 0; });",
             "default.extend(quote! { ark_ff::migration_trace::record(&r, 0, 0, carry); let mut carry2 = 0; });"),
            ("default.extend(quote! { carry2 = fa::adc(&mut r[#num_limbs + #i], carry, carry2); });",
             "default.extend(quote! { carry2 = fa::adc(&mut r[#num_limbs + #i], carry, carry2); ark_ff::migration_trace::record(&r, k, carry, carry2); });"),
        ]
        for before, after in hooks:
            if square_changed.count(before) != 1:
                raise RuntimeError("Upstream square no longer matches a reviewed instrumentation site")
            square_changed = square_changed.replace(before, after)
        square.write_text(square_changed)
        patch += "".join(difflib.unified_diff(
            square_original.splitlines(keepends=True), square_changed.splitlines(keepends=True),
            fromfile="upstream/square.rs", tofile="instrumented/square.rs"))
        fused = macros / "src/montgomery/sum_of_products.rs"
        fused_original = fused.read_text()
        fused_changed = fused_original
        fused_sites = [
            ("carry_b = fa::adc(&mut carry_a, carry_b, carry2);",
             "carry_b = fa::adc(&mut carry_a, carry_b, carry2);\n                        ark_ff::migration_trace::record(&result.0, 0, carry_a, carry_b);"),
            ("result.0[#num_limbs - 1] = fa::adc_no_carry(carry_a, carry_b, &mut carry2);",
             "result.0[#num_limbs - 1] = fa::adc_no_carry(carry_a, carry_b, &mut carry2);\n                    ark_ff::migration_trace::record(&result.0, k, carry_a, carry2);"),
        ]
        for before, after in fused_sites:
            if fused_changed.count(before) != 1:
                raise RuntimeError("Upstream fused product no longer matches a reviewed instrumentation site")
            fused_changed = fused_changed.replace(before, after)
        fused.write_text(fused_changed)
        patch += "".join(difflib.unified_diff(
            fused_original.splitlines(keepends=True), fused_changed.splitlines(keepends=True),
            fromfile="upstream/sum_of_products.rs", tofile="instrumented/sum_of_products.rs"))
        # Expose actual upstream homogeneous state/methods for direct comparison.
        # Only visibility changes; arithmetic statements remain untouched.
        g2 = ec / "src/models/bls12/g2.rs"
        original = g2.read_text()
        changed = original
        for field in ("x", "y", "z"):
            before = f"    {field}: Fp2<P::Fp2Config>,"
            if changed.count(before) != 1:
                raise RuntimeError("Upstream homogeneous field visibility site changed")
            changed = changed.replace(before, f"    pub {field}: Fp2<P::Fp2Config>,")
        for method in ("double_in_place", "add_in_place"):
            before = f"    fn {method}("
            if changed.count(before) != 1:
                raise RuntimeError("Upstream homogeneous method visibility site changed")
            changed = changed.replace(before, f"    pub fn {method}(")
        g2.write_text(changed)
        patch += "".join(difflib.unified_diff(
            original.splitlines(keepends=True), changed.splitlines(keepends=True),
            fromfile="upstream/g2.rs", tofile="exposed-upstream/g2.rs"))
        model = ec / "src/models/bls12/mod.rs"
        original = model.read_text()
        before = "    fn ell("
        if original.count(before) != 1:
            raise RuntimeError("Upstream line-evaluation visibility site changed")
        changed = original.replace(before, "    pub fn ell(")
        model.write_text(changed)
        patch += "".join(difflib.unified_diff(
            original.splitlines(keepends=True), changed.splitlines(keepends=True),
            fromfile="upstream/bls12.rs", tofile="exposed-upstream/bls12.rs"))
        for name in ("rust", "curve", "minimal"):
            shutil.copytree(ROOT / name, work / name, ignore=shutil.ignore_patterns(
                "target", "*.olean*", "*.ilean", "*.ir"))
        patch += instrument_minimal(work)
        (work / "instrumentation.patch").write_text(patch)
        shutil.copyfile(ROOT / "migration-tests/montgomery_trace.rs", work / "rust/tests/montgomery_trace.rs")
        command = [
            "cargo", "test", "--release", "--offline", "--test", "montgomery_trace",
            "--config", f"patch.crates-io.ark-ff.path={json.dumps(str(ff))}",
            "--config", f"patch.crates-io.ark-ec.path={json.dumps(str(ec))}",
            "--config", f"patch.crates-io.ark-ff-macros.path={json.dumps(str(macros))}",
            "--config", "profile.release.overflow-checks=true", "--", "--nocapture",
        ]
        env = dict(os.environ, CARGO_HOME=str(ROOT / ".cache/cargo"),
                   CARGO_TARGET_DIR=str(build / "arkworks-trace-target"),
                   POWER_TRACE_EXPORT=str(build / "power-trace-example.json"))
        with log_path.open("w") as log:
            subprocess.run(command, cwd=work / "rust", env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True, timeout=300)
        counts = re.search(r"Compared (\d+) products and (\d+) actual arkworks", log_path.read_text())
        if counts is None:
            raise RuntimeError("Missing intermediate comparison counts")
        conversions = re.search(r"Compared (\d+) conversion calls and (\d+) actual conversion round boundaries; (\d+) constructors and (\d+) constructor round boundaries", log_path.read_text())
        if conversions is None:
            raise RuntimeError("Missing conversion comparison counts")
        report.update(conversions=int(conversions[1]), conversion_rounds=int(conversions[2]),
                      constructors=int(conversions[3]), constructor_rounds=int(conversions[4]))
        squares = re.search(r"Compared (\d+) squares, (\d+) square phase boundaries and (\d+) square reduction rounds", log_path.read_text())
        if squares is None:
            raise RuntimeError("Missing square comparison counts")
        report.update(squares=int(squares[1]), square_phases=int(squares[2]), square_rounds=int(squares[3]))
        fused = re.search(r"Compared (\d+) fused products and (\d+) accumulation/reduction boundaries", log_path.read_text())
        if fused is None:
            raise RuntimeError("Missing fused-product comparison counts")
        report.update(fused_products=int(fused[1]), fused_boundaries=int(fused[2]))
        fp2 = re.search(r"Compared (\d+) Fp2 products/squares and (\d+) inverses at (\d+) base-field boundaries", log_path.read_text())
        if fp2 is None:
            raise RuntimeError("Missing Fp2 comparison counts")
        report.update(fp2_products=int(fp2[1]), fp2_squares=int(fp2[1]),
                      fp2_inverses=int(fp2[2]), fp2_boundaries=int(fp2[3]), fp2_mul_xi_calls=int(fp2[1]),
                      fp2_inverse_scope="norm squaring and final products; binary inverse state trace checked separately")
        frobenius = re.search(r"Compared (\d+) Fp2 Frobenius powers at (\d+) actual execution boundaries", log_path.read_text())
        if frobenius is None:
            raise RuntimeError("Missing Fp2 Frobenius state comparison counts")
        report.update(fp2_frobenius_cases=int(frobenius[1]), fp2_frobenius_boundaries=int(frobenius[2]))
        endomorphism = re.search(r"Compared (\d+) G1 endomorphisms at (\d+) actual execution boundaries", log_path.read_text())
        if endomorphism is None:
            raise RuntimeError("Missing G1 endomorphism execution comparison counts")
        report.update(g1_endomorphism_cases=int(endomorphism[1]),
                      g1_endomorphism_boundaries=int(endomorphism[2]))
        glv = re.search(r"Compared (\d+) GLV projective cases at (\d+) actual Fq execution boundaries; (\d+) Fr boundaries excluded", log_path.read_text())
        if glv is None:
            raise RuntimeError("Missing GLV point execution comparison counts")
        report.update(glv_projective_cases=int(glv[1]), glv_fq_boundaries=int(glv[2]),
                      glv_fr_boundaries_excluded=int(glv[3]),
                      glv_trace_scope="exact Fq multiplication/square/conversion execution states and raw output coordinates; Fr conversion/storage replaced by the proved integer backend and excluded from this trace")
        affine = re.search(r"Compared (\d+) affine integer cases at (\d+) actual Fq execution boundaries", log_path.read_text())
        if affine is None:
            raise RuntimeError("Missing affine integer execution comparison counts")
        report.update(affine_integer_cases=int(affine[1]), affine_integer_boundaries=int(affine[2]))
        cofactor = re.search(r"Compared (\d+) source cofactor cases at (\d+) actual Fq execution boundaries and (\d+) inverse states; (\d+) Fr boundaries excluded", log_path.read_text())
        if cofactor is None:
            raise RuntimeError("Missing source cofactor execution comparison counts")
        report.update(cofactor_cases=int(cofactor[1]), cofactor_fq_boundaries=int(cofactor[2]),
                      cofactor_inverse_states=int(cofactor[3]), cofactor_fr_boundaries_excluded=int(cofactor[4]),
                      cofactor_trace_scope="exact Fq operations and inverse states, including both source normalization conversions; source Fr effective-cofactor constant construction replaced by a fixed canonical integer and excluded")
        subgroup = re.search(r"Compared (\d+) source fast subgroup cases at (\d+) actual Fq execution boundaries and (\d+) inverse states; (\d+) Fr boundaries excluded", log_path.read_text())
        if subgroup is None:
            raise RuntimeError("Missing source fast subgroup execution comparison counts")
        report.update(fast_subgroup_cases=int(subgroup[1]), fast_subgroup_fq_boundaries=int(subgroup[2]),
                      fast_subgroup_inverse_states=int(subgroup[3]), fast_subgroup_fr_boundaries_excluded=int(subgroup[4]),
                      fast_subgroup_trace_scope="exact Fq operations and inverse states, including source normalization; Fr scalar reduction and GLV decomposition instructions excluded")

        power = re.search(r"Compared (\d+) source Fq powers at (\d+) actual execution boundaries and (\d+) square roots at (\d+) boundaries", log_path.read_text())
        if power is None:
            raise RuntimeError("Missing source Fq power/square-root execution counts")
        report.update(fq_power_cases=int(power[1]), fq_power_boundaries=int(power[2]),
                      fq_sqrt_cases=int(power[3]), fq_sqrt_boundaries=int(power[4]))
        integer_api = re.search(r"Compared (\d+) source integer API cases at (\d+) actual Fq execution boundaries and (\d+) inverse states", log_path.read_text())
        if integer_api is None:
            raise RuntimeError("Missing source integer API execution counts")
        report.update(integer_api_cases=int(integer_api[1]), integer_api_boundaries=int(integer_api[2]),
                      integer_api_inverse_states=int(integer_api[3]))
        encoding = re.search(r"Compared (\d+) source compressed encodings at (\d+) actual Fq execution boundaries and (\d+) inverse states", log_path.read_text())
        if encoding is None:
            raise RuntimeError("Missing source compressed encoding execution counts")
        report.update(compressed_encoding_cases=int(encoding[1]), compressed_encoding_boundaries=int(encoding[2]),
                      compressed_encoding_inverse_states=int(encoding[3]))
        recovery = re.search(r"Compared (\d+) source point recovery calls at (\d+) actual Fq execution boundaries", log_path.read_text())
        if recovery is None:
            raise RuntimeError("Missing source point recovery execution counts")
        report.update(point_recovery_calls=int(recovery[1]), point_recovery_boundaries=int(recovery[2]))
        optimized = re.search(r"Compared (\d+) optimized powers; (\d+) nonzero-exponent traces differ by 15 fewer boundaries, with identical raw outputs", log_path.read_text())
        if optimized is None:
            raise RuntimeError("Missing optimized power trace-divergence evidence")
        report.update(optimized_power_cases=int(optimized[1]), optimized_power_different_traces=int(optimized[2]),
                      optimized_power_saved_boundaries_per_nonzero_exponent=15,
                      optimized_power_example_original_boundaries=57, optimized_power_example_boundaries=42)
        alternative = re.search(r"Compared (\d+) LSB-first powers against original and actual arkworks, with 384 squares per call", log_path.read_text())
        if alternative is None:
            raise RuntimeError("Missing alternative power trace evidence")
        trace = json.loads((build / "power-trace-example.json").read_text())
        if trace["arkworks"] != trace["minimal"] or len(trace["arkworks"]) != 57 or len(trace["alternative"]) != 3468:
            raise RuntimeError("Invalid exported power trace comparison")
        report.update(alternative_power_cases=int(alternative[1]),
                      alternative_power_example_boundaries=3468,
                      power_trace_example="build/power-trace-example.json")
        fp6 = re.search(r"Compared (\d+) Fp6 products/squares/inverses at (\d+) actual execution boundaries", log_path.read_text())
        if fp6 is None:
            raise RuntimeError("Missing Fp6 actual execution comparison counts")
        report.update(fp6_products=int(fp6[1]), fp6_squares=int(fp6[1]), fp6_inverses=int(fp6[1]),
                      fp6_boundaries=int(fp6[2]), minimal_execution_instrumented=True, fp2_actual_execution_compared=True,
                      base_inverse_internal_trace_compared=True)
        frobenius6 = re.search(r"Compared (\d+) Fp6 Frobenius powers at (\d+) actual execution boundaries", log_path.read_text())
        if frobenius6 is None:
            raise RuntimeError("Missing Fp6 Frobenius state comparison counts")
        report.update(fp6_frobenius_cases=int(frobenius6[1]), fp6_frobenius_boundaries=int(frobenius6[2]))
        fp12 = re.search(r"Compared (\d+) Fp12 products/squares/inverses at (\d+) actual execution boundaries", log_path.read_text())
        if fp12 is None:
            raise RuntimeError("Missing Fp12 actual execution comparison counts")
        report.update(fp12_products=int(fp12[1]), fp12_squares=int(fp12[1]), fp12_inverses=int(fp12[1]),
                      fp12_boundaries=int(fp12[2]))
        frobenius12 = re.search(r"Compared (\d+) Fp12 Frobenius powers at (\d+) actual execution boundaries", log_path.read_text())
        if frobenius12 is None:
            raise RuntimeError("Missing Fp12 Frobenius state comparison counts")
        report.update(fp12_frobenius_cases=int(frobenius12[1]), fp12_frobenius_boundaries=int(frobenius12[2]))
        cyclotomic = re.search(r"Compared (\d+) cyclotomic squares at (\d+) actual execution boundaries", log_path.read_text())
        if cyclotomic is None:
            raise RuntimeError("Missing cyclotomic-square comparison counts")
        report.update(cyclotomic_squares=int(cyclotomic[1]), cyclotomic_square_boundaries=int(cyclotomic[2]))
        exponent = re.search(r"Compared (\d+) signed-NAF parameter exponents at (\d+) actual execution boundaries", log_path.read_text())
        if exponent is None:
            raise RuntimeError("Missing signed-NAF exponent comparison counts")
        report.update(cyclotomic_exponents=int(exponent[1]), cyclotomic_exponent_boundaries=int(exponent[2]))
        optimized = re.search(r"Compared (\d+) optimized final exponents at (\d+) actual execution boundaries", log_path.read_text())
        if optimized is None:
            raise RuntimeError("Missing optimized final-exponent comparison counts")
        report.update(optimized_final_exponents=int(optimized[1]), optimized_final_boundaries=int(optimized[2]))
        prepared = re.search(r"Compared (\d+) homogeneous doubles/adds/lines and scalar products at (\d+) actual execution boundaries", log_path.read_text())
        if prepared is None:
            raise RuntimeError("Missing prepared-line comparison counts")
        report.update(prepared_line_cases=int(prepared[1]), prepared_line_boundaries=int(prepared[2]))
        prepared_g2 = re.search(r"Compared (\d+) G2 preparations at (\d+) actual execution boundaries", log_path.read_text())
        if prepared_g2 is None:
            raise RuntimeError("Missing full G2 preparation comparison counts")
        report.update(prepared_g2_cases=int(prepared_g2[1]), prepared_g2_boundaries=int(prepared_g2[2]))
        projective = re.search(r"Compared (\d+) projective preparation cases at (\d+) actual execution boundaries", log_path.read_text())
        if projective is None:
            raise RuntimeError("Missing projective preparation comparison counts")
        report.update(projective_preparation_cases=int(projective[1]), projective_preparation_boundaries=int(projective[2]))
        miller = re.search(r"Compared (\d+) prepared multi-Miller loops at (\d+) actual execution boundaries", log_path.read_text())
        if miller is None:
            raise RuntimeError("Missing prepared multi-Miller comparison counts")
        report.update(prepared_miller_cases=int(miller[1]), prepared_miller_boundaries=int(miller[2]))
        sparse = re.search(r"Compared (\d+) cases for each sparse helper at (\d+) actual execution boundaries", log_path.read_text())
        if sparse is None:
            raise RuntimeError("Missing sparse-helper actual execution comparison counts")
        report.update(fp6_mul_by_1_cases=int(sparse[1]), fp6_mul_by_01_cases=int(sparse[1]),
                      fp12_mul_by_014_cases=int(sparse[1]), sparse_boundaries=int(sparse[2]))
        tower_inverse = re.search(r"Compared (\d+) binary inverse states inside Fp2/Fp6/Fp12 inversion", log_path.read_text())
        if tower_inverse is None:
            raise RuntimeError("Missing tower binary-inverse state comparison counts")
        report.update(tower_binary_inverse_state_boundaries=int(tower_inverse[1]))
        inverse = re.search(r"Compared (\d+) binary inverses and (\d+) actual u/v/b/c state boundaries", log_path.read_text())
        if inverse is None:
            raise RuntimeError("Missing binary-inverse state comparison counts")
        report.update(binary_inverse_cases=int(inverse[1]), binary_inverse_state_boundaries=int(inverse[2]), binary_inverse_state_trace_compared=True)
        report.update(status="passed", products=int(counts[1]), rounds=int(counts[2]),
                      instrumentation_sha256=hashlib.sha256(patch.encode()).hexdigest())
        print(log_path.read_text()[-2500:])
    except Exception as error:
        report.update(status="failed", reason=str(error))
        if log_path.exists():
            print(log_path.read_text()[-5000:], file=sys.stderr)
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
