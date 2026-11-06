use curve_g1::{add, double, field::generator, mul_256, mul_u64, negate, Field};

fn main() {
    let g = generator();
    let two_g = double(g);
    let three_g = add(g, two_g);
    let minus_g = negate(g);
    let seventeen_g = mul_u64(g, 17);
    let large_multiple = mul_256(g, [17, 0, 0, 1]);
    assert!(add(g, minus_g).z.is_zero());
    for (name, p) in [
        ("2G", two_g),
        ("3G", three_g),
        ("17G", seventeen_g),
        ("(2^192 + 17)G", large_multiple),
    ] {
        println!("{name}: Jacobian coordinates, canonical little-endian u64 limbs");
        println!("  X = {:016x?}", p.x.to_limbs());
        println!("  Y = {:016x?}", p.y.to_limbs());
        println!("  Z = {:016x?}", p.z.to_limbs());
    }
}
