import PreparedG2Proof
import Fp2DomainProof

open EthLib.Cryptography.Bls
namespace PreparedGeometry

local instance : CommRing Fp := Fin.instCommRing Fp.modulus
noncomputable local instance : Field Fp2 := QuadraticDomain.fieldStructure
noncomputable local instance : Div Fp2 := ⟨fun a b => a*b⁻¹⟩

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl
private theorem source_sub (a b : Fp2) : Fp2.sub a b = a + -b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  apply ext2
  all_goals change _ - _ = _ + -_
  all_goals ring

theorem double_z (p : PreparedLine.Hom) (half : Fp) :
    (PreparedLine.double p half).1.z = (2 : Fp2)*p.y^3*p.z := by
  simp only [PreparedLine.double, HSub.hSub, Sub.sub, source_sub]
  ring

theorem add_z (p : PreparedLine.Hom) (qx qy : Fp2) :
    (PreparedLine.add p qx qy).1.z = p.z*(p.x + -(qx*p.z))^3 := by
  simp only [PreparedLine.add, HSub.hSub, Sub.sub, source_sub]
  ring

/-- Homogeneous equation for coordinates x/z and y/z on the BLS twist. -/
def OnCurve (p : PreparedLine.Hom) : Prop :=
  p.y^2*p.z = p.x^3 + PreparedLine.coeffB*p.z^3

theorem double_onCurve (p : PreparedLine.Hom) (half : Fp) (hp : OnCurve p)
    (hh : Fp2.ofFp half = (2 : Fp2)⁻¹) :
    OnCurve (PreparedLine.double p half).1 := by
  have htwo : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  unfold OnCurve at hp ⊢
  simp only [PreparedLine.double, HSub.hSub, Sub.sub, source_sub, hh]
  field_simp
  linear_combination (2*p.y^3*(p.y^2 + -(9*PreparedLine.coeffB*p.z^2))^3)*hp

theorem double_x_cross (p : PreparedLine.Hom) (half : Fp) (hp : OnCurve p)
    (hh : Fp2.ofFp half = (2 : Fp2)⁻¹) :
    (PreparedLine.double p half).1.x * (4*p.y^2*p.z^2) =
      (PreparedLine.double p half).1.z * (9*p.x^4 + -(8*p.x*p.y^2*p.z)) := by
  have htwo : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  unfold OnCurve at hp
  simp only [PreparedLine.double, HSub.hSub, Sub.sub, source_sub, hh]
  field_simp
  linear_combination (36*p.x*p.y^3*p.z)*hp

/-- The source preparation constant is exactly the quadratic field's half. -/
theorem source_half : Fp2.ofFp (Fp.inverse (Fp.ofNat 2)) = (2 : Fp2)⁻¹ := by
  have ht : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  have hi := BaseField.inverse_mul (Fp.ofNat 2) (by decide +kernel)
  have he := congrArg QuadraticField.ofFpHom hi
  rw [map_mul, map_one] at he
  have hc : QuadraticField.ofFpHom (Fp.ofNat 2) = (2 : Fp2) := by
    apply ext2 <;> decide +kernel
  rw [hc] at he
  exact mul_left_cancel₀ ht (he.trans (mul_inv_cancel₀ ht).symm)

private theorem ratio_eq (a b c d : Fp2) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a*d = b*c) : a*b⁻¹ = c*d⁻¹ := by
  field_simp
  exact h

private theorem affine_x_formula (x y z : Fp2) (hy : y ≠ 0) (hz : z ≠ 0)
    (ht : (2 : Fp2) ≠ 0) :
    (9*x^4 + -(8*x*y^2*z))*(4*y^2*z^2)⁻¹ =
      (3*(x*z⁻¹)^2*(2*(y*z⁻¹))⁻¹)^2 + -(2*(x*z⁻¹)) := by
  have hfour : (4 : Fp2) ≠ 0 := by
    have he : (4 : Fp2) = 2*2 := by ring
    rw [he]
    exact mul_ne_zero ht ht
  field_simp
  ring

private theorem two_nonzero : (2 : Fp2) ≠ 0 := by
  intro h
  have hc := congrArg Fp2.c0 h
  have hn : (2 : Fp) ≠ 0 := by decide +kernel
  exact hn hc

private theorem four_nonzero : (4 : Fp2) ≠ 0 := by
  have he : (4 : Fp2) = 2*2 := by ring
  rw [he]
  exact mul_ne_zero two_nonzero two_nonzero

/-- Doubling stays finite whenever the input is finite and has nonzero y. -/
theorem double_z_nonzero (p : PreparedLine.Hom) (half : Fp)
    (hy : p.y ≠ 0) (hz : p.z ≠ 0) : (PreparedLine.double p half).1.z ≠ 0 := by
  rw [double_z]
  exact mul_ne_zero (mul_ne_zero two_nonzero (pow_ne_zero _ hy)) hz

/-- Normalizing the source doubled x gives the ordinary affine tangent formula. -/
theorem double_affine_x (p : PreparedLine.Hom) (hp : OnCurve p)
    (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    let d := (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1
    d.x*d.z⁻¹ =
      (3*(p.x*p.z⁻¹)^2*(2*(p.y*p.z⁻¹))⁻¹)^2 + -(2*(p.x*p.z⁻¹)) := by
  dsimp only
  have hd : (4 : Fp2)*p.y^2*p.z^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero four_nonzero (pow_ne_zero _ hy)) (pow_ne_zero _ hz)
  exact (ratio_eq _ _ _ _ (double_z_nonzero p _ hy hz) hd
    (double_x_cross p _ hp source_half)).trans
      (affine_x_formula p.x p.y p.z hy hz two_nonzero)

/-- The source doubled y numerator agrees with the affine tangent formula. -/
theorem double_y_cross (p : PreparedLine.Hom) (half : Fp) (hp : OnCurve p)
    (hh : Fp2.ofFp half = (2 : Fp2)⁻¹) :
    (4*p.z^2)*(PreparedLine.double p half).1.y =
      36*p.x^3*p.y^2*p.z + -(27*p.x^6) + -(8*p.y^4*p.z^2) := by
  have htwo := two_nonzero
  unfold OnCurve at hp
  simp only [PreparedLine.double, HSub.hSub, Sub.sub, source_sub, hh]
  field_simp
  linear_combination (36*(p.y^2*p.z + -(3*p.x^3) + 3*PreparedLine.coeffB*p.z^3))*hp

private theorem eight_nonzero : (8 : Fp2) ≠ 0 := by
  intro h
  have hc := congrArg Fp2.c0 h
  have hn : (8 : Fp) ≠ 0 := by decide +kernel
  exact hn hc

private theorem affine_y_formula (x y z : Fp2) (hy : y ≠ 0) (hz : z ≠ 0) :
    (36*x^3*y^2*z + -(27*x^6) + -(8*y^4*z^2))*(8*y^3*z^3)⁻¹ =
      (3*(x*z⁻¹)^2*(2*(y*z⁻¹))⁻¹)*
        (x*z⁻¹ + -((3*(x*z⁻¹)^2*(2*(y*z⁻¹))⁻¹)^2 + -(2*(x*z⁻¹)))) + -(y*z⁻¹) := by
  have htwo := two_nonzero
  have hfour := four_nonzero
  have height := eight_nonzero
  field_simp
  ring

/-- Normalizing the source doubled y gives the ordinary affine tangent formula. -/
theorem double_affine_y (p : PreparedLine.Hom) (hp : OnCurve p)
    (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    let d := (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1
    d.y*d.z⁻¹ = (3*(p.x*p.z⁻¹)^2*(2*(p.y*p.z⁻¹))⁻¹)*
      (p.x*p.z⁻¹ + -(d.x*d.z⁻¹)) + -(p.y*p.z⁻¹) := by
  dsimp only
  let n := 36*p.x^3*p.y^2*p.z + -(27*p.x^6) + -(8*p.y^4*p.z^2)
  have hc : (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1.y*(8*p.y^3*p.z^3) =
      (PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1.z*n := by
    rw [double_z]
    calc
      _ = ((4*p.z^2)*(PreparedLine.double p (Fp.inverse (Fp.ofNat 2))).1.y)*
          (2*p.y^3*p.z) := by ring
      _ = n*(2*p.y^3*p.z) := by rw [double_y_cross p _ hp source_half]
      _ = _ := by ring
  have hd : (8 : Fp2)*p.y^3*p.z^3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero eight_nonzero (pow_ne_zero _ hy)) (pow_ne_zero _ hz)
  rw [double_affine_x p hp hy hz]
  exact (ratio_eq _ _ _ _ (double_z_nonzero p _ hy hz) hd hc).trans
    (affine_y_formula p.x p.y p.z hy hz)

/-- A source mixed addition stays finite when its affine x coordinates differ. -/
theorem add_z_nonzero (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    (PreparedLine.add p qx qy).1.z ≠ 0 := by
  rw [add_z]
  exact mul_ne_zero hz (pow_ne_zero _ hx)

private theorem add_x_cross (p : PreparedLine.Hom) (qx qy : Fp2) :
    let t := p.y + -(qy*p.z)
    let l := p.x + -(qx*p.z)
    (PreparedLine.add p qx qy).1.x*(p.z*l^2) =
      (PreparedLine.add p qx qy).1.z*(p.z*t^2 + -((p.x+qx*p.z)*l^2)) := by
  simp only [PreparedLine.add, HSub.hSub, Sub.sub, source_sub]
  ring

private theorem add_x_formula (x z qx t l : Fp2) (hz : z ≠ 0) (hl : l ≠ 0) :
    (z*t^2 + -((x+qx*z)*l^2))*(z*l^2)⁻¹ =
      (t*l⁻¹)^2 + -(x*z⁻¹) + -qx := by
  field_simp
  ring

/-- Normalizing the source mixed-add x gives the usual affine chord formula. -/
theorem add_affine_x (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    let a := (PreparedLine.add p qx qy).1
    a.x*a.z⁻¹ = ((p.y + -(qy*p.z))*(p.x + -(qx*p.z))⁻¹)^2 + -(p.x*p.z⁻¹) + -qx := by
  dsimp only
  have hd : p.z*(p.x + -(qx*p.z))^2 ≠ 0 := mul_ne_zero hz (pow_ne_zero _ hx)
  exact (ratio_eq _ _ _ _ (add_z_nonzero p qx qy hz hx) hd (add_x_cross p qx qy)).trans
    (add_x_formula p.x p.z qx (p.y + -(qy*p.z)) (p.x + -(qx*p.z)) hz hx)

private theorem add_y_cross (p : PreparedLine.Hom) (qx qy : Fp2) :
    let a := (PreparedLine.add p qx qy).1
    let t := p.y + -(qy*p.z)
    let l := p.x + -(qx*p.z)
    a.y*(p.z*l) = t*(p.x*a.z + -(a.x*p.z)) + -(p.y*a.z*l) := by
  simp only [PreparedLine.add, HSub.hSub, Sub.sub, source_sub]
  ring

private theorem normalize_y (y' x' z' x y z t l : Fp2)
    (hz' : z' ≠ 0) (hz : z ≠ 0) (hl : l ≠ 0)
    (h : y'*(z*l) = t*(x*z' + -(x'*z)) + -(y*z'*l)) :
    y'*z'⁻¹ = t*l⁻¹*(x*z⁻¹ + -(x'*z'⁻¹)) + -(y*z⁻¹) := by
  field_simp
  linear_combination h

/-- Normalizing the source mixed-add y gives the usual affine chord formula. -/
theorem add_affine_y (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    let a := (PreparedLine.add p qx qy).1
    a.y*a.z⁻¹ = ((p.y + -(qy*p.z))*(p.x + -(qx*p.z))⁻¹)*
      (p.x*p.z⁻¹ + -(a.x*a.z⁻¹)) + -(p.y*p.z⁻¹) := by
  dsimp only
  exact normalize_y _ _ _ _ _ _ _ _ (add_z_nonzero p qx qy hz hx) hz hx
    (add_y_cross p qx qy)

/-- The homogeneous x-separation is exactly affine x-separation on finite inputs. -/
theorem affine_x_ne (p : PreparedLine.Hom) (qx : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) : p.x*p.z⁻¹ ≠ qx := by
  intro h
  have he : p.x = qx*p.z := by
    calc
      p.x = (p.x*p.z⁻¹)*p.z := by rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
      _ = qx*p.z := by rw [h]
  apply hx
  rw [he, add_neg_cancel]

/-- The source homogeneous slope equals the ordinary affine chord slope. -/
theorem add_slope (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    (p.y + -(qy*p.z))*(p.x + -(qx*p.z))⁻¹ =
      (qy + -(p.y*p.z⁻¹))*(qx + -(p.x*p.z⁻¹))⁻¹ := by
  have hd : qx + -(p.x*p.z⁻¹) ≠ 0 := by
    intro h
    have he : qx = p.x*p.z⁻¹ := by linear_combination h
    exact affine_x_ne p qx hz hx he.symm
  apply ratio_eq _ _ _ _ hx hd
  field_simp
  ring

#print axioms affine_x_ne
#print axioms add_slope
#print axioms add_affine_y
#print axioms add_z_nonzero
#print axioms add_affine_x
#print axioms double_affine_y
#print axioms double_z_nonzero
#print axioms double_affine_x
#print axioms double_y_cross
#print axioms double_z
#print axioms add_z
#print axioms double_onCurve
#print axioms double_x_cross
#print axioms source_half
end PreparedGeometry
