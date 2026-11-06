import FinalScalingProof
import PreparedGeometryProof
import PreparedMillerProof

open EthLib.Cryptography.Bls

namespace PreparedLineGeometry

private theorem line_identity {K : Type*} [Field K] (j t l x y z px py w : K)
    (hl : l ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hj : j*z = t*x + -(l*y)) :
    j + -(t*px*w^2) + l*py*w^3 =
      (l*w^3)*(py + -(y*z⁻¹*(w^3)⁻¹) +
        -(t*l⁻¹*w⁻¹*(px + -(x*z⁻¹*(w^2)⁻¹)))) := by
  field_simp
  linear_combination hj

noncomputable section
local instance : Field Fp2 := QuadraticDomain.fieldStructure
local instance : Field Fp6 := CubicDomain.fieldStructure
local instance : Field Fp12 := DodecicDomain.fieldStructure

/-- The unchanged tower embedding of a quadratic coefficient. -/
def embed : Fp2 →+* Fp12 := DodecicField.ofFp6Hom.comp CubicField.ofFp2Hom

private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl
private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

theorem sparse_eq (a b c : Fp2) : ExtensionAlignment.sparseElement014 a b c =
    embed a + embed b*DodecicField.w^2 + embed c*DodecicField.w^3 := by
  apply ext12
  all_goals apply ext6
  all_goals simp [ExtensionAlignment.sparseElement014, embed, DodecicField.w, Fp6.v, pow_succ]

theorem factor_eq (a : Fp2) : FinalScaling.lineFactor a = embed a*DodecicField.w^3 := by
  apply ext12
  all_goals apply ext6
  all_goals simp [FinalScaling.lineFactor, embed, DodecicField.w, Fp6.v, pow_succ]

private theorem w_nonzero : DodecicField.w ≠ (0 : Fp12) := by
  intro h
  have hc := congrArg (fun a : Fp12 => a.c1.c0.c0) h
  have hn : Fp.one ≠ Fp.zero := by decide +kernel
  exact hn hc

private theorem embed_nonzero (a : Fp2) (ha : a ≠ 0) : embed a ≠ 0 := by
  intro h
  exact ha (embed.injective (h.trans (map_zero embed).symm))

/-- Affine line evaluation after the twist map, with homogeneous slope numerator and denominator. -/
def eval (x y z t l : Fp2) (px py : Fp) : Fp12 :=
  let w := DodecicField.w
  embed (Fp2.ofFp py) + -(embed (y*z⁻¹)*(w^3)⁻¹) +
    -(embed (t*l⁻¹)*w⁻¹*(embed (Fp2.ofFp px) + -(embed (x*z⁻¹)*(w^2)⁻¹)))

theorem sparse_line (j t l x y z : Fp2) (px py : Fp)
    (hl : l ≠ 0) (hz : z ≠ 0) (hj : j*z = t*x + -(l*y)) :
    ExtensionAlignment.sparseElement014 j ((-t)*Fp2.ofFp px) (l*Fp2.ofFp py) =
      FinalScaling.lineFactor l * eval x y z t l px py := by
  have he := congrArg embed hj
  simp only [map_mul, map_add, map_neg] at he
  have h := line_identity (embed j) (embed t) (embed l) (embed x) (embed y) (embed z)
    (embed (Fp2.ofFp px)) (embed (Fp2.ofFp py)) DodecicField.w
    (embed_nonzero l hl) (embed_nonzero z hz) w_nonzero he
  simpa only [sparse_eq, factor_eq, eval, map_mul, map_neg, map_inv₀, neg_mul] using h

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl
private theorem source_sub (a b : Fp2) : Fp2.sub a b = a + -b := by
  let _ : CommRing Fp := Fin.instCommRing Fp.modulus
  apply ext2
  all_goals change _ - _ = _ + -_
  all_goals ring

theorem add_line (p : PreparedLine.Hom) (qx qy : Fp2) (px py : Fp)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    PreparedMiller.lineValue (PreparedLine.add p qx qy).2 px py =
      FinalScaling.lineFactor (p.x + -(qx*p.z))*
        eval p.x p.y p.z (p.y + -(qy*p.z)) (p.x + -(qx*p.z)) px py := by
  let t := p.y + -(qy*p.z)
  let l := p.x + -(qx*p.z)
  have hj : (t*qx + -(l*qy))*p.z = t*p.x + -(l*p.y) := by
    dsimp only [t, l]
    ring
  have h := sparse_line (t*qx + -(l*qy)) t l p.x p.y p.z px py hx hz hj
  simpa only [PreparedMiller.lineValue, PreparedLine.add, HSub.hSub, Sub.sub,
    source_sub, t, l] using h

private theorem extCoeff (a b : PreparedLine.Coeff) (h0 : a.c0 = b.c0)
    (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl

theorem double_line (p : PreparedLine.Hom) (half : Fp) (px py : Fp)
    (hp : PreparedGeometry.OnCurve p) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    PreparedMiller.lineValue (PreparedLine.double p half).2 px py =
      FinalScaling.lineFactor (-(2*p.y*p.z))*
        eval p.x p.y p.z (-(3*p.x^2)) (-(2*p.y*p.z)) px py := by
  let t := -(3*p.x^2)
  let l := -(2*p.y*p.z)
  let j := 3*PreparedLine.coeffB*p.z^2 + -(p.y^2)
  have htwo : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  have hl : l ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero htwo hy) hz)
  have hj : j*p.z = t*p.x + -(l*p.y) := by
    unfold PreparedGeometry.OnCurve at hp
    dsimp only [j, t, l]
    linear_combination (-3)*hp
  have hc : (PreparedLine.double p half).2 = ⟨j, -t, l⟩ := by
    apply extCoeff
    all_goals simp only [PreparedLine.double, HSub.hSub, Sub.sub, source_sub, j, t, l]
    all_goals ring
  rw [hc]
  exact sparse_line j t l p.x p.y p.z px py hl hz hj

theorem w_square : DodecicField.w^2 = DodecicField.ofFp6Hom Fp6.v := by
  apply ext12
  all_goals apply ext6
  all_goals simp [DodecicField.w, Fp6.v, pow_succ]

theorem wInv2_eq : Embedded.wInv2 = (DodecicField.w^2)⁻¹ := by
  change DodecicField.ofFp6Hom (Fp6.inverse Fp6.v) = _
  rw [TowerFieldInverse.fp6_inverse_eq, w_square, map_inv₀]

private theorem inv_cube {K : Type*} [Field K] (w : K) (hw : w ≠ 0) :
    (w^2*w^2)⁻¹*w = (w^3)⁻¹ := by
  field_simp

theorem wInv3_eq : Embedded.wInv3 = (DodecicField.w^3)⁻¹ := by
  have he : Embedded.wInv3 =
      DodecicField.ofFp6Hom ((Fp6.v*Fp6.v).inverse)*DodecicField.w := by
    apply ext12
    all_goals simp [Embedded.wInv3, DodecicField.w, Fp6.v]
  rw [he, TowerFieldInverse.fp6_inverse_eq, map_inv₀, map_mul, ←w_square]
  exact inv_cube _ w_nonzero

theorem add_line_final (p : PreparedLine.Hom) (qx qy : Fp2) (px py : Fp)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    finalExponentiation (PreparedMiller.lineValue (PreparedLine.add p qx qy).2 px py) =
      finalExponentiation (eval p.x p.y p.z (p.y + -(qy*p.z)) (p.x + -(qx*p.z)) px py) := by
  rw [add_line p qx qy px py hz hx, mul_comm]
  exact FinalScaling.final_lineFactor _ _ hx

theorem double_line_final (p : PreparedLine.Hom) (half : Fp) (px py : Fp)
    (hp : PreparedGeometry.OnCurve p) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    finalExponentiation (PreparedMiller.lineValue (PreparedLine.double p half).2 px py) =
      finalExponentiation (eval p.x p.y p.z (-(3*p.x^2)) (-(2*p.y*p.z)) px py) := by
  rw [double_line p half px py hp hy hz, mul_comm]
  have htwo : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  exact FinalScaling.final_lineFactor _ _ (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero htwo hy) hz))

private theorem source_sub12 (a b : Fp12) : Fp12.sub a b = a + -b := by
  apply ext12
  · change Fp6.sub a.c0 b.c0 = a.c0 + -b.c0
    exact CubicField.sub_eq_add_neg _ _
  · change Fp6.sub a.c1 b.c1 = a.c1 + -b.c1
    exact CubicField.sub_eq_add_neg _ _

/-- A finite homogeneous twist point, embedded using EthLib's exact untwist constants. -/
def untwist (p : PreparedLine.Hom) : Embedded.Point :=
  { x := embed (p.x*p.z⁻¹)*Embedded.wInv2,
    y := embed (p.y*p.z⁻¹)*Embedded.wInv3 }

/-- The intermediate line model is the unchanged EthLib line-evaluation function. -/
theorem eval_eq_evalAt (p : PreparedLine.Hom) (t l : Fp2) (px py : Fp) :
    eval p.x p.y p.z t l px py =
      Line.evalAt (untwist p).x (untwist p).y (embed (t*l⁻¹)*DodecicField.w⁻¹)
        (embed (Fp2.ofFp px)) (embed (Fp2.ofFp py)) := by
  simp only [Line.evalAt, HSub.hSub, Sub.sub, source_sub12, untwist, wInv2_eq, wInv3_eq, eval]

private theorem scaled_slope {K : Type*} [Field K] (dx dy w : K) (hw : w ≠ 0) :
    (dy*(w^3)⁻¹)*(dx*(w^2)⁻¹)⁻¹ = dy*dx⁻¹*w⁻¹ := by
  by_cases hx : dx = 0
  · simp only [hx, zero_mul, inv_zero, mul_zero]
  · field_simp

private theorem sub_scaled (a b k : Fp12) : a*k + -(b*k) = (a + -b)*k := by ring

private theorem slope_untwist (rx ry qx qy : Fp2) :
    Line.addSlope (embed rx*Embedded.wInv2) (embed ry*Embedded.wInv3)
      (embed qx*Embedded.wInv2) (embed qy*Embedded.wInv3) =
        embed ((qy + -ry)*(qx + -rx)⁻¹)*DodecicField.w⁻¹ := by
  simp only [Line.addSlope, HSub.hSub, Sub.sub, source_sub12,
    TowerFieldInverse.fp12_inverse_eq, wInv2_eq, wInv3_eq]
  rw [sub_scaled, sub_scaled, scaled_slope _ _ _ w_nonzero]
  simp only [map_mul, map_add, map_neg, map_inv₀]

/-- EthLib's exact untwisted chord slope equals the source homogeneous slope. -/
theorem add_slope_eq (p : PreparedLine.Hom) (qx qy : Fp2)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    Line.addSlope (untwist p).x (untwist p).y
      (untwist ⟨qx,qy,1⟩).x (untwist ⟨qx,qy,1⟩).y =
        embed ((p.y + -(qy*p.z))*(p.x + -(qx*p.z))⁻¹)*DodecicField.w⁻¹ := by
  simp only [untwist, inv_one, mul_one]
  rw [slope_untwist, ←PreparedGeometry.add_slope p qx qy hz hx]

private theorem scaled_tangent {K : Type*} [Field K] (c x den w : K) (hw : w ≠ 0) :
    c*(x*(w^2)⁻¹)*(x*(w^2)⁻¹)*(den*(w^3)⁻¹)⁻¹ = c*x*x*den⁻¹*w⁻¹ := by
  by_cases hd : den = 0
  · simp only [hd, zero_mul, inv_zero, mul_zero]
  · field_simp

private theorem literal_two :
    (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩ : Fp12) = 2 := by
  apply ext12
  all_goals apply ext6
  all_goals apply ext2
  all_goals decide +kernel

private theorem literal_three :
    (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩ : Fp12) = 3 := by
  apply ext12
  all_goals apply ext6
  all_goals apply ext2
  all_goals decide +kernel

private theorem tangent_untwist (rx ry : Fp2) :
    Line.tangentSlope (embed rx*Embedded.wInv2) (embed ry*Embedded.wInv3) =
      embed (3*rx*rx*(2*ry)⁻¹)*DodecicField.w⁻¹ := by
  simp only [Line.tangentSlope, literal_two, literal_three,
    TowerFieldInverse.fp12_inverse_eq, wInv2_eq, wInv3_eq]
  rw [←mul_assoc (2 : Fp12), scaled_tangent _ _ _ _ w_nonzero]
  simp only [map_mul, map_inv₀, map_ofNat]

private theorem tangent_hom (x y z : Fp2) (hy : y ≠ 0) (hz : z ≠ 0) :
    3*(x*z⁻¹)*(x*z⁻¹)*(2*(y*z⁻¹))⁻¹ = (-(3*x^2))*(-(2*y*z))⁻¹ := by
  have ht : (2 : Fp2) ≠ 0 := by
    intro h
    have hc := congrArg Fp2.c0 h
    have hn : (2 : Fp) ≠ 0 := by decide +kernel
    exact hn hc
  field_simp

/-- The untwisted tangent slope is the normalized affine tangent slope divided by w. -/
theorem double_slope_affine (p : PreparedLine.Hom) :
    Line.tangentSlope (untwist p).x (untwist p).y =
      embed (3*(p.x*p.z⁻¹)^2*(2*(p.y*p.z⁻¹))⁻¹)*DodecicField.w⁻¹ := by
  simpa only [untwist, pow_two, mul_assoc] using
    tangent_untwist (p.x*p.z⁻¹) (p.y*p.z⁻¹)

/-- EthLib's exact untwisted tangent slope equals the source homogeneous slope. -/
theorem double_slope_eq (p : PreparedLine.Hom) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    Line.tangentSlope (untwist p).x (untwist p).y =
      embed ((-(3*p.x^2))*(-(2*p.y*p.z))⁻¹)*DodecicField.w⁻¹ := by
  simp only [untwist]
  rw [tangent_untwist, tangent_hom p.x p.y p.z hy hz]

/-- A prepared mixed-add line and the unchanged EthLib affine line have equal final values. -/
theorem add_line_ethlib (p : PreparedLine.Hom) (qx qy : Fp2) (px py : Fp)
    (hz : p.z ≠ 0) (hx : p.x + -(qx*p.z) ≠ 0) :
    finalExponentiation (PreparedMiller.lineValue (PreparedLine.add p qx qy).2 px py) =
      finalExponentiation (Line.evalAt (untwist p).x (untwist p).y
        (Line.addSlope (untwist p).x (untwist p).y
          (untwist ⟨qx,qy,1⟩).x (untwist ⟨qx,qy,1⟩).y)
        (embed (Fp2.ofFp px)) (embed (Fp2.ofFp py))) := by
  rw [add_line_final p qx qy px py hz hx, eval_eq_evalAt, add_slope_eq p qx qy hz hx]

/-- A prepared double line and the unchanged EthLib tangent line have equal final values. -/
theorem double_line_ethlib (p : PreparedLine.Hom) (half : Fp) (px py : Fp)
    (hp : PreparedGeometry.OnCurve p) (hy : p.y ≠ 0) (hz : p.z ≠ 0) :
    finalExponentiation (PreparedMiller.lineValue (PreparedLine.double p half).2 px py) =
      finalExponentiation (Line.evalAt (untwist p).x (untwist p).y
        (Line.tangentSlope (untwist p).x (untwist p).y)
        (embed (Fp2.ofFp px)) (embed (Fp2.ofFp py))) := by
  rw [double_line_final p half px py hp hy hz, eval_eq_evalAt, double_slope_eq p hy hz]

#print axioms sparse_eq
#print axioms factor_eq
#print axioms sparse_line
#print axioms add_line
#print axioms double_line
#print axioms w_square
#print axioms wInv2_eq
#print axioms wInv3_eq
#print axioms add_line_final
#print axioms double_line_final
#print axioms eval_eq_evalAt
#print axioms add_slope_eq
#print axioms double_slope_affine
#print axioms double_slope_eq
#print axioms add_line_ethlib
#print axioms double_line_ethlib
end
end PreparedLineGeometry
