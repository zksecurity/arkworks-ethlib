import ExtensionProof

open EthLib.Cryptography.Bls

namespace PreparedLine

/-- Homogeneous coordinates of the source preparation algorithm, not Jacobian G2. -/
structure Hom where
  x : Fp2
  y : Fp2
  z : Fp2

structure Coeff where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2

def coeffB : Fp2 := ⟨Fp.ofNat 4,Fp.ofNat 4⟩

/-- Source double-step polynomials over unchanged EthLib coefficient arithmetic. -/
def double (p : Hom) (half : Fp) : Hom × Coeff :=
  let a := (p.x*p.y)*Fp2.ofFp half
  let b := p.y*p.y
  let c := p.z*p.z
  let e := coeffB*(c+c+c)
  let f := e+e+e
  let g := (b+f)*Fp2.ofFp half
  let h := (p.y+p.z)*(p.y+p.z)-(b+c)
  let i := e-b
  let j := p.x*p.x
  let eSquare := e*e
  (⟨a*(b-f),g*g-(eSquare+eSquare+eSquare),b*h⟩,⟨i,j+j+j,-h⟩)

/-- Source mixed-add step polynomials, with an affine coordinate pair as addend. -/
def add (p : Hom) (qx qy : Fp2) : Hom × Coeff :=
  let theta := p.y-qy*p.z
  let lambda := p.x-qx*p.z
  let c := theta*theta
  let d := lambda*lambda
  let e := lambda*d
  let f := p.z*c
  let g := p.x*d
  let h := e+f-(g+g)
  let j := theta*qx-lambda*qy
  (⟨lambda*h,theta*(g-h)-e*p.y,p.z*e⟩,⟨j,-theta,lambda⟩)

end PreparedLine

open Aeneas Aeneas.Std Aeneas.Std.WP
open ConcreteExtension

namespace ConcretePreparedLine

abbrev RawHom := CurveG1.pairing.prepared.HomG2
abbrev RawCoeff := CurveG1.pairing.prepared.LineCoeff

def ValidHom (p : RawHom) : Prop := Valid2 p.x ∧ Valid2 p.y ∧ Valid2 p.z
def decodeHom (p : RawHom) : PreparedLine.Hom := ⟨decode2 p.x,decode2 p.y,decode2 p.z⟩
def ValidCoeff (c : RawCoeff) : Prop := Valid2 c.c0 ∧ Valid2 c.c1 ∧ Valid2 c.c2
def decodeCoeff (c : RawCoeff) : PreparedLine.Coeff := ⟨decode2 c.c0,decode2 c.c1,decode2 c.c2⟩

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

/-- The precomputed Montgomery constant is exactly the pinned curve's (4,4). -/
theorem coefficient_spec : Valid2 CurveG1.pairing.prepared.COEFF_B ∧
    decode2 CurveG1.pairing.prepared.COEFF_B = PreparedLine.coeffB := by
  constructor
  · unfold Valid2 FieldProof.Valid
    constructor <;> decide +kernel
  · apply ext2 <;> decide +kernel

/-- Extracted doubling terminates, preserves canonical coefficients, and computes the source polynomials. -/
@[step] theorem double_spec (p : RawHom) (half : ConcreteField.Raw)
    (hp : ValidHom p) (hh : FieldProof.Valid half) :
    CurveG1.pairing.prepared.HomG2.double p half ⦃ r =>
      ValidHom r.1 ∧ ValidCoeff r.2 ∧
      (decodeHom r.1,decodeCoeff r.2) = PreparedLine.double (decodeHom p) (ConcreteField.decode half) ⦄ := by
  rcases hp with ⟨hx,hy,hz⟩
  have ⟨hb,he⟩ := coefficient_spec
  unfold CurveG1.pairing.prepared.HomG2.double
  step*
  all_goals simp_all [ValidHom, ValidCoeff, decodeHom, decodeCoeff, PreparedLine.double]

/-- Extracted addition computes the source polynomials for every canonical coordinate input. -/
@[step] theorem add_spec (p : RawHom) (qx qy : Raw2)
    (hp : ValidHom p) (hx : Valid2 qx) (hy : Valid2 qy) :
    CurveG1.pairing.prepared.HomG2.add p qx qy ⦃ r =>
      ValidHom r.1 ∧ ValidCoeff r.2 ∧
      (decodeHom r.1,decodeCoeff r.2) = PreparedLine.add (decodeHom p) (decode2 qx) (decode2 qy) ⦄ := by
  rcases hp with ⟨hpx,hpy,hpz⟩
  unfold CurveG1.pairing.prepared.HomG2.add
  step*
  all_goals simp_all [ValidHom, ValidCoeff, decodeHom, decodeCoeff, PreparedLine.add]

/-- The extracted M-twist line evaluation is ordinary multiplication by its sparse element. -/
@[step] theorem ell_spec (f : Raw12) (c : RawCoeff) (px py : ConcreteField.Raw)
    (hf : Valid12 f) (hc : ValidCoeff c) (hx : FieldProof.Valid px) (hy : FieldProof.Valid py) :
    CurveG1.pairing.prepared.ell f c px py ⦃ r => Valid12 r ∧
      decode12 r = decode12 f * ExtensionAlignment.sparseElement014
        (decode2 c.c0) (decode2 c.c1*Fp2.ofFp (ConcreteField.decode px))
        (decode2 c.c2*Fp2.ofFp (ConcreteField.decode py)) ⦄ := by
  rcases hc with ⟨hc0,hc1,hc2⟩
  unfold CurveG1.pairing.prepared.ell
  step*

#print axioms coefficient_spec
#print axioms double_spec
#print axioms add_spec
#print axioms ell_spec
end ConcretePreparedLine
