import CyclotomicProof

open EthLib.Cryptography.Bls

namespace CyclotomicSquare

local instance : CommRing Fp2 := QuadraticField.ringStructure
local instance : CommRing Fp6 := CubicField.ringStructure
local instance : CommRing Fp12 := DodecicField.ringStructure

private theorem ext2 (a b : Fp2) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl
private theorem ext6 (a b : Fp6) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; rfl
private theorem ext12 (a b : Fp12) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

abbrev omega : Fp2 := CubicFrobenius.coefficient 2

private theorem omega_square : omega^2 = -omega + -1 := by
  apply ext2 <;> decide +kernel
private theorem omega_cube : omega^3 = 1 := by
  apply ext2 <;> decide +kernel
private theorem omega_four : omega^4 = omega := by
  rw [show (4 : Nat) = 3+1 from rfl, pow_add, omega_cube, pow_one, one_mul]

private theorem cubic_two (a : Fp6) : a^(Fp.modulus^2) =
    ⟨a.c0,a.c1*omega,a.c2*(omega*omega)⟩ := by
  rw [←CubicFrobenius.map_eq_power a 2]
  apply ext6
  all_goals simp [CubicFrobenius.map, QuadraticField.pow_modulus_pow]

/-- The p-squared automorphism is diagonal in the six quadratic coordinates. -/
theorem power_two (a : Fp12) : a^(Fp.modulus^2) =
    ⟨⟨a.c0.c0,a.c0.c1*omega,a.c0.c2*(omega*omega)⟩,
     ⟨-(a.c1.c0*(omega*omega)),-a.c1.c1,-(a.c1.c2*omega)⟩⟩ := by
  rw [←DodecicField.powNat_eq_pow (Fp.modulus^2) a,
    ←DodecicFrobenius.map_eq_power a 2]
  have hc : DodecicFrobenius.coefficient 2 = -(omega*omega) := by
    apply ext2 <;> decide +kernel
  unfold DodecicFrobenius.map
  rw [cubic_two, cubic_two, hc, CubicField.mul_ofFp2]
  apply ext12
  · rfl
  · apply ext6
    · dsimp only
      ring
    · dsimp only
      linear_combination -a.c1.c1*omega_cube
    · dsimp only
      linear_combination -a.c1.c2*omega*omega_cube

private theorem cubic_coefficient_four : CubicFrobenius.coefficient 4 = omega*omega := by
  apply ext2 <;> decide +kernel
private theorem dodecic_coefficient_four : DodecicFrobenius.coefficient 4 = omega := by
  apply ext2 <;> decide +kernel
private theorem omega_square_square : (omega*omega)*(omega*omega) = omega := by
  calc
    (omega*omega)*(omega*omega) = omega^4 := by ring
    _ = omega := omega_four

private theorem cubic_four (b : Fp6) : b^(Fp.modulus^4) =
    ⟨b.c0,b.c1*(omega*omega),b.c2*omega⟩ := by
  rw [←CubicFrobenius.map_eq_power b 4]
  unfold CubicFrobenius.map
  simp only [QuadraticField.pow_modulus_pow]
  norm_num only [Nat.reduceMod, ite_true]
  rw [cubic_coefficient_four, omega_square_square]

private theorem mul_omega_cube (a : Fp2) : (a*(omega*omega))*omega = a := by
  calc
    (a*(omega*omega))*omega = a*omega^3 := by ring
    _ = a := by rw [omega_cube, mul_one]

private theorem power_eq_map (a : Fp12) (k : Nat) :
    a^(Fp.modulus^k) = DodecicFrobenius.map a k := by
  rw [←DodecicField.powNat_eq_pow, ←DodecicFrobenius.map_eq_power]

private theorem scale_four (a : Fp6) :
    (⟨a.c0,a.c1*(omega*omega),a.c2*omega⟩ : Fp6)*CubicField.ofFp2Hom omega =
      ⟨a.c0*omega,a.c1,a.c2*(omega*omega)⟩ := by
  rw [CubicField.mul_ofFp2]
  apply ext6
  · rfl
  · exact mul_omega_cube _
  · exact mul_assoc _ _ _

private theorem map_four (a : Fp12) : DodecicFrobenius.map a 4 =
    ⟨⟨a.c0.c0,a.c0.c1*(omega*omega),a.c0.c2*omega⟩,
     ⟨a.c1.c0*omega,a.c1.c1,a.c1.c2*(omega*omega)⟩⟩ := by
  apply ext12
  · exact cubic_four a.c0
  · change a.c1^(Fp.modulus^4)*CubicField.ofFp2Hom (DodecicFrobenius.coefficient 4) = _
    calc
      a.c1^(Fp.modulus^4)*CubicField.ofFp2Hom (DodecicFrobenius.coefficient 4) =
          (⟨a.c1.c0,a.c1.c1*(omega*omega),a.c1.c2*omega⟩ : Fp6)*
            CubicField.ofFp2Hom (DodecicFrobenius.coefficient 4) :=
        congrArg (fun x : Fp6 => x*CubicField.ofFp2Hom (DodecicFrobenius.coefficient 4))
          (cubic_four a.c1)
      _ = (⟨a.c1.c0,a.c1.c1*(omega*omega),a.c1.c2*omega⟩ : Fp6)*CubicField.ofFp2Hom omega :=
        congrArg (fun x : Fp2 =>
          (⟨a.c1.c0,a.c1.c1*(omega*omega),a.c1.c2*omega⟩ : Fp6)*CubicField.ofFp2Hom x)
          dodecic_coefficient_four
      _ = _ := scale_four a.c1

/-- Applying the fourth Frobenius table gives its diagonal on quadratic coordinates. -/
theorem power_four (a : Fp12) : a^(Fp.modulus^4) =
    ⟨⟨a.c0.c0,a.c0.c1*(omega*omega),a.c0.c2*omega⟩,
     ⟨a.c1.c0*omega,a.c1.c1,a.c1.c2*(omega*omega)⟩⟩ :=
  (power_eq_map a 4).trans (map_four a)

/-- Polynomial form of the source Granger–Scott schedule. -/
def square (a : Fp12) : Fp12 :=
  let r0 := a.c0.c0
  let r4 := a.c0.c1
  let r3 := a.c0.c2
  let r2 := a.c1.c0
  let r1 := a.c1.c1
  let r5 := a.c1.c2
  let xi := CubicField.xi
  let t0 := r0*r0+xi*(r1*r1)
  let t1 := 2*r0*r1
  let t2 := r2*r2+xi*(r3*r3)
  let t3 := 2*r2*r3
  let t4 := r4*r4+xi*(r5*r5)
  let t5 := 2*r4*r5
  ⟨⟨3*t0 + -(2*r0),3*t2 + -(2*r4),3*t4 + -(2*r3)⟩,
   ⟨3*xi*t5+2*r2,3*t1+2*r1,3*t3+2*r5⟩⟩

private theorem frobenius_relation (a : Fp12)
    (ha : a^(Fp.modulus^4-Fp.modulus^2+1) = 1) :
    a^(Fp.modulus^4)*a = a^(Fp.modulus^2) := by
  have he : Fp.modulus^4+1 = (Fp.modulus^4-Fp.modulus^2+1)+Fp.modulus^2 := by decide +kernel
  rw [←pow_succ, he, pow_add, ha, one_mul]

@[ext] private structure Coordinates (R : Type) where
  r0 : R
  r4 : R
  r3 : R
  r2 : R
  r1 : R
  r5 : R

private def multiply {R : Type} [CommRing R] (xi : R) (a b : Coordinates R) : Coordinates R :=
  ⟨a.r0*b.r0+xi*(a.r4*b.r3+a.r3*b.r4)+xi*(a.r2*b.r5+a.r1*b.r1+a.r5*b.r2),
   a.r0*b.r4+a.r4*b.r0+xi*(a.r3*b.r3)+a.r2*b.r2+xi*(a.r1*b.r5+a.r5*b.r1),
   a.r0*b.r3+a.r4*b.r4+a.r3*b.r0+a.r2*b.r1+a.r1*b.r2+xi*(a.r5*b.r5),
   a.r0*b.r2+xi*(a.r4*b.r5+a.r3*b.r1)+a.r2*b.r0+xi*(a.r1*b.r3+a.r5*b.r4),
   a.r0*b.r1+a.r4*b.r2+xi*(a.r3*b.r5)+a.r2*b.r4+a.r1*b.r0+xi*(a.r5*b.r3),
   a.r0*b.r5+a.r4*b.r1+a.r3*b.r2+a.r2*b.r3+a.r1*b.r4+a.r5*b.r0⟩

private def diagonal2 {R : Type} [CommRing R] (w : R) (a : Coordinates R) : Coordinates R :=
  ⟨a.r0,a.r4*w,a.r3*(w*w),-(a.r2*(w*w)),-a.r1,-(a.r5*w)⟩
private def diagonal4 {R : Type} [CommRing R] (w : R) (a : Coordinates R) : Coordinates R :=
  ⟨a.r0,a.r4*(w*w),a.r3*w,a.r2*w,a.r1,a.r5*(w*w)⟩
private def grangerScott {R : Type} [CommRing R] (xi : R) (a : Coordinates R) : Coordinates R :=
  ⟨3*(a.r0*a.r0+xi*(a.r1*a.r1)) + -(2*a.r0),
   3*(a.r2*a.r2+xi*(a.r3*a.r3)) + -(2*a.r4),
   3*(a.r4*a.r4+xi*(a.r5*a.r5)) + -(2*a.r3),
   3*xi*(2*a.r4*a.r5)+2*a.r2,
   3*(2*a.r0*a.r1)+2*a.r1,
   3*(2*a.r2*a.r3)+2*a.r5⟩

private theorem coordinate_identity {R : Type} [CommRing R] (xi w : R) (a : Coordinates R)
    (hw2 : w^2 = -w + -1) (hw3 : w^3 = 1) (hw4 : w^4 = w)
    (h : multiply xi (diagonal4 w a) a = diagonal2 w a) :
    grangerScott xi a = multiply xi a a := by
  have e0 := congrArg Coordinates.r0 h
  have e4 := congrArg Coordinates.r4 h
  have e3 := congrArg Coordinates.r3 h
  have e2 := congrArg Coordinates.r2 h
  have e1 := congrArg Coordinates.r1 h
  have e5 := congrArg Coordinates.r5 h
  dsimp only [multiply, diagonal4, diagonal2] at e0 e4 e3 e2 e1 e5
  apply Coordinates.ext
  all_goals dsimp only [grangerScott, multiply]
  · linear_combination (norm := (ring_nf; simp only [hw2]; ring)) 2*e0
  · linear_combination (norm := (ring_nf; simp only [hw2,hw3,hw4]; ring)) 2*w^2*e4
  · linear_combination (norm := (ring_nf; simp only [hw2,hw3]; ring)) 2*w*e3
  · linear_combination (norm := (ring_nf; simp only [hw2,hw3]; ring)) 2*w*e2
  · linear_combination (norm := (ring_nf; simp only [hw2]; ring)) 2*e1
  · linear_combination (norm := (ring_nf; simp only [hw2,hw3,hw4]; ring)) 2*w^2*e5

private def coordinates (a : Fp12) : Coordinates Fp2 :=
  ⟨a.c0.c0,a.c0.c1,a.c0.c2,a.c1.c0,a.c1.c1,a.c1.c2⟩

private theorem coordinates_mul (a b : Fp12) :
    coordinates (a*b) = multiply CubicField.xi (coordinates a) (coordinates b) := by
  apply Coordinates.ext
  all_goals simp [coordinates, multiply, Fp6.v]
  all_goals ring

private theorem coordinates_injective (a b : Fp12) (h : coordinates a = coordinates b) : a = b := by
  apply ext12
  · apply ext6
    · exact congrArg Coordinates.r0 h
    · exact congrArg Coordinates.r4 h
    · exact congrArg Coordinates.r3 h
  · apply ext6
    · exact congrArg Coordinates.r2 h
    · exact congrArg Coordinates.r1 h
    · exact congrArg Coordinates.r5 h

/-- The optimized polynomial agrees with ordinary squaring on the cyclotomic subgroup. -/
theorem square_correct (a : Fp12) (ha : a^(Fp.modulus^4-Fp.modulus^2+1) = 1) :
    square a = a*a := by
  have h := congrArg coordinates (frobenius_relation a ha)
  rw [coordinates_mul, power_four, power_two] at h
  change multiply CubicField.xi (diagonal4 omega (coordinates a)) (coordinates a) =
    diagonal2 omega (coordinates a) at h
  apply coordinates_injective
  change grangerScott CubicField.xi (coordinates a) = coordinates (a*a)
  rw [coordinates_mul]
  exact coordinate_identity _ _ _ omega_square omega_cube omega_four h

/-- The optimized branch is the branch selected by the BLS12-381 characteristic. -/
theorem characteristic_guard : (Fp.modulus%6)^2%6 = 1 := by decide +kernel

/-- The polynomial formula preserves the live API's zero case. -/
theorem square_zero : square (0 : Fp12) = 0 := by
  apply ext12
  all_goals apply ext6
  all_goals simp [square]

/-- Inputs established by the easy-stage proof, including its total zero adapter. -/
def Admissible (a : Fp12) : Prop := a = 0 ∨ a^(Fp.modulus^4-Fp.modulus^2+1) = 1

theorem square_correct_on_domain (a : Fp12) (ha : Admissible a) : square a = a*a := by
  rcases ha with h | h
  · rw [h, square_zero, mul_zero]
  · exact square_correct a h

/-- Ordinary squaring preserves the domain required by the optimized next square. -/
theorem squared_admissible (a : Fp12) (ha : Admissible a) : Admissible (a*a) := by
  rcases ha with h | h
  · left
    rw [h, mul_zero]
  · right
    rw [mul_pow, h, mul_one]

#print axioms characteristic_guard
#print axioms square_zero
#print axioms square_correct_on_domain
#print axioms squared_admissible
#print axioms power_two
#print axioms power_four
#print axioms square_correct
end CyclotomicSquare
