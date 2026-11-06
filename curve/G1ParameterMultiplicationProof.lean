import G1FastSubgroupProof
import GLVGroupRefinementProof

open EthLib.Cryptography.Bls

namespace G1ParameterMultiplication

/-- This small fixed scalar has a zero second GLV component, independently of its input point. -/
theorem parameter_components :
    GLVDecomposition.components (G1FastSubgroup.parameter % Fr.modulus : Int) =
      ((G1FastSubgroup.parameter : Int), 0) := by decide +kernel

/-- The subgroup algorithm's second multiplication is valid on the full curve, before membership is known. -/
theorem glv_parameter_correct (p : G1) (hp : G1Curve.OnCurve p) :
    G1Curve.OnCurve (GLVSchedule.mulProjective p G1FastSubgroup.parameter) ∧
    G1Curve.interpret (GLVSchedule.mulProjective p G1FastSubgroup.parameter) =
      G1FastSubgroup.parameter • G1Curve.interpret p := by
  simpa only [parameter_components, zero_zsmul, add_zero, natCast_zsmul] using
    GLVGroup.mul_projective_components p G1FastSubgroup.parameter hp

#print axioms parameter_components
#print axioms glv_parameter_correct
end G1ParameterMultiplication
