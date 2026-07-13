module

public import QuaternionicComputing.Semantics.Hierarchy.ProjectiveKernel

/-!
# Projective-to-input hierarchy audit

This non-root leaf consumes all nine projective-to-input covering arrows and
all six generic real/complex projective-kernel arrows, then gives explicit
quaternionic converse witnesses.  The witnesses use arbitrary two-by-two
matrices, not unitary channels: input-column and output-row phase remain
incomparable, while projective action is strictly stronger than each one-sided
phase family.

The public root deliberately does not import this file.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics.ProjectiveInputAudit

open QuaternionicComputing.Quaternion
open QuaternionicComputing.State

universe u v

/-! ## Complete consumer for the nine stable arrows -/

/-- A proof-term consumer for all raw, normalized, and circuit covering arrows. -/
theorem projectiveInput_arrows_api
    {O : Type u} {I : Type v} [Fintype I]
    {UR VR : Matrix O I ℝ}
    {UC VC : Matrix O I ℂ}
    {UQ VQ : Matrix O I ℍ[ℝ]}
    (hRawR : RealRawProjectiveActionEq UR VR)
    (hRawC : ComplexRawProjectiveActionEq UC VC)
    (hRawQ : QuaternionRawProjectiveActionEq UQ VQ)
    (hR : RealProjectiveActionEq UR VR)
    (hC : ComplexProjectiveActionEq UC VC)
    (hQ : QuaternionProjectiveActionEq UQ VQ)
    {W : Type*} [Fintype W]
    {CR DR : Circuit.OrderedCircuit ℝ W}
    {CC DC : Circuit.OrderedCircuit ℂ W}
    {CQ DQ : Circuit.OrderedCircuit ℍ[ℝ] W}
    (hCR : RealCircuitProjectiveActionEq CR DR)
    (hCC : ComplexCircuitProjectiveActionEq CC DC)
    (hCQ : QuaternionCircuitProjectiveActionEq CQ DQ) :
    RealInputBasisSignEq UR VR ∧
      ComplexInputBasisPhaseEq UC VC ∧
      QuaternionInputRightPhaseEq UQ VQ ∧
      RealInputBasisSignEq UR VR ∧
      ComplexInputBasisPhaseEq UC VC ∧
      QuaternionInputRightPhaseEq UQ VQ ∧
      RealCircuitInputBasisSignEq CR DR ∧
      ComplexCircuitInputBasisPhaseEq CC DC ∧
      QuaternionCircuitInputRightPhaseEq CQ DQ :=
  ⟨hRawR.inputBasisSignEq,
    hRawC.inputBasisPhaseEq,
    hRawQ.inputRightPhaseEq,
    hR.inputBasisSignEq,
    hC.inputBasisPhaseEq,
    hQ.inputRightPhaseEq,
    hCR.inputBasisSignEq,
    hCC.inputBasisPhaseEq,
    hCQ.inputRightPhaseEq⟩

/-! ## Generic real and complex projective kernels -/

/--
A proof-term consumer for the arbitrary-matrix real and complex projective
kernels at the raw, normalized, and evaluator-backed circuit levels.
-/
theorem realComplexProjectiveKernel_arrows_api
    {O : Type u} {I : Type v} [Fintype I]
    {UR VR : Matrix O I ℝ}
    {UC VC : Matrix O I ℂ}
    (hRawR : RealRawProjectiveActionEq UR VR)
    (hRawC : ComplexRawProjectiveActionEq UC VC)
    (hR : RealProjectiveActionEq UR VR)
    (hC : ComplexProjectiveActionEq UC VC)
    {W : Type*} [Fintype W]
    {CR DR : Circuit.OrderedCircuit ℝ W}
    {CC DC : Circuit.OrderedCircuit ℂ W}
    (hCR : RealCircuitProjectiveActionEq CR DR)
    (hCC : ComplexCircuitProjectiveActionEq CC DC) :
    RealGlobalSignEq UR VR ∧
      ComplexGlobalPhaseEq UC VC ∧
      RealGlobalSignEq UR VR ∧
      ComplexGlobalPhaseEq UC VC ∧
      RealCircuitGlobalSignEq CR DR ∧
      ComplexCircuitGlobalPhaseEq CC DC :=
  ⟨hRawR.globalSignEq,
    hRawC.globalPhaseEq,
    hR.globalSignEq,
    hC.globalPhaseEq,
    hCR.globalSignEq,
    hCC.globalPhaseEq⟩

/-! ## Quaternionic strictness witnesses -/

/-- The constant-one quaternionic matrix on two Boolean coordinates. -/
def quaternionAllOnes : Matrix Bool Bool ℍ[ℝ] :=
  fun _ _ ↦ 1

/-- Give the two input columns distinct right phases `i` and `j`. -/
def quaternionColumnTwist : Matrix Bool Bool ℍ[ℝ] :=
  fun _ x ↦ if x then j else i

/-- Give the two output rows distinct left phases `i` and `j`. -/
def quaternionRowTwist : Matrix Bool Bool ℍ[ℝ] :=
  fun y _ ↦ if y then j else i

/-- The normalized real-coordinate quaternionic column `(3/5,4/5)`. -/
def quaternionThreeFour : QuaternionState Bool :=
  ⟨fun x ↦ if x then
      (⟨4 / 5, 0, 0, 0⟩ : ℍ[ℝ])
    else (⟨3 / 5, 0, 0, 0⟩ : ℍ[ℝ]), by
    norm_num [quaternionTotalWeight, totalWeight, basisWeight,
      quaternionWeight, Fintype.univ_bool,
      _root_.Quaternion.normSq_def']⟩

/-- The column twist has exactly the advertised right input phases. -/
theorem quaternionColumnTwist_inputRightPhaseEq :
    QuaternionInputRightPhaseEq quaternionAllOnes quaternionColumnTwist := by
  refine ⟨fun x ↦ if x then j else i, ?_, ?_⟩
  · intro x
    cases x <;> simp [normSq_i, normSq_j]
  · intro y x
    cases x <;> simp [quaternionAllOnes, quaternionColumnTwist]

/-- Distinct column phases cannot be represented by one phase per output row. -/
theorem quaternionColumnTwist_not_outputLeftPhaseEq :
    ¬ QuaternionOutputLeftPhaseEq quaternionAllOnes quaternionColumnTwist := by
  rintro ⟨theta, _, htheta⟩
  have hi := htheta false false
  have hj := htheta false true
  simp [quaternionAllOnes, quaternionColumnTwist] at hi hj
  have hij : i = j := hi.trans hj.symm
  have him := congrArg (fun q : ℍ[ℝ] ↦ q.imI) hij
  norm_num [i, j] at him

/--
The normalized `(3/5,4/5)` input separates the column twist at the all-pure
basis-measurement level.
-/
theorem quaternionColumnTwist_not_pureInputBasisMeasurementEq :
    ¬ PureInputBasisMeasurementEq quaternionWeight
      quaternionAllOnes quaternionColumnTwist := by
  intro h
  have hw := h quaternionThreeFour false
  norm_num [OutputWeightEqAt, BasisWeightEq, basisWeight,
    quaternionWeight, Matrix.mulVec, dotProduct, Fintype.univ_bool,
    quaternionAllOnes, quaternionColumnTwist,
    quaternionThreeFour,
    _root_.Quaternion.normSq_def', i, j] at hw

/-- Complete strictness boundary for the input-column quaternionic branch. -/
theorem quaternionColumnTwist_boundary :
    QuaternionInputRightPhaseEq quaternionAllOnes quaternionColumnTwist ∧
      BasisMeasurementEq quaternionWeight
        quaternionAllOnes quaternionColumnTwist ∧
      ¬ QuaternionOutputLeftPhaseEq quaternionAllOnes quaternionColumnTwist ∧
      ¬ PureInputBasisMeasurementEq quaternionWeight
        quaternionAllOnes quaternionColumnTwist ∧
      ¬ QuaternionProjectiveActionEq quaternionAllOnes quaternionColumnTwist ∧
      ¬ QuaternionRawProjectiveActionEq quaternionAllOnes quaternionColumnTwist := by
  have hinput := quaternionColumnTwist_inputRightPhaseEq
  have hnotPure := quaternionColumnTwist_not_pureInputBasisMeasurementEq
  have hnotProjective :
      ¬ QuaternionProjectiveActionEq quaternionAllOnes quaternionColumnTwist := by
    intro h
    exact hnotPure h.pureInputBasisMeasurementEq
  have hnotRaw :
      ¬ QuaternionRawProjectiveActionEq quaternionAllOnes quaternionColumnTwist := by
    intro h
    exact hnotProjective h.projectiveActionEq
  exact ⟨hinput, hinput.basisMeasurementEq,
    quaternionColumnTwist_not_outputLeftPhaseEq,
    hnotPure, hnotProjective, hnotRaw⟩

/-- The row twist has exactly the advertised left output phases. -/
theorem quaternionRowTwist_outputLeftPhaseEq :
    QuaternionOutputLeftPhaseEq quaternionAllOnes quaternionRowTwist := by
  refine ⟨fun y ↦ if y then j else i, ?_, ?_⟩
  · intro y
    cases y <;> simp [normSq_i, normSq_j]
  · intro y x
    cases y <;> simp [quaternionAllOnes, quaternionRowTwist]

/-- Distinct row phases cannot be represented by one phase per input column. -/
theorem quaternionRowTwist_not_inputRightPhaseEq :
    ¬ QuaternionInputRightPhaseEq quaternionAllOnes quaternionRowTwist := by
  rintro ⟨phi, _, hphi⟩
  have hi := hphi false false
  have hj := hphi true false
  simp [quaternionAllOnes, quaternionRowTwist] at hi hj
  have hij : i = j := hi.trans hj.symm
  have him := congrArg (fun q : ℍ[ℝ] ↦ q.imI) hij
  norm_num [i, j] at him

/-- Complete strictness boundary for the output-row quaternionic branch. -/
theorem quaternionRowTwist_boundary :
    QuaternionOutputLeftPhaseEq quaternionAllOnes quaternionRowTwist ∧
      PureInputBasisMeasurementEq quaternionWeight
        quaternionAllOnes quaternionRowTwist ∧
      BasisMeasurementEq quaternionWeight
        quaternionAllOnes quaternionRowTwist ∧
      ¬ QuaternionInputRightPhaseEq quaternionAllOnes quaternionRowTwist ∧
      ¬ QuaternionProjectiveActionEq quaternionAllOnes quaternionRowTwist ∧
      ¬ QuaternionRawProjectiveActionEq quaternionAllOnes quaternionRowTwist := by
  have houtput := quaternionRowTwist_outputLeftPhaseEq
  have hnotInput := quaternionRowTwist_not_inputRightPhaseEq
  have hnotProjective :
      ¬ QuaternionProjectiveActionEq quaternionAllOnes quaternionRowTwist := by
    intro h
    exact hnotInput h.inputRightPhaseEq
  have hnotRaw :
      ¬ QuaternionRawProjectiveActionEq quaternionAllOnes quaternionRowTwist := by
    intro h
    exact hnotProjective h.projectiveActionEq
  exact ⟨houtput, houtput.pureInputBasisMeasurementEq,
    houtput.basisMeasurementEq, hnotInput, hnotProjective, hnotRaw⟩

/-! ## Selected local axiom endpoints -/

#print axioms projectiveInput_arrows_api
#print axioms realComplexProjectiveKernel_arrows_api
#print axioms quaternionColumnTwist_boundary
#print axioms quaternionRowTwist_boundary

end QuaternionicComputing.Semantics.ProjectiveInputAudit
