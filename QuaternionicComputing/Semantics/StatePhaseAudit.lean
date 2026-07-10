module

public import QuaternionicComputing.Semantics.StatePhase

/-!
# Normalized state-phase semantic audit

This non-root diagnostic leaf exercises the complete Stage 3A state-phase API.
It also repairs the normalization defect in the older quaternionic left-phase
counterexample: the original `(1, 1)` column has total weight two, while the
replacement `(3/5, 4/5)` column and both of its evolved outputs have total
weight one.

The left-phase example is only a rejection certificate.  Public quaternionic
state phase remains right-sided throughout `Semantics.StatePhase`.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion

namespace QuaternionicComputing.Semantics.StatePhaseAudit

open QuaternionicComputing.State
open QuaternionicComputing.Quaternion

/-! ## Normalized quaternionic left-phase rejection witness -/

/-- The original raw witness is not normalized: its total quaternionic weight is two. -/
theorem phaseWitnessInput_totalWeight :
    quaternionTotalWeight phaseWitnessInput = 2 := by
  simp [quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight,
    phaseWitnessInput, Fintype.univ_bool, _root_.Quaternion.normSq_def']

/-- A normalized two-coordinate replacement with nonzero real amplitudes. -/
def normalizedPhaseWitnessInput : Bool → ℍ[ℝ]
  | false => ⟨3 / 5, 0, 0, 0⟩
  | true => ⟨4 / 5, 0, 0, 0⟩

/-- The repaired input column has exact total quaternionic weight one. -/
theorem normalizedPhaseWitnessInput_totalWeight :
    quaternionTotalWeight normalizedPhaseWitnessInput = 1 := by
  simp [quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight,
    normalizedPhaseWitnessInput, Fintype.univ_bool,
    _root_.Quaternion.normSq_def']
  norm_num

/-- The repaired input packaged as a normalized quaternionic state. -/
def normalizedPhaseWitnessState : QuaternionState Bool :=
  ⟨normalizedPhaseWitnessInput, normalizedPhaseWitnessInput_totalWeight⟩

/-- The unit left-`i` multiple of the repaired input. -/
def normalizedLeftPhaseWitnessInput : Bool → ℍ[ℝ] :=
  i • normalizedPhaseWitnessInput

/-- The left-`i` input remains exactly normalized. -/
theorem normalizedLeftPhaseWitnessInput_totalWeight :
    quaternionTotalWeight normalizedLeftPhaseWitnessInput = 1 := by
  simp [normalizedLeftPhaseWitnessInput, normalizedPhaseWitnessInput,
    quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight,
    Fintype.univ_bool, _root_.Quaternion.normSq_def', i]
  norm_num

/-- The left-`i` input packaged as a normalized quaternionic state. -/
def normalizedLeftPhaseWitnessState : QuaternionState Bool :=
  ⟨normalizedLeftPhaseWitnessInput,
    normalizedLeftPhaseWitnessInput_totalWeight⟩

/-- The diagnostic gate preserves quaternionic total weight on every Bool column. -/
theorem phaseWitnessGate_quaternionTotalWeight (x : Bool → ℍ[ℝ]) :
    quaternionTotalWeight (phaseWitnessGate x) = quaternionTotalWeight x := by
  simpa [quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight]
    using phaseWitnessGate_normSq x

/-- The evolved repaired input column. -/
def normalizedPhaseWitnessOutput : Bool → ℍ[ℝ] :=
  phaseWitnessGate normalizedPhaseWitnessInput

/-- The evolved repaired input remains exactly normalized. -/
theorem normalizedPhaseWitnessOutput_totalWeight :
    quaternionTotalWeight normalizedPhaseWitnessOutput = 1 := by
  rw [normalizedPhaseWitnessOutput,
    phaseWitnessGate_quaternionTotalWeight,
    normalizedPhaseWitnessInput_totalWeight]

/-- The evolved repaired input packaged as a normalized quaternionic state. -/
def normalizedPhaseWitnessOutputState : QuaternionState Bool :=
  ⟨normalizedPhaseWitnessOutput, normalizedPhaseWitnessOutput_totalWeight⟩

/-- The evolved left-`i` input column. -/
def normalizedLeftPhaseWitnessOutput : Bool → ℍ[ℝ] :=
  phaseWitnessGate normalizedLeftPhaseWitnessInput

/-- The evolved left-`i` input remains exactly normalized. -/
theorem normalizedLeftPhaseWitnessOutput_totalWeight :
    quaternionTotalWeight normalizedLeftPhaseWitnessOutput = 1 := by
  rw [normalizedLeftPhaseWitnessOutput,
    phaseWitnessGate_quaternionTotalWeight,
    normalizedLeftPhaseWitnessInput_totalWeight]

/-- The evolved left-`i` input packaged as a normalized quaternionic state. -/
def normalizedLeftPhaseWitnessOutputState : QuaternionState Bool :=
  ⟨normalizedLeftPhaseWitnessOutput,
    normalizedLeftPhaseWitnessOutput_totalWeight⟩

/-- All four columns used by the repaired diagnostic have exact total weight one. -/
theorem normalizedWitness_all_totalWeights :
    quaternionTotalWeight normalizedPhaseWitnessInput = 1 ∧
      quaternionTotalWeight normalizedLeftPhaseWitnessInput = 1 ∧
      quaternionTotalWeight normalizedPhaseWitnessOutput = 1 ∧
      quaternionTotalWeight normalizedLeftPhaseWitnessOutput = 1 :=
  ⟨normalizedPhaseWitnessInput_totalWeight,
    normalizedLeftPhaseWitnessInput_totalWeight,
    normalizedPhaseWitnessOutput_totalWeight,
    normalizedLeftPhaseWitnessOutput_totalWeight⟩

/-- The two repaired normalized inputs lie on the same candidate left-phase ray. -/
theorem normalized_leftPhaseEquivalent_i_input :
    LeftPhaseEquivalent
      normalizedLeftPhaseWitnessInput normalizedPhaseWitnessInput := by
  exact ⟨i, normSq_i, rfl⟩

/-- The norm-preserving gate separates the repaired normalized left-phase inputs. -/
theorem normalized_not_leftPhaseEquivalent_gate_i_input :
    ¬ LeftPhaseEquivalent
      normalizedLeftPhaseWitnessOutput normalizedPhaseWitnessOutput := by
  change ¬ LeftPhaseEquivalent
    (phaseWitnessGate (i • normalizedPhaseWitnessInput))
    (phaseWitnessGate normalizedPhaseWitnessInput)
  rintro ⟨eta, _, heta⟩
  have hfalse := congrFun heta false
  have htrue := congrFun heta true
  simp only [phaseWitnessGate, normalizedPhaseWitnessInput, Pi.smul_apply,
    smul_eq_mul] at hfalse htrue
  have hre := congrArg (fun q : ℍ[ℝ] => q.re) hfalse
  have himI := congrArg (fun q : ℍ[ℝ] => q.imI) hfalse
  have himJ := congrArg (fun q : ℍ[ℝ] => q.imJ) hfalse
  have himK := congrArg (fun q : ℍ[ℝ] => q.imK) hfalse
  have heta_eq : i = eta := by
    apply QuaternionAlgebra.ext
    all_goals norm_num [i] at hre himI himJ himK ⊢
    all_goals linarith
  subst eta
  have hgateK := congrArg (fun q : ℍ[ℝ] => q.imK) htrue
  norm_num [i, j] at hgateK

/-! ## Concrete normalized reference states and unit phases -/

/-- A normalized real basis state used by the sign diagnostics. -/
def realReferenceState : RealState Bool :=
  ⟨fun b => if b then 0 else 1, by
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool]⟩

/-- The real unit-sign certificate for `-1`. -/
theorem real_negOne_sq : (-1 : ℝ) * (-1) = 1 := by
  norm_num

/-- The reference real state multiplied on the right by `-1`. -/
def realNegOneState : RealState Bool :=
  State.RealState.rightSign realReferenceState (-1) real_negOne_sq

/-- A normalized complex basis state used by the phase diagnostics. -/
def complexReferenceState : ComplexState Bool :=
  ⟨fun b => if b then 0 else 1, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

/-- The complex phase `I` has unit norm square. -/
theorem complex_I_normSq : _root_.Complex.normSq Complex.I = 1 := by
  simp [_root_.Complex.normSq_apply]

/-- The reference complex state multiplied on the right by `I`. -/
def complexIState : ComplexState Bool :=
  State.ComplexState.rightPhase complexReferenceState Complex.I
    complex_I_normSq

/-- A normalized quaternionic basis state used by the phase diagnostics. -/
def quaternionReferenceState : QuaternionState Bool :=
  ⟨fun b => if b then 0 else 1, by
    simp [totalWeight, basisWeight, quaternionWeight, Fintype.univ_bool]⟩

/-- The reference quaternionic state multiplied strictly on the right by `j`. -/
def quaternionJState : QuaternionState Bool :=
  State.QuaternionState.rightPhase quaternionReferenceState j normSq_j

/-! ## Complete consumer for the reusable real-sign leaf -/

/-- Every declaration introduced by `State.RealPhase` has a named diagnostic consumer. -/
theorem realSign_api
    (x y z : Bool → ℝ) (s : ℝ)
    (hxy : Real.SignEquivalent x y)
    (hyz : Real.SignEquivalent y z)
    (hs : s * s = 1) (A : Matrix Bool Bool ℝ) (b : Bool) :
    Real.SignEquivalent x x ∧
      Real.SignEquivalent y x ∧
      Real.SignEquivalent x z ∧
      Real.SignEquivalent x x ∧
      (s * s = 1 ↔ s = 1 ∨ s = -1) ∧
      (Real.SignEquivalent x y ↔ x = y ∨ x = -y) ∧
      realBasisWeight (fun i => x i * s) b =
        realBasisWeight x b * (s * s) ∧
      realBasisWeight (fun i => x i * s) b = realBasisWeight x b ∧
      realTotalWeight (fun i => x i * s) =
        realTotalWeight x * (s * s) ∧
      realTotalWeight (fun i => x i * s) = realTotalWeight x ∧
      realBasisWeight x b = realBasisWeight y b ∧
      realTotalWeight x = realTotalWeight y ∧
      A *ᵥ (fun i => x i * s) = (fun i => (A *ᵥ x) i * s) ∧
      Real.SignEquivalent (A *ᵥ x) (A *ᵥ y) := by
  exact ⟨Real.signEquivalent_refl x,
    Real.signEquivalent_symm hxy,
    Real.signEquivalent_trans hxy hyz,
    Real.signEquivalent_equivalence.1 x,
    Real.sign_sq_eq_one_iff,
    Real.signEquivalent_iff_eq_or_eq_neg x y,
    realBasisWeight_right_mul x s b,
    realBasisWeight_right_mul_of_sq_eq_one x s hs b,
    realTotalWeight_right_mul x s,
    realTotalWeight_right_mul_of_sq_eq_one x s hs,
    signEquivalent_realBasisWeight hxy b,
    signEquivalent_realTotalWeight hxy,
    real_mulVec_right_mul A x s,
    signEquivalent_real_mulVec A hxy⟩

/-- The normalized `-1` example consumes the state-level real-sign constructors and laws. -/
theorem realNegOneState_api (b : Bool) :
    State.RealState.rightSign realReferenceState (-1) real_negOne_sq b =
        realReferenceState b * (-1) ∧
      realBasisWeight
          (State.RealState.rightSign realReferenceState (-1) real_negOne_sq) b =
        realBasisWeight realReferenceState b ∧
      realTotalWeight
          (State.RealState.rightSign realReferenceState (-1) real_negOne_sq) =
        realTotalWeight realReferenceState ∧
      Real.SignEquivalent
        (State.RealState.rightSign realReferenceState (-1) real_negOne_sq :
          Bool → ℝ)
        realReferenceState := by
  exact ⟨State.RealState.rightSign_apply _ _ _ b,
    State.RealState.rightSign_basisWeight _ _ _ b,
    State.RealState.rightSign_totalWeight _ _ _,
    State.RealState.signEquivalent_rightSign _ _ _⟩

/-! ## Exact and phase semantic API consumers -/

/-- Every exact normalized-state declaration has a generic named consumer. -/
theorem exactState_api
    {R I : Type*} [Fintype I] {weight : R → ℝ}
    (a b c : NormalizedState I R weight)
    (hab : ExactStateEq a b) (hbc : ExactStateEq b c)
    (hweight : ∀ r, 0 ≤ weight r) :
    ExactStateEq a a ∧
      ExactStateEq b a ∧
      ExactStateEq a c ∧
      ExactStateEq a a ∧
      (ExactStateEq a b ↔ a = b) ∧
      ExactStateEq a b ∧
      a = b ∧
      BasisWeightEq weight a b ∧
      NormalizedDistributionEq weight hweight a b := by
  exact ⟨ExactStateEq.refl a,
    ExactStateEq.symm hab,
    ExactStateEq.trans hab hbc,
    ExactStateEq.equivalence.1 a,
    ExactStateEq.iff_eq,
    ExactStateEq.of_eq (ExactStateEq.eq hab),
    ExactStateEq.eq hab,
    ExactStateEq.basisWeightEq hab,
    ExactStateEq.normalizedDistributionEq hweight hab⟩

/-- The concrete real `-1` ray consumes the complete real semantic phase surface. -/
theorem realNegOne_semantic_api
    (U : Matrix Bool Bool ℝ) (hU : U ∈ unitary (Matrix Bool Bool ℝ)) :
    (RealStatePhaseEq realNegOneState realReferenceState ↔
        Real.SignEquivalent (realNegOneState : Bool → ℝ) realReferenceState) ∧
      RealStatePhaseEq realReferenceState realReferenceState ∧
      RealStatePhaseEq realReferenceState realNegOneState ∧
      RealStatePhaseEq realNegOneState realNegOneState ∧
      RealStatePhaseEq realReferenceState realReferenceState ∧
      RealStatePhaseEq realReferenceState realReferenceState ∧
      RealStatePhaseEq realNegOneState realReferenceState ∧
      RealStatePhaseEq
        (State.RealState.rightSign realReferenceState (-1) real_negOne_sq)
        realReferenceState ∧
      BasisWeightEq State.realWeight realNegOneState realReferenceState ∧
      NormalizedDistributionEq State.realWeight State.realWeight_nonneg
        realNegOneState realReferenceState ∧
      Real.SignEquivalent
        (U *ᵥ (realNegOneState : Bool → ℝ))
        (U *ᵥ (realReferenceState : Bool → ℝ)) ∧
      RealStatePhaseEq
        (State.RealState.evolveUnitary realNegOneState U hU)
        (State.RealState.evolveUnitary realReferenceState U hU) := by
  have hphase : RealStatePhaseEq realNegOneState realReferenceState :=
    RealStatePhaseEq.rightSign realReferenceState (-1) real_negOne_sq
  have hfromSign : RealStatePhaseEq realNegOneState realReferenceState := by
    apply RealStatePhaseEq.of_sign (-1) real_negOne_sq
    rfl
  exact ⟨RealStatePhaseEq.iff_signEquivalent,
    RealStatePhaseEq.refl realReferenceState,
    RealStatePhaseEq.symm hphase,
    RealStatePhaseEq.trans hphase (RealStatePhaseEq.symm hphase),
    RealStatePhaseEq.equivalence.1 realReferenceState,
    RealStatePhaseEq.of_exact (ExactStateEq.refl realReferenceState),
    hfromSign,
    RealStatePhaseEq.rightSign realReferenceState (-1) real_negOne_sq,
    RealStatePhaseEq.basisWeightEq hphase,
    RealStatePhaseEq.normalizedDistributionEq hphase,
    RealStatePhaseEq.raw_mulVec U hphase,
    RealStatePhaseEq.evolveUnitary U hU hphase⟩

/-- The concrete complex `I` ray consumes the complete complex semantic phase surface. -/
theorem complexI_semantic_api
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitary (Matrix Bool Bool ℂ)) :
    (ComplexStatePhaseEq complexIState complexReferenceState ↔
        Complex.RightPhaseEquivalent
          (complexIState : Bool → ℂ) complexReferenceState) ∧
      ComplexStatePhaseEq complexReferenceState complexReferenceState ∧
      ComplexStatePhaseEq complexReferenceState complexIState ∧
      ComplexStatePhaseEq complexIState complexIState ∧
      ComplexStatePhaseEq complexReferenceState complexReferenceState ∧
      ComplexStatePhaseEq complexReferenceState complexReferenceState ∧
      ComplexStatePhaseEq complexIState complexReferenceState ∧
      ComplexStatePhaseEq
        (State.ComplexState.rightPhase complexReferenceState Complex.I
          complex_I_normSq)
        complexReferenceState ∧
      BasisWeightEq State.complexWeight complexIState complexReferenceState ∧
      NormalizedDistributionEq State.complexWeight State.complexWeight_nonneg
        complexIState complexReferenceState ∧
      Complex.RightPhaseEquivalent
        (U *ᵥ (complexIState : Bool → ℂ))
        (U *ᵥ (complexReferenceState : Bool → ℂ)) ∧
      ComplexStatePhaseEq
        (State.ComplexState.evolveUnitary complexIState U hU)
        (State.ComplexState.evolveUnitary complexReferenceState U hU) := by
  have hphase : ComplexStatePhaseEq complexIState complexReferenceState :=
    ComplexStatePhaseEq.rightPhase complexReferenceState Complex.I
      complex_I_normSq
  have hfromPhase : ComplexStatePhaseEq complexIState complexReferenceState := by
    apply ComplexStatePhaseEq.of_phase Complex.I complex_I_normSq
    rfl
  exact ⟨ComplexStatePhaseEq.iff_rightPhaseEquivalent,
    ComplexStatePhaseEq.refl complexReferenceState,
    ComplexStatePhaseEq.symm hphase,
    ComplexStatePhaseEq.trans hphase (ComplexStatePhaseEq.symm hphase),
    ComplexStatePhaseEq.equivalence.1 complexReferenceState,
    ComplexStatePhaseEq.of_exact (ExactStateEq.refl complexReferenceState),
    hfromPhase,
    ComplexStatePhaseEq.rightPhase complexReferenceState Complex.I
      complex_I_normSq,
    ComplexStatePhaseEq.basisWeightEq hphase,
    ComplexStatePhaseEq.normalizedDistributionEq hphase,
    ComplexStatePhaseEq.raw_mulVec U hphase,
    ComplexStatePhaseEq.evolveUnitary U hU hphase⟩

/-- The concrete quaternionic right-`j` ray consumes the complete quaternion API. -/
theorem quaternionJ_semantic_api
    (U : Matrix Bool Bool ℍ[ℝ])
    (hU : U ∈ unitary (Matrix Bool Bool ℍ[ℝ])) :
    (QuaternionStatePhaseEq quaternionJState quaternionReferenceState ↔
        RightPhaseEquivalent
          (quaternionJState : Bool → ℍ[ℝ]) quaternionReferenceState) ∧
      QuaternionStatePhaseEq quaternionReferenceState quaternionReferenceState ∧
      QuaternionStatePhaseEq quaternionReferenceState quaternionJState ∧
      QuaternionStatePhaseEq quaternionJState quaternionJState ∧
      QuaternionStatePhaseEq quaternionReferenceState quaternionReferenceState ∧
      QuaternionStatePhaseEq quaternionReferenceState quaternionReferenceState ∧
      QuaternionStatePhaseEq quaternionJState quaternionReferenceState ∧
      QuaternionStatePhaseEq
        (State.QuaternionState.rightPhase quaternionReferenceState j normSq_j)
        quaternionReferenceState ∧
      BasisWeightEq State.quaternionWeight
        quaternionJState quaternionReferenceState ∧
      NormalizedDistributionEq State.quaternionWeight
        State.quaternionWeight_nonneg quaternionJState quaternionReferenceState ∧
      RightPhaseEquivalent
        (U *ᵥ (quaternionJState : Bool → ℍ[ℝ]))
        (U *ᵥ (quaternionReferenceState : Bool → ℍ[ℝ])) ∧
      QuaternionStatePhaseEq
        (State.QuaternionState.evolveUnitary quaternionJState U hU)
        (State.QuaternionState.evolveUnitary quaternionReferenceState U hU) := by
  have hphase : QuaternionStatePhaseEq
      quaternionJState quaternionReferenceState :=
    QuaternionStatePhaseEq.rightPhase quaternionReferenceState j normSq_j
  have hfromPhase : QuaternionStatePhaseEq
      quaternionJState quaternionReferenceState := by
    apply QuaternionStatePhaseEq.of_phase j normSq_j
    rfl
  exact ⟨QuaternionStatePhaseEq.iff_rightPhaseEquivalent,
    QuaternionStatePhaseEq.refl quaternionReferenceState,
    QuaternionStatePhaseEq.symm hphase,
    QuaternionStatePhaseEq.trans hphase
      (QuaternionStatePhaseEq.symm hphase),
    QuaternionStatePhaseEq.equivalence.1 quaternionReferenceState,
    QuaternionStatePhaseEq.of_exact
      (ExactStateEq.refl quaternionReferenceState),
    hfromPhase,
    QuaternionStatePhaseEq.rightPhase quaternionReferenceState j normSq_j,
    QuaternionStatePhaseEq.basisWeightEq hphase,
    QuaternionStatePhaseEq.normalizedDistributionEq hphase,
    QuaternionStatePhaseEq.raw_mulVec U hphase,
    QuaternionStatePhaseEq.evolveUnitary U hU hphase⟩

/-- The three circuit-specialized raw-evaluation theorems have one direct consumer. -/
theorem circuitRawEval_api
    {W : Type*} [Fintype W]
    (realCircuit : Circuit.OrderedCircuit ℝ W)
    (complexCircuit : Circuit.OrderedCircuit ℂ W)
    (quaternionCircuit : Circuit.OrderedCircuit ℍ[ℝ] W)
    {realA realB : RealState (Circuit.BitBasis W)}
    {complexA complexB : ComplexState (Circuit.BitBasis W)}
    {quaternionA quaternionB : QuaternionState (Circuit.BitBasis W)}
    (hreal : RealStatePhaseEq realA realB)
    (hcomplex : ComplexStatePhaseEq complexA complexB)
    (hquaternion : QuaternionStatePhaseEq quaternionA quaternionB) :
    Real.SignEquivalent
        (realCircuit.eval *ᵥ (realA : Circuit.BitBasis W → ℝ))
        (realCircuit.eval *ᵥ (realB : Circuit.BitBasis W → ℝ)) ∧
      Complex.RightPhaseEquivalent
        (complexCircuit.eval *ᵥ (complexA : Circuit.BitBasis W → ℂ))
        (complexCircuit.eval *ᵥ (complexB : Circuit.BitBasis W → ℂ)) ∧
      RightPhaseEquivalent
        (quaternionCircuit.eval *ᵥ
          (quaternionA : Circuit.BitBasis W → ℍ[ℝ]))
        (quaternionCircuit.eval *ᵥ
          (quaternionB : Circuit.BitBasis W → ℍ[ℝ])) := by
  exact ⟨RealStatePhaseEq.raw_eval realCircuit hreal,
    ComplexStatePhaseEq.raw_eval complexCircuit hcomplex,
    QuaternionStatePhaseEq.raw_eval quaternionCircuit hquaternion⟩

end QuaternionicComputing.Semantics.StatePhaseAudit

#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.normalizedWitness_all_totalWeights
#print axioms
  QuaternionicComputing.Semantics.StatePhaseAudit.normalized_not_leftPhaseEquivalent_gate_i_input
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.realSign_api
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.exactState_api
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.realNegOne_semantic_api
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.complexI_semantic_api
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.quaternionJ_semantic_api
#print axioms QuaternionicComputing.Semantics.StatePhaseAudit.circuitRawEval_api
