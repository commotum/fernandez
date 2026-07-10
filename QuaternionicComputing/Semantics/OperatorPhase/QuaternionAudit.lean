module

public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionKernel

/-!
# Quaternionic operator-phase audit

This non-root diagnostic leaf gives named consumers for every stable
declaration exported by `Quaternion`, `QuaternionCircuit`, and
`QuaternionKernel`.  It also specializes the projective kernel to the
two-dimensional `Bool` space, checks the right-input/left-output multiplication
orders, and records both a central `-1` example and the rank-one `j` exception.

The public root deliberately does not import this file.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

/-! ## Complete consumers for the operator relations -/

/-- Complete named consumer for the central real-sign operator API. -/
theorem quaternionCentralSign_api (U V T : Matrix Bool Bool ℍ[ℝ])
    (hUV : QuaternionCentralSignEq U V)
    (hVT : QuaternionCentralSignEq V T)
    (hexact : ExactOperatorEq U V)
    (hU : U ∈ unitary (Matrix Bool Bool ℍ[ℝ])) :
    QuaternionCentralSignEq U U ∧
      QuaternionCentralSignEq V U ∧
      QuaternionCentralSignEq U T ∧
      QuaternionCentralSignEq U U ∧
      QuaternionCentralSignEq U V ∧
      QuaternionInputRightPhaseEq U V ∧
      QuaternionOutputLeftPhaseEq U V ∧
      QuaternionRawProjectiveActionEq U V ∧
      QuaternionProjectiveActionEq U V ∧
      V ∈ unitary (Matrix Bool Bool ℍ[ℝ]) ∧
      (U ∈ unitary (Matrix Bool Bool ℍ[ℝ]) ↔
        V ∈ unitary (Matrix Bool Bool ℍ[ℝ])) ∧
      QuaternionCentralSignEq (U * U) (V * V) := by
  exact ⟨QuaternionCentralSignEq.refl U,
    QuaternionCentralSignEq.symm hUV,
    QuaternionCentralSignEq.trans hUV hVT,
    QuaternionCentralSignEq.equivalence.1 U,
    QuaternionCentralSignEq.of_exact hexact,
    QuaternionCentralSignEq.inputRightPhaseEq hUV,
    QuaternionCentralSignEq.outputLeftPhaseEq hUV,
    QuaternionCentralSignEq.rawProjectiveActionEq hUV,
    QuaternionCentralSignEq.projectiveActionEq hUV,
    QuaternionCentralSignEq.mem_unitary hUV hU,
    QuaternionCentralSignEq.mem_unitary_iff hUV,
    QuaternionCentralSignEq.mul hUV hUV⟩

/-- Complete named consumer for input-column phases acting on the right. -/
theorem quaternionInputRightPhase_api
    (U V T A : Matrix Bool Bool ℍ[ℝ])
    (hUV : QuaternionInputRightPhaseEq U V)
    (hVT : QuaternionInputRightPhaseEq V T)
    (hexact : ExactOperatorEq U V) :
    QuaternionInputRightPhaseEq U U ∧
      QuaternionInputRightPhaseEq V U ∧
      QuaternionInputRightPhaseEq U T ∧
      QuaternionInputRightPhaseEq U U ∧
      QuaternionInputRightPhaseEq U V ∧
      BasisMeasurementEq State.quaternionWeight U V ∧
      QuaternionInputRightPhaseEq (A * U) (A * V) := by
  exact ⟨QuaternionInputRightPhaseEq.refl U,
    QuaternionInputRightPhaseEq.symm hUV,
    QuaternionInputRightPhaseEq.trans hUV hVT,
    QuaternionInputRightPhaseEq.equivalence.1 U,
    QuaternionInputRightPhaseEq.of_exact hexact,
    QuaternionInputRightPhaseEq.basisMeasurementEq hUV,
    QuaternionInputRightPhaseEq.mul_left A hUV⟩

/-- Complete named consumer for output-row phases acting on the left. -/
theorem quaternionOutputLeftPhase_api
    (U V T B : Matrix Bool Bool ℍ[ℝ]) (psi : Bool → ℍ[ℝ])
    (hUV : QuaternionOutputLeftPhaseEq U V)
    (hVT : QuaternionOutputLeftPhaseEq V T)
    (hexact : ExactOperatorEq U V) :
    QuaternionOutputLeftPhaseEq U U ∧
      QuaternionOutputLeftPhaseEq V U ∧
      QuaternionOutputLeftPhaseEq U T ∧
      QuaternionOutputLeftPhaseEq U U ∧
      QuaternionOutputLeftPhaseEq U V ∧
      BasisMeasurementEq State.quaternionWeight U V ∧
      (∃ theta : Bool → ℍ[ℝ],
        (∀ y, _root_.Quaternion.normSq (theta y) = 1) ∧
          V *ᵥ psi = fun y ↦ theta y * (U *ᵥ psi) y) ∧
      PureInputBasisMeasurementEq State.quaternionWeight U V ∧
      QuaternionOutputLeftPhaseEq (U * B) (V * B) := by
  exact ⟨QuaternionOutputLeftPhaseEq.refl U,
    QuaternionOutputLeftPhaseEq.symm hUV,
    QuaternionOutputLeftPhaseEq.trans hUV hVT,
    QuaternionOutputLeftPhaseEq.equivalence.1 U,
    QuaternionOutputLeftPhaseEq.of_exact hexact,
    QuaternionOutputLeftPhaseEq.basisMeasurementEq hUV,
    QuaternionOutputLeftPhaseEq.mulVec_eq hUV psi,
    QuaternionOutputLeftPhaseEq.pureInputBasisMeasurementEq hUV,
    QuaternionOutputLeftPhaseEq.mul_right B hUV⟩

/-- Complete named consumer for raw all-input projective action. -/
theorem quaternionRawProjectiveAction_api
    (U V T A B : Matrix Bool Bool ℍ[ℝ])
    (hUV : QuaternionRawProjectiveActionEq U V)
    (hVT : QuaternionRawProjectiveActionEq V T)
    (hexact : ExactOperatorEq U V) :
    QuaternionRawProjectiveActionEq U U ∧
      QuaternionRawProjectiveActionEq V U ∧
      QuaternionRawProjectiveActionEq U T ∧
      QuaternionRawProjectiveActionEq U U ∧
      QuaternionRawProjectiveActionEq U V ∧
      QuaternionProjectiveActionEq U V ∧
      (QuaternionRawProjectiveActionEq U V ↔
        QuaternionProjectiveActionEq U V) ∧
      QuaternionRawProjectiveActionEq (A * U) (A * V) ∧
      QuaternionRawProjectiveActionEq (U * B) (V * B) := by
  exact ⟨QuaternionRawProjectiveActionEq.refl U,
    QuaternionRawProjectiveActionEq.symm hUV,
    QuaternionRawProjectiveActionEq.trans hUV hVT,
    QuaternionRawProjectiveActionEq.equivalence.1 U,
    QuaternionRawProjectiveActionEq.of_exact hexact,
    QuaternionRawProjectiveActionEq.projectiveActionEq hUV,
    quaternionRawProjectiveActionEq_iff_projectiveActionEq,
    QuaternionRawProjectiveActionEq.mul_left A hUV,
    QuaternionRawProjectiveActionEq.mul_right B hUV⟩

/-- Complete named consumer for normalized pure-input projective action. -/
theorem quaternionProjectiveAction_api
    (U V T A P : Matrix Bool Bool ℍ[ℝ])
    (hUV : QuaternionProjectiveActionEq U V)
    (hVT : QuaternionProjectiveActionEq V T)
    (hexact : ExactOperatorEq U V)
    (hP : P ∈ unitary (Matrix Bool Bool ℍ[ℝ])) :
    QuaternionProjectiveActionEq U U ∧
      QuaternionProjectiveActionEq V U ∧
      QuaternionProjectiveActionEq U T ∧
      QuaternionProjectiveActionEq U U ∧
      QuaternionProjectiveActionEq U V ∧
      QuaternionRawProjectiveActionEq U V ∧
      PureInputBasisMeasurementEq State.quaternionWeight U V ∧
      QuaternionProjectiveActionEq (A * U) (A * V) ∧
      QuaternionProjectiveActionEq (U * P) (V * P) := by
  exact ⟨QuaternionProjectiveActionEq.refl U,
    QuaternionProjectiveActionEq.symm hUV,
    QuaternionProjectiveActionEq.trans hUV hVT,
    QuaternionProjectiveActionEq.equivalence.1 U,
    QuaternionProjectiveActionEq.of_exact hexact,
    QuaternionProjectiveActionEq.rawProjectiveActionEq hUV,
    QuaternionProjectiveActionEq.pureInputBasisMeasurementEq hUV,
    QuaternionProjectiveActionEq.mul_left A hUV,
    QuaternionProjectiveActionEq.mul_right_unitary P hP hUV⟩

/-! ## Complete consumers for chronological circuit wrappers -/

/-- Complete named consumer for central-sign circuit equality. -/
theorem quaternionCircuitCentralSign_api
    (C D E L : OrderedCircuit ℍ[ℝ] Bool)
    (hCD : QuaternionCircuitCentralSignEq C D)
    (hDE : QuaternionCircuitCentralSignEq D E)
    (hexact : ExactCircuitEq C D) :
    (QuaternionCircuitCentralSignEq C D ↔
        QuaternionCentralSignEq C.eval D.eval) ∧
      QuaternionCentralSignEq C.eval D.eval ∧
      QuaternionCircuitCentralSignEq C C ∧
      QuaternionCircuitCentralSignEq D C ∧
      QuaternionCircuitCentralSignEq C E ∧
      QuaternionCircuitCentralSignEq C C ∧
      QuaternionCircuitCentralSignEq C D ∧
      QuaternionCircuitCentralSignEq (C ++ D) (D ++ E) ∧
      QuaternionCircuitCentralSignEq (C ++ L) (D ++ L) ∧
      QuaternionCircuitCentralSignEq (L ++ C) (L ++ D) := by
  exact ⟨QuaternionCircuitCentralSignEq.iff_eval,
    QuaternionCircuitCentralSignEq.eval hCD,
    QuaternionCircuitCentralSignEq.refl C,
    QuaternionCircuitCentralSignEq.symm hCD,
    QuaternionCircuitCentralSignEq.trans hCD hDE,
    QuaternionCircuitCentralSignEq.equivalence.1 C,
    ExactCircuitEq.quaternionCentralSignEq hexact,
    QuaternionCircuitCentralSignEq.append hCD hDE,
    QuaternionCircuitCentralSignEq.append_same_later L hCD,
    QuaternionCircuitCentralSignEq.prepend_same_earlier L hCD⟩

/-- Complete named consumer for input-right-phase circuit equality. -/
theorem quaternionCircuitInputRightPhase_api
    (C D E L : OrderedCircuit ℍ[ℝ] Bool)
    (hCD : QuaternionCircuitInputRightPhaseEq C D)
    (hDE : QuaternionCircuitInputRightPhaseEq D E) :
    (QuaternionCircuitInputRightPhaseEq C D ↔
        QuaternionInputRightPhaseEq C.eval D.eval) ∧
      QuaternionInputRightPhaseEq C.eval D.eval ∧
      QuaternionCircuitInputRightPhaseEq C C ∧
      QuaternionCircuitInputRightPhaseEq D C ∧
      QuaternionCircuitInputRightPhaseEq C E ∧
      QuaternionCircuitInputRightPhaseEq C C ∧
      QuaternionCircuitInputRightPhaseEq (C ++ L) (D ++ L) := by
  exact ⟨QuaternionCircuitInputRightPhaseEq.iff_eval,
    QuaternionCircuitInputRightPhaseEq.eval hCD,
    QuaternionCircuitInputRightPhaseEq.refl C,
    QuaternionCircuitInputRightPhaseEq.symm hCD,
    QuaternionCircuitInputRightPhaseEq.trans hCD hDE,
    QuaternionCircuitInputRightPhaseEq.equivalence.1 C,
    QuaternionCircuitInputRightPhaseEq.append_same_later L hCD⟩

/-- Complete named consumer for output-left-phase circuit equality. -/
theorem quaternionCircuitOutputLeftPhase_api
    (C D E P : OrderedCircuit ℍ[ℝ] Bool)
    (hCD : QuaternionCircuitOutputLeftPhaseEq C D)
    (hDE : QuaternionCircuitOutputLeftPhaseEq D E) :
    (QuaternionCircuitOutputLeftPhaseEq C D ↔
        QuaternionOutputLeftPhaseEq C.eval D.eval) ∧
      QuaternionOutputLeftPhaseEq C.eval D.eval ∧
      QuaternionCircuitOutputLeftPhaseEq C C ∧
      QuaternionCircuitOutputLeftPhaseEq D C ∧
      QuaternionCircuitOutputLeftPhaseEq C E ∧
      QuaternionCircuitOutputLeftPhaseEq C C ∧
      QuaternionCircuitOutputLeftPhaseEq (P ++ C) (P ++ D) := by
  exact ⟨QuaternionCircuitOutputLeftPhaseEq.iff_eval,
    QuaternionCircuitOutputLeftPhaseEq.eval hCD,
    QuaternionCircuitOutputLeftPhaseEq.refl C,
    QuaternionCircuitOutputLeftPhaseEq.symm hCD,
    QuaternionCircuitOutputLeftPhaseEq.trans hCD hDE,
    QuaternionCircuitOutputLeftPhaseEq.equivalence.1 C,
    QuaternionCircuitOutputLeftPhaseEq.prepend_same_earlier P hCD⟩

/-- Complete named consumer for normalized-projective circuit equality. -/
theorem quaternionCircuitProjectiveAction_api
    (C D E L P : OrderedCircuit ℍ[ℝ] Bool)
    (hCD : QuaternionCircuitProjectiveActionEq C D)
    (hDE : QuaternionCircuitProjectiveActionEq D E)
    (hP : P.IsLocallyUnitary) :
    (QuaternionCircuitProjectiveActionEq C D ↔
        QuaternionProjectiveActionEq C.eval D.eval) ∧
      QuaternionProjectiveActionEq C.eval D.eval ∧
      QuaternionCircuitProjectiveActionEq C C ∧
      QuaternionCircuitProjectiveActionEq D C ∧
      QuaternionCircuitProjectiveActionEq C E ∧
      QuaternionCircuitProjectiveActionEq C C ∧
      QuaternionCircuitProjectiveActionEq (C ++ L) (D ++ L) ∧
      QuaternionCircuitProjectiveActionEq (P ++ C) (P ++ D) := by
  exact ⟨QuaternionCircuitProjectiveActionEq.iff_eval,
    QuaternionCircuitProjectiveActionEq.eval hCD,
    QuaternionCircuitProjectiveActionEq.refl C,
    QuaternionCircuitProjectiveActionEq.symm hCD,
    QuaternionCircuitProjectiveActionEq.trans hCD hDE,
    QuaternionCircuitProjectiveActionEq.equivalence.1 C,
    QuaternionCircuitProjectiveActionEq.append_same_later L hCD,
    QuaternionCircuitProjectiveActionEq.prepend_same_earlier_of_isLocallyUnitary
      P hP hCD⟩

/-! ## Dimension-two kernel and rank-one exception -/

/-- The raw and normalized kernel characterizations specialized to `Bool`. -/
theorem bool_projectiveKernel_api
    {U V : Matrix Bool Bool ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix Bool Bool ℍ[ℝ])) :
    (QuaternionRawProjectiveActionEq U V ↔
        QuaternionCentralSignEq U V) ∧
      (QuaternionProjectiveActionEq U V ↔
        QuaternionCentralSignEq U V) ∧
      (QuaternionRawProjectiveActionEq U V →
        QuaternionCentralSignEq U V) ∧
      (QuaternionProjectiveActionEq U V →
        QuaternionCentralSignEq U V) := by
  have hdim : 1 < Fintype.card Bool := by
    norm_num [Fintype.card_bool]
  exact ⟨quaternionRawProjectiveActionEq_iff_centralSignEq_of_unitary
      hdim hU,
    quaternionProjectiveActionEq_iff_centralSignEq_of_unitary hdim hU,
    QuaternionRawProjectiveActionEq.centralSignEq_of_unitary hdim hU,
    QuaternionProjectiveActionEq.centralSignEq_of_unitary hdim hU⟩

/-- Named consumer for the full rank-one scalar API and its explicit `j` exception. -/
theorem quaternionRankOne_api (q : ℍ[ℝ])
    (hq : _root_.Quaternion.normSq q = 1) :
    quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ]) ∧
      QuaternionRawProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar q) ∧
      QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar q) ∧
      (quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ]) ↔
        _root_.Quaternion.normSq q = 1) ∧
      (QuaternionRawProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
          (quaternionRankOneScalar q) ↔
        _root_.Quaternion.normSq q = 1) ∧
      (QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
          (quaternionRankOneScalar q) ↔
        _root_.Quaternion.normSq q = 1) ∧
      (QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
          (quaternionRankOneScalar q) ↔
        quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ])) ∧
      ¬ QuaternionCentralSignEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar Quaternion.j) ∧
      (quaternionRankOneScalar Quaternion.j ∈
          unitary (Matrix Unit Unit ℍ[ℝ]) ∧
        QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
          (quaternionRankOneScalar Quaternion.j) ∧
        ¬ QuaternionCentralSignEq (1 : Matrix Unit Unit ℍ[ℝ])
          (quaternionRankOneScalar Quaternion.j)) := by
  exact ⟨quaternionRankOneScalar_mem_unitary q hq,
    quaternionRankOneScalar_rawProjectiveActionEq q hq,
    quaternionRankOneScalar_projectiveActionEq q hq,
    quaternionRankOneScalar_mem_unitary_iff q,
    quaternionRankOneScalar_rawProjectiveActionEq_iff_normSq_eq_one q,
    quaternionRankOneScalar_projectiveActionEq_iff_normSq_eq_one q,
    quaternionRankOneScalar_projectiveActionEq_iff_mem_unitary q,
    quaternionRankOneJ_not_centralSignEq,
    quaternionRankOneJ_exception⟩

/-! ## Explicit side and central-sign diagnostics -/

/-- Identity with a column-dependent unit quaternion multiplied on the right. -/
def inputRightOrderTwist : Matrix Bool Bool ℍ[ℝ] :=
  fun y x ↦ (1 : Matrix Bool Bool ℍ[ℝ]) y x *
    if x then Quaternion.i else Quaternion.j

/-- The diagnostic column phases are witnessed in the required right order. -/
theorem inputRightOrderTwist_eq :
    QuaternionInputRightPhaseEq (1 : Matrix Bool Bool ℍ[ℝ])
      inputRightOrderTwist := by
  refine ⟨fun x ↦ if x then Quaternion.i else Quaternion.j, ?_, ?_⟩
  · intro x
    cases x <;> simp [QuaternionicComputing.Quaternion.normSq_i,
      QuaternionicComputing.Quaternion.normSq_j]
  · intro y x
    rfl

/-- Common later evolution retains the input phase on the right. -/
theorem inputRight_multiplicationOrder_test (A : Matrix Bool Bool ℍ[ℝ]) :
    QuaternionInputRightPhaseEq A (A * inputRightOrderTwist) := by
  simpa only [Matrix.mul_one] using
    QuaternionInputRightPhaseEq.mul_left A inputRightOrderTwist_eq

/-- Identity with a row-dependent unit quaternion multiplied on the left. -/
def outputLeftOrderTwist : Matrix Bool Bool ℍ[ℝ] :=
  fun y x ↦ (if y then Quaternion.i else Quaternion.j) *
    (1 : Matrix Bool Bool ℍ[ℝ]) y x

/-- The diagnostic row phases are witnessed in the required left order. -/
theorem outputLeftOrderTwist_eq :
    QuaternionOutputLeftPhaseEq (1 : Matrix Bool Bool ℍ[ℝ])
      outputLeftOrderTwist := by
  refine ⟨fun y ↦ if y then Quaternion.i else Quaternion.j, ?_, ?_⟩
  · intro y
    cases y <;> simp [QuaternionicComputing.Quaternion.normSq_i,
      QuaternionicComputing.Quaternion.normSq_j]
  · intro y x
    rfl

/-- Common earlier evolution retains the output phase on the left. -/
theorem outputLeft_multiplicationOrder_test (B : Matrix Bool Bool ℍ[ℝ]) :
    QuaternionOutputLeftPhaseEq B (outputLeftOrderTwist * B) := by
  simpa only [Matrix.one_mul] using
    QuaternionOutputLeftPhaseEq.mul_right B outputLeftOrderTwist_eq

/-- The central sign `-1` is nontrivial but is admitted by central-sign equality. -/
theorem central_negOne_example :
    QuaternionCentralSignEq (1 : Matrix Bool Bool ℍ[ℝ])
        ((-1 : ℝ) • (1 : Matrix Bool Bool ℍ[ℝ])) ∧
      ¬ ExactOperatorEq (1 : Matrix Bool Bool ℍ[ℝ])
        ((-1 : ℝ) • (1 : Matrix Bool Bool ℍ[ℝ])) := by
  constructor
  · exact ⟨-1, by norm_num, rfl⟩
  · intro h
    have he := congrFun (congrFun h false) false
    have hre := congrArg (fun q : ℍ[ℝ] ↦ q.re) he
    norm_num at hre

/-! ## Representative axiom audit -/

#print axioms quaternionCentralSign_api
#print axioms quaternionProjectiveAction_api
#print axioms quaternionCircuitProjectiveAction_api
#print axioms bool_projectiveKernel_api
#print axioms quaternionRankOne_api
#print axioms inputRight_multiplicationOrder_test
#print axioms outputLeft_multiplicationOrder_test
#print axioms central_negOne_example

end QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit
