module

public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit

/-!
# Real and complex operator-phase audit

This non-root diagnostic leaf exercises every stable declaration exported by
`ComplexReal` and `ComplexRealCircuit`.  Its strictness witnesses use the
unitary rational rotation with entries `3/5`, `4/5`, `-4/5`, and `3/5`.
Consequently the failed converses and input/output-phase incomparability are
not artifacts of singular or unnormalised examples.

The zero-wire circuit examples separately certify nontrivial real `-1` and
complex `I` global phases through the chronological evaluator.  This file is
intentionally excluded from the public root.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

/-! ## Complete consumers for the operator-level API -/

/-- Complete named consumer for the real global-sign operator API. -/
theorem realGlobalSign_api (U V T : Matrix Bool Bool ℝ)
    (hUV : RealGlobalSignEq U V) (hVT : RealGlobalSignEq V T)
    (hexact : ExactOperatorEq U V)
    (hU : U ∈ unitary (Matrix Bool Bool ℝ)) :
    RealGlobalSignEq U U ∧
      RealGlobalSignEq V U ∧
      RealGlobalSignEq U T ∧
      RealGlobalSignEq U U ∧
      RealGlobalSignEq U V ∧
      RealInputBasisSignEq U V ∧
      RealOutputBasisSignEq U V ∧
      RealProjectiveActionEq U V ∧
      V ∈ unitary (Matrix Bool Bool ℝ) ∧
      (U ∈ unitary (Matrix Bool Bool ℝ) ↔
        V ∈ unitary (Matrix Bool Bool ℝ)) ∧
      RealGlobalSignEq (U * U) (V * V) := by
  exact ⟨RealGlobalSignEq.refl U,
    RealGlobalSignEq.symm hUV,
    RealGlobalSignEq.trans hUV hVT,
    RealGlobalSignEq.equivalence.1 U,
    RealGlobalSignEq.of_exact hexact,
    RealGlobalSignEq.inputBasisSignEq hUV,
    RealGlobalSignEq.outputBasisSignEq hUV,
    RealGlobalSignEq.projectiveActionEq hUV,
    RealGlobalSignEq.mem_unitary hUV hU,
    RealGlobalSignEq.mem_unitary_iff hUV,
    RealGlobalSignEq.mul hUV hUV⟩

/-- Complete named consumer for the complex global-phase operator API. -/
theorem complexGlobalPhase_api (U V T : Matrix Bool Bool ℂ)
    (hUV : ComplexGlobalPhaseEq U V) (hVT : ComplexGlobalPhaseEq V T)
    (hexact : ExactOperatorEq U V)
    (hU : U ∈ unitary (Matrix Bool Bool ℂ)) :
    ComplexGlobalPhaseEq U U ∧
      ComplexGlobalPhaseEq V U ∧
      ComplexGlobalPhaseEq U T ∧
      ComplexGlobalPhaseEq U U ∧
      ComplexGlobalPhaseEq U V ∧
      ComplexInputBasisPhaseEq U V ∧
      ComplexOutputBasisPhaseEq U V ∧
      ComplexProjectiveActionEq U V ∧
      V ∈ unitary (Matrix Bool Bool ℂ) ∧
      (U ∈ unitary (Matrix Bool Bool ℂ) ↔
        V ∈ unitary (Matrix Bool Bool ℂ)) ∧
      ComplexGlobalPhaseEq (U * U) (V * V) := by
  exact ⟨ComplexGlobalPhaseEq.refl U,
    ComplexGlobalPhaseEq.symm hUV,
    ComplexGlobalPhaseEq.trans hUV hVT,
    ComplexGlobalPhaseEq.equivalence.1 U,
    ComplexGlobalPhaseEq.of_exact hexact,
    ComplexGlobalPhaseEq.inputBasisPhaseEq hUV,
    ComplexGlobalPhaseEq.outputBasisPhaseEq hUV,
    ComplexGlobalPhaseEq.projectiveActionEq hUV,
    ComplexGlobalPhaseEq.mem_unitary hUV hU,
    ComplexGlobalPhaseEq.mem_unitary_iff hUV,
    ComplexGlobalPhaseEq.mul hUV hUV⟩

/-- Complete named consumer for real input-column signs. -/
theorem realInputBasisSign_api (U V T A : Matrix Bool Bool ℝ)
    (hUV : RealInputBasisSignEq U V) (hVT : RealInputBasisSignEq V T)
    (hexact : ExactOperatorEq U V) :
    RealInputBasisSignEq U U ∧
      RealInputBasisSignEq V U ∧
      RealInputBasisSignEq U T ∧
      RealInputBasisSignEq U U ∧
      RealInputBasisSignEq U V ∧
      BasisMeasurementEq State.realWeight U V ∧
      RealInputBasisSignEq (A * U) (A * V) := by
  exact ⟨RealInputBasisSignEq.refl U,
    RealInputBasisSignEq.symm hUV,
    RealInputBasisSignEq.trans hUV hVT,
    RealInputBasisSignEq.equivalence.1 U,
    RealInputBasisSignEq.of_exact hexact,
    RealInputBasisSignEq.basisMeasurementEq hUV,
    RealInputBasisSignEq.mul_left A hUV⟩

/-- Complete named consumer for complex input-column phases. -/
theorem complexInputBasisPhase_api (U V T A : Matrix Bool Bool ℂ)
    (hUV : ComplexInputBasisPhaseEq U V)
    (hVT : ComplexInputBasisPhaseEq V T)
    (hexact : ExactOperatorEq U V) :
    ComplexInputBasisPhaseEq U U ∧
      ComplexInputBasisPhaseEq V U ∧
      ComplexInputBasisPhaseEq U T ∧
      ComplexInputBasisPhaseEq U U ∧
      ComplexInputBasisPhaseEq U V ∧
      BasisMeasurementEq State.complexWeight U V ∧
      ComplexInputBasisPhaseEq (A * U) (A * V) := by
  exact ⟨ComplexInputBasisPhaseEq.refl U,
    ComplexInputBasisPhaseEq.symm hUV,
    ComplexInputBasisPhaseEq.trans hUV hVT,
    ComplexInputBasisPhaseEq.equivalence.1 U,
    ComplexInputBasisPhaseEq.of_exact hexact,
    ComplexInputBasisPhaseEq.basisMeasurementEq hUV,
    ComplexInputBasisPhaseEq.mul_left A hUV⟩

/-- Complete named consumer for real output-row signs. -/
theorem realOutputBasisSign_api (U V T B : Matrix Bool Bool ℝ)
    (psi : Bool → ℝ) (hUV : RealOutputBasisSignEq U V)
    (hVT : RealOutputBasisSignEq V T) (hexact : ExactOperatorEq U V) :
    RealOutputBasisSignEq U U ∧
      RealOutputBasisSignEq V U ∧
      RealOutputBasisSignEq U T ∧
      RealOutputBasisSignEq U U ∧
      RealOutputBasisSignEq U V ∧
      BasisMeasurementEq State.realWeight U V ∧
      (∃ s : Bool → ℝ, (∀ y, s y * s y = 1) ∧
        V *ᵥ psi = fun y ↦ s y * (U *ᵥ psi) y) ∧
      PureInputBasisMeasurementEq State.realWeight U V ∧
      RealOutputBasisSignEq (U * B) (V * B) := by
  exact ⟨RealOutputBasisSignEq.refl U,
    RealOutputBasisSignEq.symm hUV,
    RealOutputBasisSignEq.trans hUV hVT,
    RealOutputBasisSignEq.equivalence.1 U,
    RealOutputBasisSignEq.of_exact hexact,
    RealOutputBasisSignEq.basisMeasurementEq hUV,
    RealOutputBasisSignEq.mulVec_eq hUV psi,
    RealOutputBasisSignEq.pureInputBasisMeasurementEq hUV,
    RealOutputBasisSignEq.mul_right B hUV⟩

/-- Complete named consumer for complex output-row phases. -/
theorem complexOutputBasisPhase_api (U V T B : Matrix Bool Bool ℂ)
    (psi : Bool → ℂ) (hUV : ComplexOutputBasisPhaseEq U V)
    (hVT : ComplexOutputBasisPhaseEq V T)
    (hexact : ExactOperatorEq U V) :
    ComplexOutputBasisPhaseEq U U ∧
      ComplexOutputBasisPhaseEq V U ∧
      ComplexOutputBasisPhaseEq U T ∧
      ComplexOutputBasisPhaseEq U U ∧
      ComplexOutputBasisPhaseEq U V ∧
      BasisMeasurementEq State.complexWeight U V ∧
      (∃ eta : Bool → ℂ, (∀ y, Complex.normSq (eta y) = 1) ∧
        V *ᵥ psi = fun y ↦ eta y * (U *ᵥ psi) y) ∧
      PureInputBasisMeasurementEq State.complexWeight U V ∧
      ComplexOutputBasisPhaseEq (U * B) (V * B) := by
  exact ⟨ComplexOutputBasisPhaseEq.refl U,
    ComplexOutputBasisPhaseEq.symm hUV,
    ComplexOutputBasisPhaseEq.trans hUV hVT,
    ComplexOutputBasisPhaseEq.equivalence.1 U,
    ComplexOutputBasisPhaseEq.of_exact hexact,
    ComplexOutputBasisPhaseEq.basisMeasurementEq hUV,
    ComplexOutputBasisPhaseEq.mulVec_eq hUV psi,
    ComplexOutputBasisPhaseEq.pureInputBasisMeasurementEq hUV,
    ComplexOutputBasisPhaseEq.mul_right B hUV⟩

/-- Complete named consumer for real projective action. -/
theorem realProjectiveAction_api (U V T A P : Matrix Bool Bool ℝ)
    (hUV : RealProjectiveActionEq U V)
    (hVT : RealProjectiveActionEq V T) (hexact : ExactOperatorEq U V)
    (hP : P ∈ unitary (Matrix Bool Bool ℝ)) :
    RealProjectiveActionEq U U ∧
      RealProjectiveActionEq V U ∧
      RealProjectiveActionEq U T ∧
      RealProjectiveActionEq U U ∧
      RealProjectiveActionEq U V ∧
      PureInputBasisMeasurementEq State.realWeight U V ∧
      RealProjectiveActionEq (A * U) (A * V) ∧
      RealProjectiveActionEq (U * P) (V * P) := by
  exact ⟨RealProjectiveActionEq.refl U,
    RealProjectiveActionEq.symm hUV,
    RealProjectiveActionEq.trans hUV hVT,
    RealProjectiveActionEq.equivalence.1 U,
    RealProjectiveActionEq.of_exact hexact,
    RealProjectiveActionEq.pureInputBasisMeasurementEq hUV,
    RealProjectiveActionEq.mul_left A hUV,
    RealProjectiveActionEq.mul_right_unitary P hP hUV⟩

/-- Complete named consumer for complex projective action. -/
theorem complexProjectiveAction_api (U V T A P : Matrix Bool Bool ℂ)
    (hUV : ComplexProjectiveActionEq U V)
    (hVT : ComplexProjectiveActionEq V T) (hexact : ExactOperatorEq U V)
    (hP : P ∈ unitary (Matrix Bool Bool ℂ)) :
    ComplexProjectiveActionEq U U ∧
      ComplexProjectiveActionEq V U ∧
      ComplexProjectiveActionEq U T ∧
      ComplexProjectiveActionEq U U ∧
      ComplexProjectiveActionEq U V ∧
      PureInputBasisMeasurementEq State.complexWeight U V ∧
      ComplexProjectiveActionEq (A * U) (A * V) ∧
      ComplexProjectiveActionEq (U * P) (V * P) := by
  exact ⟨ComplexProjectiveActionEq.refl U,
    ComplexProjectiveActionEq.symm hUV,
    ComplexProjectiveActionEq.trans hUV hVT,
    ComplexProjectiveActionEq.equivalence.1 U,
    ComplexProjectiveActionEq.of_exact hexact,
    ComplexProjectiveActionEq.pureInputBasisMeasurementEq hUV,
    ComplexProjectiveActionEq.mul_left A hUV,
    ComplexProjectiveActionEq.mul_right_unitary P hP hUV⟩

/-! ## Complete consumers for chronological circuit wrappers -/

/-- Complete named consumer for real circuit global signs. -/
theorem realCircuitGlobalSign_api
    (C D E L : OrderedCircuit ℝ Bool)
    (hCD : RealCircuitGlobalSignEq C D)
    (hDE : RealCircuitGlobalSignEq D E) (hexact : ExactCircuitEq C D) :
    (RealCircuitGlobalSignEq C D ↔ RealGlobalSignEq C.eval D.eval) ∧
      RealGlobalSignEq C.eval D.eval ∧
      RealCircuitGlobalSignEq C C ∧
      RealCircuitGlobalSignEq D C ∧
      RealCircuitGlobalSignEq C E ∧
      RealCircuitGlobalSignEq C C ∧
      RealCircuitGlobalSignEq C D ∧
      RealCircuitGlobalSignEq (C ++ D) (D ++ E) ∧
      RealCircuitGlobalSignEq (C ++ L) (D ++ L) ∧
      RealCircuitGlobalSignEq (L ++ C) (L ++ D) := by
  exact ⟨RealCircuitGlobalSignEq.iff_eval,
    RealCircuitGlobalSignEq.eval hCD,
    RealCircuitGlobalSignEq.refl C,
    RealCircuitGlobalSignEq.symm hCD,
    RealCircuitGlobalSignEq.trans hCD hDE,
    RealCircuitGlobalSignEq.equivalence.1 C,
    ExactCircuitEq.realGlobalSignEq hexact,
    RealCircuitGlobalSignEq.append hCD hDE,
    RealCircuitGlobalSignEq.append_same_later L hCD,
    RealCircuitGlobalSignEq.prepend_same_earlier L hCD⟩

/-- Complete named consumer for complex circuit global phases. -/
theorem complexCircuitGlobalPhase_api
    (C D E L : OrderedCircuit ℂ Bool)
    (hCD : ComplexCircuitGlobalPhaseEq C D)
    (hDE : ComplexCircuitGlobalPhaseEq D E) (hexact : ExactCircuitEq C D) :
    (ComplexCircuitGlobalPhaseEq C D ↔
        ComplexGlobalPhaseEq C.eval D.eval) ∧
      ComplexGlobalPhaseEq C.eval D.eval ∧
      ComplexCircuitGlobalPhaseEq C C ∧
      ComplexCircuitGlobalPhaseEq D C ∧
      ComplexCircuitGlobalPhaseEq C E ∧
      ComplexCircuitGlobalPhaseEq C C ∧
      ComplexCircuitGlobalPhaseEq C D ∧
      ComplexCircuitGlobalPhaseEq (C ++ D) (D ++ E) ∧
      ComplexCircuitGlobalPhaseEq (C ++ L) (D ++ L) ∧
      ComplexCircuitGlobalPhaseEq (L ++ C) (L ++ D) := by
  exact ⟨ComplexCircuitGlobalPhaseEq.iff_eval,
    ComplexCircuitGlobalPhaseEq.eval hCD,
    ComplexCircuitGlobalPhaseEq.refl C,
    ComplexCircuitGlobalPhaseEq.symm hCD,
    ComplexCircuitGlobalPhaseEq.trans hCD hDE,
    ComplexCircuitGlobalPhaseEq.equivalence.1 C,
    ExactCircuitEq.complexGlobalPhaseEq hexact,
    ComplexCircuitGlobalPhaseEq.append hCD hDE,
    ComplexCircuitGlobalPhaseEq.append_same_later L hCD,
    ComplexCircuitGlobalPhaseEq.prepend_same_earlier L hCD⟩

/-- Complete named consumer for real circuit input-column signs. -/
theorem realCircuitInputBasisSign_api
    (C D E L : OrderedCircuit ℝ Bool)
    (hCD : RealCircuitInputBasisSignEq C D)
    (hDE : RealCircuitInputBasisSignEq D E) :
    (RealCircuitInputBasisSignEq C D ↔
        RealInputBasisSignEq C.eval D.eval) ∧
      RealInputBasisSignEq C.eval D.eval ∧
      RealCircuitInputBasisSignEq C C ∧
      RealCircuitInputBasisSignEq D C ∧
      RealCircuitInputBasisSignEq C E ∧
      RealCircuitInputBasisSignEq C C ∧
      RealCircuitInputBasisSignEq (C ++ L) (D ++ L) := by
  exact ⟨RealCircuitInputBasisSignEq.iff_eval,
    RealCircuitInputBasisSignEq.eval hCD,
    RealCircuitInputBasisSignEq.refl C,
    RealCircuitInputBasisSignEq.symm hCD,
    RealCircuitInputBasisSignEq.trans hCD hDE,
    RealCircuitInputBasisSignEq.equivalence.1 C,
    RealCircuitInputBasisSignEq.append_same_later L hCD⟩

/-- Complete named consumer for complex circuit input-column phases. -/
theorem complexCircuitInputBasisPhase_api
    (C D E L : OrderedCircuit ℂ Bool)
    (hCD : ComplexCircuitInputBasisPhaseEq C D)
    (hDE : ComplexCircuitInputBasisPhaseEq D E) :
    (ComplexCircuitInputBasisPhaseEq C D ↔
        ComplexInputBasisPhaseEq C.eval D.eval) ∧
      ComplexInputBasisPhaseEq C.eval D.eval ∧
      ComplexCircuitInputBasisPhaseEq C C ∧
      ComplexCircuitInputBasisPhaseEq D C ∧
      ComplexCircuitInputBasisPhaseEq C E ∧
      ComplexCircuitInputBasisPhaseEq C C ∧
      ComplexCircuitInputBasisPhaseEq (C ++ L) (D ++ L) := by
  exact ⟨ComplexCircuitInputBasisPhaseEq.iff_eval,
    ComplexCircuitInputBasisPhaseEq.eval hCD,
    ComplexCircuitInputBasisPhaseEq.refl C,
    ComplexCircuitInputBasisPhaseEq.symm hCD,
    ComplexCircuitInputBasisPhaseEq.trans hCD hDE,
    ComplexCircuitInputBasisPhaseEq.equivalence.1 C,
    ComplexCircuitInputBasisPhaseEq.append_same_later L hCD⟩

/-- Complete named consumer for real circuit output-row signs. -/
theorem realCircuitOutputBasisSign_api
    (C D E P : OrderedCircuit ℝ Bool)
    (hCD : RealCircuitOutputBasisSignEq C D)
    (hDE : RealCircuitOutputBasisSignEq D E) :
    (RealCircuitOutputBasisSignEq C D ↔
        RealOutputBasisSignEq C.eval D.eval) ∧
      RealOutputBasisSignEq C.eval D.eval ∧
      RealCircuitOutputBasisSignEq C C ∧
      RealCircuitOutputBasisSignEq D C ∧
      RealCircuitOutputBasisSignEq C E ∧
      RealCircuitOutputBasisSignEq C C ∧
      RealCircuitOutputBasisSignEq (P ++ C) (P ++ D) := by
  exact ⟨RealCircuitOutputBasisSignEq.iff_eval,
    RealCircuitOutputBasisSignEq.eval hCD,
    RealCircuitOutputBasisSignEq.refl C,
    RealCircuitOutputBasisSignEq.symm hCD,
    RealCircuitOutputBasisSignEq.trans hCD hDE,
    RealCircuitOutputBasisSignEq.equivalence.1 C,
    RealCircuitOutputBasisSignEq.prepend_same_earlier P hCD⟩

/-- Complete named consumer for complex circuit output-row phases. -/
theorem complexCircuitOutputBasisPhase_api
    (C D E P : OrderedCircuit ℂ Bool)
    (hCD : ComplexCircuitOutputBasisPhaseEq C D)
    (hDE : ComplexCircuitOutputBasisPhaseEq D E) :
    (ComplexCircuitOutputBasisPhaseEq C D ↔
        ComplexOutputBasisPhaseEq C.eval D.eval) ∧
      ComplexOutputBasisPhaseEq C.eval D.eval ∧
      ComplexCircuitOutputBasisPhaseEq C C ∧
      ComplexCircuitOutputBasisPhaseEq D C ∧
      ComplexCircuitOutputBasisPhaseEq C E ∧
      ComplexCircuitOutputBasisPhaseEq C C ∧
      ComplexCircuitOutputBasisPhaseEq (P ++ C) (P ++ D) := by
  exact ⟨ComplexCircuitOutputBasisPhaseEq.iff_eval,
    ComplexCircuitOutputBasisPhaseEq.eval hCD,
    ComplexCircuitOutputBasisPhaseEq.refl C,
    ComplexCircuitOutputBasisPhaseEq.symm hCD,
    ComplexCircuitOutputBasisPhaseEq.trans hCD hDE,
    ComplexCircuitOutputBasisPhaseEq.equivalence.1 C,
    ComplexCircuitOutputBasisPhaseEq.prepend_same_earlier P hCD⟩

/-- Complete named consumer for real circuit projective action. -/
theorem realCircuitProjectiveAction_api
    (C D F L E : OrderedCircuit ℝ Bool)
    (hCD : RealCircuitProjectiveActionEq C D)
    (hDF : RealCircuitProjectiveActionEq D F)
    (hE : E.IsLocallyUnitary) :
    (RealCircuitProjectiveActionEq C D ↔
        RealProjectiveActionEq C.eval D.eval) ∧
      RealProjectiveActionEq C.eval D.eval ∧
      RealCircuitProjectiveActionEq C C ∧
      RealCircuitProjectiveActionEq D C ∧
      RealCircuitProjectiveActionEq C F ∧
      RealCircuitProjectiveActionEq C C ∧
      RealCircuitProjectiveActionEq (C ++ L) (D ++ L) ∧
      RealCircuitProjectiveActionEq (E ++ C) (E ++ D) := by
  exact ⟨RealCircuitProjectiveActionEq.iff_eval,
    RealCircuitProjectiveActionEq.eval hCD,
    RealCircuitProjectiveActionEq.refl C,
    RealCircuitProjectiveActionEq.symm hCD,
    RealCircuitProjectiveActionEq.trans hCD hDF,
    RealCircuitProjectiveActionEq.equivalence.1 C,
    RealCircuitProjectiveActionEq.append_same_later L hCD,
    RealCircuitProjectiveActionEq.prepend_same_earlier_of_isLocallyUnitary
      E hE hCD⟩

/-- Complete named consumer for complex circuit projective action. -/
theorem complexCircuitProjectiveAction_api
    (C D F L E : OrderedCircuit ℂ Bool)
    (hCD : ComplexCircuitProjectiveActionEq C D)
    (hDF : ComplexCircuitProjectiveActionEq D F)
    (hE : E.IsLocallyUnitary) :
    (ComplexCircuitProjectiveActionEq C D ↔
        ComplexProjectiveActionEq C.eval D.eval) ∧
      ComplexProjectiveActionEq C.eval D.eval ∧
      ComplexCircuitProjectiveActionEq C C ∧
      ComplexCircuitProjectiveActionEq D C ∧
      ComplexCircuitProjectiveActionEq C F ∧
      ComplexCircuitProjectiveActionEq C C ∧
      ComplexCircuitProjectiveActionEq (C ++ L) (D ++ L) ∧
      ComplexCircuitProjectiveActionEq (E ++ C) (E ++ D) := by
  exact ⟨ComplexCircuitProjectiveActionEq.iff_eval,
    ComplexCircuitProjectiveActionEq.eval hCD,
    ComplexCircuitProjectiveActionEq.refl C,
    ComplexCircuitProjectiveActionEq.symm hCD,
    ComplexCircuitProjectiveActionEq.trans hCD hDF,
    ComplexCircuitProjectiveActionEq.equivalence.1 C,
    ComplexCircuitProjectiveActionEq.append_same_later L hCD,
    ComplexCircuitProjectiveActionEq.prepend_same_earlier_of_isLocallyUnitary
      E hE hCD⟩

/-! ## Rational unitary rotation witnesses -/

/-- The real rational rotation `[[3/5,4/5],[-4/5,3/5]]`. -/
def realRotation : Matrix Bool Bool ℝ
  | false, false => 3 / 5
  | false, true => 4 / 5
  | true, false => -4 / 5
  | true, true => 3 / 5

/-- The rational real rotation is exactly unitary. -/
theorem realRotation_mem_unitary :
    realRotation ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, realRotation, Fintype.univ_bool]

/-- The same rational rotation regarded as a complex matrix. -/
def complexRotation : Matrix Bool Bool ℂ :=
  fun y x ↦ realRotation y x

/-- The rational complex rotation is exactly unitary. -/
theorem complexRotation_mem_unitary :
    complexRotation ∈ unitary (Matrix Bool Bool ℂ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, complexRotation, realRotation,
      Fintype.univ_bool]

/-- Negating one real input column. -/
def realInputTwist : Matrix Bool Bool ℝ :=
  fun y x ↦ realRotation y x * if x then -1 else 1

/-- Negating one real output row. -/
def realOutputTwist : Matrix Bool Bool ℝ :=
  fun y x ↦ (if y then -1 else 1) * realRotation y x

/-- The real input-column twist remains unitary. -/
theorem realInputTwist_mem_unitary :
    realInputTwist ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, realInputTwist, realRotation,
      Fintype.univ_bool]

/-- The real output-row twist remains unitary. -/
theorem realOutputTwist_mem_unitary :
    realOutputTwist ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, realOutputTwist, realRotation,
      Fintype.univ_bool]

/-- Multiplying one complex input column by `I`. -/
def complexInputTwist : Matrix Bool Bool ℂ :=
  fun y x ↦ complexRotation y x * if x then Complex.I else 1

/-- Multiplying one complex output row by `I`. -/
def complexOutputTwist : Matrix Bool Bool ℂ :=
  fun y x ↦ (if y then Complex.I else 1) * complexRotation y x

/-- The complex input-column twist remains unitary. -/
theorem complexInputTwist_mem_unitary :
    complexInputTwist ∈ unitary (Matrix Bool Bool ℂ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, complexInputTwist, complexRotation,
      realRotation, Fintype.univ_bool, Complex.conj_I, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_mul_I]

/-- The complex output-row twist remains unitary. -/
theorem complexOutputTwist_mem_unitary :
    complexOutputTwist ∈ unitary (Matrix Bool Bool ℂ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, complexOutputTwist, complexRotation,
      realRotation, Fintype.univ_bool, Complex.conj_I, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_mul_I]

/-- A normalized real input exposing input-column interference. -/
def realThreeFour : State.RealState Bool :=
  ⟨fun x ↦ if x then (4 / 5 : ℝ) else 3 / 5, by
    norm_num [State.realTotalWeight, State.totalWeight, State.basisWeight,
      State.realWeight, Fintype.univ_bool]⟩

/-- The same normalized input over the complex scalars. -/
def complexThreeFour : State.ComplexState Bool :=
  ⟨fun x ↦ if x then (4 / 5 : ℂ) else 3 / 5, by
    norm_num [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, Complex.normSq_apply, Fintype.univ_bool]⟩

/-- A normalized real basis input exposing output-row phase inconsistency. -/
def realBasisFalse : State.RealState Bool :=
  ⟨fun x ↦ if x then 0 else 1, by
    simp [State.realTotalWeight, State.totalWeight, State.basisWeight,
      State.realWeight, Fintype.univ_bool]⟩

/-- The corresponding normalized complex basis input. -/
def complexBasisFalse : State.ComplexState Bool :=
  ⟨fun x ↦ if x then 0 else 1, by
    simp [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, Fintype.univ_bool]⟩

/-! ### Real strictness and incomparability -/

theorem realRotation_inputTwist :
    RealInputBasisSignEq realRotation realInputTwist := by
  refine ⟨fun x ↦ if x then -1 else 1, ?_, ?_⟩
  · intro x
    cases x <;> norm_num
  · intro y x
    rfl

theorem realInputTwist_not_global :
    ¬ RealGlobalSignEq realRotation realInputTwist := by
  rintro ⟨s, _, h⟩
  have h0 := congrFun (congrFun h false) false
  have h1 := congrFun (congrFun h false) true
  norm_num [realRotation, realInputTwist] at h0 h1
  linarith

theorem realInputTwist_not_output :
    ¬ RealOutputBasisSignEq realRotation realInputTwist := by
  rintro ⟨s, _, h⟩
  have h0 := h false false
  have h1 := h false true
  norm_num [realRotation, realInputTwist] at h0 h1
  linarith

theorem realInputTwist_not_pureInputBasisMeasurementEq :
    ¬ PureInputBasisMeasurementEq State.realWeight
      realRotation realInputTwist := by
  intro h
  have hw := h realThreeFour false
  norm_num [OutputWeightEqAt, BasisWeightEq, State.basisWeight,
    State.realWeight, Matrix.mulVec, dotProduct, Fintype.univ_bool,
    realRotation, realInputTwist, realThreeFour] at hw

theorem realRotation_outputTwist :
    RealOutputBasisSignEq realRotation realOutputTwist := by
  refine ⟨fun y ↦ if y then -1 else 1, ?_, ?_⟩
  · intro y
    cases y <;> norm_num
  · intro y x
    rfl

theorem realOutputTwist_not_global :
    ¬ RealGlobalSignEq realRotation realOutputTwist := by
  rintro ⟨s, _, h⟩
  have h0 := congrFun (congrFun h false) false
  have h1 := congrFun (congrFun h true) false
  norm_num [realRotation, realOutputTwist] at h0 h1
  linarith

theorem realOutputTwist_not_input :
    ¬ RealInputBasisSignEq realRotation realOutputTwist := by
  rintro ⟨s, _, h⟩
  have h0 := h false false
  have h1 := h true false
  norm_num [realRotation, realOutputTwist] at h0 h1
  linarith

theorem realOutputTwist_pureInputBasisMeasurementEq :
    PureInputBasisMeasurementEq State.realWeight
      realRotation realOutputTwist :=
  realRotation_outputTwist.pureInputBasisMeasurementEq

theorem realOutputTwist_not_projectiveActionEq :
    ¬ RealProjectiveActionEq realRotation realOutputTwist := by
  intro h
  rcases h realBasisFalse with ⟨s, _, hout⟩
  have h0 := congrFun hout false
  have h1 := congrFun hout true
  norm_num [Matrix.mulVec, dotProduct, Fintype.univ_bool, realRotation,
    realOutputTwist, realBasisFalse] at h0 h1
  linarith

/-- A nontrivial global real sign is strictly weaker than exact equality. -/
def realNegRotation : Matrix Bool Bool ℝ :=
  (-1 : ℝ) • realRotation

theorem realRotation_neg_global :
    RealGlobalSignEq realRotation realNegRotation :=
  ⟨-1, by norm_num, rfl⟩

theorem realRotation_neg_not_exact :
    ¬ ExactOperatorEq realRotation realNegRotation := by
  intro h
  have h00 := congrFun (congrFun h false) false
  norm_num [realRotation, realNegRotation] at h00

theorem realNegRotation_mem_unitary :
    realNegRotation ∈ unitary (Matrix Bool Bool ℝ) :=
  realRotation_neg_global.mem_unitary realRotation_mem_unitary

/-! ### Complex strictness and incomparability -/

theorem complexRotation_inputTwist :
    ComplexInputBasisPhaseEq complexRotation complexInputTwist := by
  refine ⟨fun x ↦ if x then Complex.I else 1, ?_, ?_⟩
  · intro x
    cases x <;> simp [Complex.normSq_I]
  · intro y x
    rfl

theorem complexInputTwist_not_global :
    ¬ ComplexGlobalPhaseEq complexRotation complexInputTwist := by
  rintro ⟨eta, _, h⟩
  have h0 := congrFun (congrFun h false) false
  have h1 := congrFun (congrFun h false) true
  have h0re := congrArg Complex.re h0
  have h0im := congrArg Complex.im h0
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  norm_num [complexRotation, realRotation, complexInputTwist] at
    h0re h0im h1re h1im
  linarith

theorem complexInputTwist_not_output :
    ¬ ComplexOutputBasisPhaseEq complexRotation complexInputTwist := by
  rintro ⟨eta, _, h⟩
  have h0 := h false false
  have h1 := h false true
  have h0re := congrArg Complex.re h0
  have h0im := congrArg Complex.im h0
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  norm_num [complexRotation, realRotation, complexInputTwist] at
    h0re h0im h1re h1im
  linarith

theorem complexInputTwist_not_pureInputBasisMeasurementEq :
    ¬ PureInputBasisMeasurementEq State.complexWeight
      complexRotation complexInputTwist := by
  intro h
  have hw := h complexThreeFour false
  norm_num [OutputWeightEqAt, BasisWeightEq, State.basisWeight,
    State.complexWeight, Complex.normSq_apply, Matrix.mulVec, dotProduct,
    Fintype.univ_bool, complexRotation, realRotation, complexInputTwist,
    complexThreeFour] at hw

theorem complexRotation_outputTwist :
    ComplexOutputBasisPhaseEq complexRotation complexOutputTwist := by
  refine ⟨fun y ↦ if y then Complex.I else 1, ?_, ?_⟩
  · intro y
    cases y <;> simp [Complex.normSq_I]
  · intro y x
    rfl

theorem complexOutputTwist_not_global :
    ¬ ComplexGlobalPhaseEq complexRotation complexOutputTwist := by
  rintro ⟨eta, _, h⟩
  have h0 := congrFun (congrFun h false) false
  have h1 := congrFun (congrFun h true) false
  have h0re := congrArg Complex.re h0
  have h0im := congrArg Complex.im h0
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  norm_num [complexRotation, realRotation, complexOutputTwist] at
    h0re h0im h1re h1im
  linarith

theorem complexOutputTwist_not_input :
    ¬ ComplexInputBasisPhaseEq complexRotation complexOutputTwist := by
  rintro ⟨eta, _, h⟩
  have h0 := h false false
  have h1 := h true false
  have h0re := congrArg Complex.re h0
  have h0im := congrArg Complex.im h0
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  norm_num [complexRotation, realRotation, complexOutputTwist] at
    h0re h0im h1re h1im
  linarith

theorem complexOutputTwist_pureInputBasisMeasurementEq :
    PureInputBasisMeasurementEq State.complexWeight
      complexRotation complexOutputTwist :=
  complexRotation_outputTwist.pureInputBasisMeasurementEq

theorem complexOutputTwist_not_projectiveActionEq :
    ¬ ComplexProjectiveActionEq complexRotation complexOutputTwist := by
  intro h
  rcases h complexBasisFalse with ⟨eta, _, hout⟩
  have h0 := congrFun hout false
  have h1 := congrFun hout true
  have h0re := congrArg Complex.re h0
  have h0im := congrArg Complex.im h0
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  norm_num [Matrix.mulVec, dotProduct, Fintype.univ_bool, complexRotation,
    realRotation, complexOutputTwist, complexBasisFalse] at
    h0re h0im h1re h1im
  linarith

/-- A nontrivial complex global phase of the rational rotation. -/
def complexIRotation : Matrix Bool Bool ℂ :=
  Complex.I • complexRotation

theorem complexRotation_I_global :
    ComplexGlobalPhaseEq complexRotation complexIRotation :=
  ⟨Complex.I, Complex.normSq_I, rfl⟩

theorem complexRotation_I_not_exact :
    ¬ ExactOperatorEq complexRotation complexIRotation := by
  intro h
  have h00 := congrFun (congrFun h false) false
  have him := congrArg Complex.im h00
  norm_num [complexRotation, realRotation, complexIRotation] at him

theorem complexIRotation_mem_unitary :
    complexIRotation ∈ unitary (Matrix Bool Bool ℂ) :=
  complexRotation_I_global.mem_unitary complexRotation_mem_unitary

/-! ## Nontrivial chronological-circuit phase examples -/

/-- The unique split for a zero-wire gate. -/
def emptySplit : Empty ⊕ Empty ≃ Empty :=
  Equiv.sumEmpty Empty Empty

/-- The unique zero-wire computational basis assignment. -/
def emptyBasis : BitBasis Empty :=
  fun e ↦ nomatch e

/-- The scalar `-1` real local matrix. -/
def realNegLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℝ :=
  fun _ _ ↦ -1

/-- The corresponding placed zero-wire real gate. -/
def realNegGate : PlacedGate ℝ Empty :=
  PlacedGate.ofSplit emptySplit realNegLocal

/-- The corresponding one-gate chronological real circuit. -/
def realNegCircuit : OrderedCircuit ℝ Empty :=
  [realNegGate]

/-- The scalar `I` complex local matrix. -/
def complexILocal : Matrix (BitBasis Empty) (BitBasis Empty) ℂ :=
  fun _ _ ↦ Complex.I

/-- The corresponding placed zero-wire complex gate. -/
def complexIGate : PlacedGate ℂ Empty :=
  PlacedGate.ofSplit emptySplit complexILocal

/-- The corresponding one-gate chronological complex circuit. -/
def complexICircuit : OrderedCircuit ℂ Empty :=
  [complexIGate]

theorem nil_realNegCircuit_global :
    RealCircuitGlobalSignEq ([] : OrderedCircuit ℝ Empty)
      realNegCircuit := by
  refine ⟨-1, by norm_num, ?_⟩
  ext x y
  simp [realNegCircuit, realNegGate, realNegLocal, emptySplit]

theorem nil_realNegCircuit_not_exact :
    ¬ ExactCircuitEq ([] : OrderedCircuit ℝ Empty)
      realNegCircuit := by
  intro h
  have he := congrFun (congrFun h emptyBasis) emptyBasis
  norm_num [realNegCircuit, realNegGate, realNegLocal, emptySplit,
    emptyBasis] at he

theorem nil_complexICircuit_global :
    ComplexCircuitGlobalPhaseEq ([] : OrderedCircuit ℂ Empty)
      complexICircuit := by
  refine ⟨Complex.I, Complex.normSq_I, ?_⟩
  ext x y
  simp [complexICircuit, complexIGate, complexILocal, emptySplit]

theorem nil_complexICircuit_not_exact :
    ¬ ExactCircuitEq ([] : OrderedCircuit ℂ Empty)
      complexICircuit := by
  intro h
  have he := congrFun (congrFun h emptyBasis) emptyBasis
  have him := congrArg Complex.im he
  norm_num [complexICircuit, complexIGate, complexILocal, emptySplit,
    emptyBasis] at him

end QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit

#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.realGlobalSign_api
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.complexGlobalPhase_api
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.realCircuitGlobalSign_api
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.complexCircuitGlobalPhase_api
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.realInputTwist_not_pureInputBasisMeasurementEq
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.realOutputTwist_not_projectiveActionEq
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.complexInputTwist_not_pureInputBasisMeasurementEq
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.complexOutputTwist_not_projectiveActionEq
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.nil_realNegCircuit_not_exact
#print axioms QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit.nil_complexICircuit_not_exact
