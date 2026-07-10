module

public import QuaternionicComputing.State.Ray

/-!
# Normalized ray quotient audit

This non-root diagnostic leaf gives named consumers for every stable
declaration exported by `State.Ray`.  It checks the complete real, complex,
and quaternionic quotient interfaces, the exact empty/nonempty index
boundary, and concrete unit-phase identifications for a rebit, qubit, and
quaterbit.

The quaternionic example uses multiplication by `j` strictly on the right.
The public root deliberately does not import this file.
-/

@[expose] public noncomputable section

open scoped BigOperators Quaternion RightActions

namespace QuaternionicComputing.State.RayAudit

open QuaternionicComputing.Real
open QuaternionicComputing.Complex
open QuaternionicComputing.Quaternion

/-! ## Concrete normalized representatives -/

/-- A normalized real basis representative. -/
def realReferenceState : RealState Bool :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool]⟩

/-- The real scalar `-1` is a unit sign. -/
theorem real_negOne_sq : (-1 : ℝ) * (-1) = 1 := by
  norm_num

/-- The real reference representative multiplied by `-1` on the right. -/
def realNegOneState : RealState Bool :=
  RealState.rightSign realReferenceState (-1) real_negOne_sq

/-- A normalized complex basis representative. -/
def complexReferenceState : ComplexState Bool :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

/-- The complex scalar `I` has unit norm square. -/
theorem complex_I_normSq : _root_.Complex.normSq _root_.Complex.I = 1 := by
  simp [_root_.Complex.normSq_apply]

/-- The complex reference representative multiplied by `I` on the right. -/
def complexIState : ComplexState Bool :=
  ComplexState.rightPhase complexReferenceState _root_.Complex.I
    complex_I_normSq

/-- A normalized quaternionic basis representative. -/
def quaternionReferenceState : QuaternionState Bool :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, quaternionWeight, Fintype.univ_bool]⟩

/-- The quaternionic reference representative multiplied by `j` on the right. -/
def quaternionJState : QuaternionState Bool :=
  QuaternionState.rightPhase quaternionReferenceState Quaternion.j normSq_j

/-! ## Complete scalar-specific quotient consumers -/

/-- Complete named consumer for the normalized real-ray quotient API. -/
theorem realRay_api
    (r : RealRay Bool) (a b : RealState Bool)
    (f g : RebitRay → ℝ)
    (hfg : ∀ x : RealState Bool,
      f (RealRay.mk x) = g (RealRay.mk x)) :
    ((realRaySetoid Bool) a b ↔ SignEquivalent (a : Bool → ℝ) b) ∧
      (RealRay.mk a = RealRay.mk b ↔
        SignEquivalent (a : Bool → ℝ) b) ∧
      (RealRay.mk a = RealRay.mk b ↔
        (a : Bool → ℝ) = (b : Bool → ℝ) ∨
          (a : Bool → ℝ) = -(b : Bool → ℝ)) ∧
      (∃ x : RealState Bool, RealRay.mk x = r) ∧
      r = r ∧
      RealRay.lift
          (fun x : RealState Bool ↦ realBasisWeight x false)
          (fun _ _ h ↦ signEquivalent_realBasisWeight h false)
          (RealRay.mk a) =
        realBasisWeight a false ∧
      f = g := by
  exact ⟨Iff.rfl,
    RealRay.mk_eq_mk_iff,
    RealRay.mk_eq_mk_iff_eq_or_eq_neg,
    RealRay.exists_rep r,
    RealRay.inductionOn r (fun _ ↦ rfl),
    RealRay.lift_mk
      (fun x : RealState Bool ↦ realBasisWeight x false)
      (fun _ _ h ↦ signEquivalent_realBasisWeight h false) a,
    RealRay.function_ext hfg⟩

/-- Complete named consumer for the normalized complex-ray quotient API. -/
theorem complexRay_api
    (r : ComplexRay Bool) (a b : ComplexState Bool)
    (f g : QubitRay → ℝ)
    (hfg : ∀ x : ComplexState Bool,
      f (ComplexRay.mk x) = g (ComplexRay.mk x)) :
    ((complexRaySetoid Bool) a b ↔
        RightPhaseEquivalent (a : Bool → ℂ) b) ∧
      (ComplexRay.mk a = ComplexRay.mk b ↔
        RightPhaseEquivalent (a : Bool → ℂ) b) ∧
      (∃ x : ComplexState Bool, ComplexRay.mk x = r) ∧
      r = r ∧
      ComplexRay.lift
          (fun x : ComplexState Bool ↦ complexBasisWeight x false)
          (fun _ _ h ↦ rightPhaseEquivalent_complexBasisWeight h false)
          (ComplexRay.mk a) =
        complexBasisWeight a false ∧
      f = g := by
  exact ⟨Iff.rfl,
    ComplexRay.mk_eq_mk_iff,
    ComplexRay.exists_rep r,
    ComplexRay.inductionOn r (fun _ ↦ rfl),
    ComplexRay.lift_mk
      (fun x : ComplexState Bool ↦ complexBasisWeight x false)
      (fun _ _ h ↦ rightPhaseEquivalent_complexBasisWeight h false) a,
    ComplexRay.function_ext hfg⟩

/-- Complete named consumer for the normalized quaternionic right-ray quotient API. -/
theorem quaternionRay_api
    (r : QuaternionRay Bool) (a b : QuaternionState Bool)
    (f g : QuaterbitRay → ℝ)
    (hfg : ∀ x : QuaternionState Bool,
      f (QuaternionRay.mk x) = g (QuaternionRay.mk x)) :
    ((quaternionRaySetoid Bool) a b ↔
        RightPhaseEquivalent (a : Bool → ℍ[ℝ]) b) ∧
      (QuaternionRay.mk a = QuaternionRay.mk b ↔
        RightPhaseEquivalent (a : Bool → ℍ[ℝ]) b) ∧
      (∃ x : QuaternionState Bool, QuaternionRay.mk x = r) ∧
      r = r ∧
      QuaternionRay.lift
          (fun x : QuaternionState Bool ↦ quaternionBasisWeight x false)
          (fun _ _ h ↦ rightPhaseEquivalent_quaternionBasisWeight h false)
          (QuaternionRay.mk a) =
        quaternionBasisWeight a false ∧
      f = g := by
  exact ⟨Iff.rfl,
    QuaternionRay.mk_eq_mk_iff,
    QuaternionRay.exists_rep r,
    QuaternionRay.inductionOn r (fun _ ↦ rfl),
    QuaternionRay.lift_mk
      (fun x : QuaternionState Bool ↦ quaternionBasisWeight x false)
      (fun _ _ h ↦ rightPhaseEquivalent_quaternionBasisWeight h false) a,
    QuaternionRay.function_ext hfg⟩

/-! ## Exact index-inhabitation boundary -/

/-- Complete named consumer for all Bool nonempty and Empty is-empty instances and iff theorems. -/
theorem rayInhabitation_api :
    Nonempty RebitRay ∧
      Nonempty QubitRay ∧
      Nonempty QuaterbitRay ∧
      IsEmpty (RealRay Empty) ∧
      IsEmpty (ComplexRay Empty) ∧
      IsEmpty (QuaternionRay Empty) ∧
      (Nonempty (RealRay Bool) ↔ Nonempty Bool) ∧
      (Nonempty (ComplexRay Bool) ↔ Nonempty Bool) ∧
      (Nonempty (QuaternionRay Bool) ↔ Nonempty Bool) := by
  exact ⟨realRayNonempty,
    complexRayNonempty,
    quaternionRayNonempty,
    realRayIsEmpty,
    complexRayIsEmpty,
    quaternionRayIsEmpty,
    realRay_nonempty_iff,
    complexRay_nonempty_iff,
    quaternionRay_nonempty_iff⟩

/-! ## Concrete phase identifications -/

/-- Negating a normalized rebit representative does not change its real ray. -/
theorem rebit_negOne_ray :
    RealRay.mk realNegOneState = RealRay.mk realReferenceState :=
  RealRay.mk_eq_mk_iff.mpr
    (RealState.signEquivalent_rightSign
      realReferenceState (-1) real_negOne_sq)

/-- Multiplying a normalized qubit representative by `I` does not change its complex ray. -/
theorem qubit_I_ray :
    ComplexRay.mk complexIState = ComplexRay.mk complexReferenceState :=
  ComplexRay.mk_eq_mk_iff.mpr
    (ComplexState.rightPhaseEquivalent_rightPhase
      complexReferenceState _root_.Complex.I complex_I_normSq)

/--
Multiplying a normalized quaterbit representative by `j` on the right does
not change its ray.
-/
theorem quaterbit_rightJ_ray :
    QuaternionRay.mk quaternionJState =
      QuaternionRay.mk quaternionReferenceState :=
  QuaternionRay.mk_eq_mk_iff.mpr
    (QuaternionState.rightPhaseEquivalent_rightPhase
      quaternionReferenceState Quaternion.j normSq_j)

/-! ## Representative axiom audit -/

#print axioms realRay_api
#print axioms complexRay_api
#print axioms quaternionRay_api
#print axioms rayInhabitation_api
#print axioms rebit_negOne_ray
#print axioms qubit_I_ray
#print axioms quaterbit_rightJ_ray

end QuaternionicComputing.State.RayAudit
