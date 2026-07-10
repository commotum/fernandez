module

public import QuaternionicComputing.State.RealificationOrbit

/-!
# Boundary between complex rays and ordinary real rays

Complex phase becomes a rotation of the two realification sectors.  Ordinary
real rays quotient only by a common sign, so the canonical first and second
realification columns do not define representative-independent assignments
from nonempty complex-ray spaces to ordinary real-ray spaces.

This file states that boundary exactly.  It does not claim that arbitrary
functions between the two quotient types fail to exist.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.State

universe u

private theorem complexState_exists_ne_zero {I : Type u} [Fintype I]
    (psi : ComplexState I) : ∃ i : I, psi i ≠ 0 := by
  by_contra h
  push Not at h
  have hpsi : (psi : I -> Complex) = 0 := by
    funext i
    exact h i
  have hnorm := psi.property
  rw [hpsi] at hnorm
  simp [totalWeight, basisWeight, complexWeight] at hnorm

private theorem complex_I_not_real_sign :
    ¬ (Complex.I = 1 ∨ Complex.I = -1) := by
  rintro (h | h)
  · have him := congrArg Complex.im h
    norm_num at him
  · have him := congrArg Complex.im h
    norm_num at him

/--
A unit complex phase preserves the ordinary real ray of the canonical first
realification column exactly when the phase is a real sign.
-/
theorem realColumn0State_rightPhase_realRay_eq_iff
    {I : Type u} [Fintype I] (psi : ComplexState I)
    (eta : Complex) (heta : Complex.normSq eta = 1) :
    RealRay.mk
          (realColumn0State (ComplexState.rightPhase psi eta heta)) =
        RealRay.mk (realColumn0State psi) ↔
      eta = 1 ∨ eta = -1 := by
  constructor
  · intro h
    rcases RealRay.mk_eq_mk_iff_eq_or_eq_neg.mp h with hEq | hNeg
    · change realColumn0
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
        realColumn0 (psi : I -> Complex) at hEq
      have hPhase :
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
            (psi : I -> Complex) :=
        realColumn0_injective hEq
      obtain ⟨i, hi⟩ := complexState_exists_ne_zero psi
      left
      apply mul_left_cancel₀ hi
      simpa using congrFun hPhase i
    · change realColumn0
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
        -(realColumn0 (psi : I -> Complex)) at hNeg
      have hColumns :
          realColumn0
              (ComplexState.rightPhase psi eta heta : I -> Complex) =
            realColumn0 (fun i => -(psi i)) := by
        ext (i | i)
        · simpa [realColumn0] using congrFun hNeg (Sum.inl i)
        · simpa [realColumn0] using congrFun hNeg (Sum.inr i)
      have hPhase :
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
            fun i => -(psi i) :=
        realColumn0_injective hColumns
      obtain ⟨i, hi⟩ := complexState_exists_ne_zero psi
      right
      apply mul_left_cancel₀ hi
      simpa using congrFun hPhase i
  · rintro (rfl | rfl)
    · apply RealRay.mk_eq_mk_iff_eq_or_eq_neg.mpr
      left
      ext (i | i) <;> simp [realColumn0]
    · apply RealRay.mk_eq_mk_iff_eq_or_eq_neg.mpr
      right
      ext (i | i) <;> simp [realColumn0]

/--
A unit complex phase preserves the ordinary real ray of the canonical second
realification column exactly when the phase is a real sign.
-/
theorem realColumn1State_rightPhase_realRay_eq_iff
    {I : Type u} [Fintype I] (psi : ComplexState I)
    (eta : Complex) (heta : Complex.normSq eta = 1) :
    RealRay.mk
          (realColumn1State (ComplexState.rightPhase psi eta heta)) =
        RealRay.mk (realColumn1State psi) ↔
      eta = 1 ∨ eta = -1 := by
  constructor
  · intro h
    rcases RealRay.mk_eq_mk_iff_eq_or_eq_neg.mp h with hEq | hNeg
    · change realColumn1
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
        realColumn1 (psi : I -> Complex) at hEq
      have hPhase :
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
            (psi : I -> Complex) :=
        realColumn1_injective hEq
      obtain ⟨i, hi⟩ := complexState_exists_ne_zero psi
      left
      apply mul_left_cancel₀ hi
      simpa using congrFun hPhase i
    · change realColumn1
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
        -(realColumn1 (psi : I -> Complex)) at hNeg
      have hColumns :
          realColumn1
              (ComplexState.rightPhase psi eta heta : I -> Complex) =
            realColumn1 (fun i => -(psi i)) := by
        ext (i | i)
        · simpa [realColumn1] using congrFun hNeg (Sum.inl i)
        · simpa [realColumn1] using congrFun hNeg (Sum.inr i)
      have hPhase :
          (ComplexState.rightPhase psi eta heta : I -> Complex) =
            fun i => -(psi i) :=
        realColumn1_injective hColumns
      obtain ⟨i, hi⟩ := complexState_exists_ne_zero psi
      right
      apply mul_left_cancel₀ hi
      simpa using congrFun hPhase i
  · rintro (rfl | rfl)
    · apply RealRay.mk_eq_mk_iff_eq_or_eq_neg.mpr
      left
      ext (i | i) <;> simp [realColumn1]
    · apply RealRay.mk_eq_mk_iff_eq_or_eq_neg.mpr
      right
      ext (i | i) <;> simp [realColumn1]

/--
Multiplication by `I` gives a phase-equivalent complex representative whose
canonical first-column encoding belongs to a different ordinary real ray.
-/
theorem realColumn0State_rightPhase_I_realRay_ne
    {I : Type u} [Fintype I] (psi : ComplexState I) :
    RealRay.mk
          (realColumn0State
            (ComplexState.rightPhase psi Complex.I Complex.normSq_I)) ≠
        RealRay.mk (realColumn0State psi) := by
  intro h
  exact complex_I_not_real_sign
    ((realColumn0State_rightPhase_realRay_eq_iff
      psi Complex.I Complex.normSq_I).mp h)

/--
Multiplication by `I` likewise sends the canonical second-column encoding to
a different ordinary real ray.
-/
theorem realColumn1State_rightPhase_I_realRay_ne
    {I : Type u} [Fintype I] (psi : ComplexState I) :
    RealRay.mk
          (realColumn1State
            (ComplexState.rightPhase psi Complex.I Complex.normSq_I)) ≠
        RealRay.mk (realColumn1State psi) := by
  intro h
  exact complex_I_not_real_sign
    ((realColumn1State_rightPhase_realRay_eq_iff
      psi Complex.I Complex.normSq_I).mp h)

/--
On a nonempty finite index type, no constructor-compatible assignment from
complex rays can return the canonical first-column ordinary real ray for every
normalized representative.
-/
theorem no_complexRay_realColumn0_lift
    {I : Type u} [Fintype I] [Nonempty I] :
    ¬ (∃ F : ComplexRay I -> RealRay (I ⊕ I),
      ∀ psi : ComplexState I,
        F (ComplexRay.mk psi) = RealRay.mk (realColumn0State psi)) := by
  rintro ⟨F, hF⟩
  let r : ComplexRay I :=
    Classical.choice (inferInstance : Nonempty (ComplexRay I))
  obtain ⟨psi, _⟩ := ComplexRay.exists_rep r
  let phasePsi : ComplexState I :=
    ComplexState.rightPhase psi Complex.I Complex.normSq_I
  have hSource : ComplexRay.mk phasePsi = ComplexRay.mk psi :=
    ComplexRay.mk_eq_mk_iff.mpr
      (ComplexState.rightPhaseEquivalent_rightPhase
        psi Complex.I Complex.normSq_I)
  apply realColumn0State_rightPhase_I_realRay_ne psi
  calc
    RealRay.mk (realColumn0State phasePsi) =
        F (ComplexRay.mk phasePsi) := (hF phasePsi).symm
    _ = F (ComplexRay.mk psi) := congrArg F hSource
    _ = RealRay.mk (realColumn0State psi) := hF psi

/--
On a nonempty finite index type, no constructor-compatible assignment from
complex rays can return the canonical second-column ordinary real ray for
every normalized representative.
-/
theorem no_complexRay_realColumn1_lift
    {I : Type u} [Fintype I] [Nonempty I] :
    ¬ (∃ F : ComplexRay I -> RealRay (I ⊕ I),
      ∀ psi : ComplexState I,
        F (ComplexRay.mk psi) = RealRay.mk (realColumn1State psi)) := by
  rintro ⟨F, hF⟩
  let r : ComplexRay I :=
    Classical.choice (inferInstance : Nonempty (ComplexRay I))
  obtain ⟨psi, _⟩ := ComplexRay.exists_rep r
  let phasePsi : ComplexState I :=
    ComplexState.rightPhase psi Complex.I Complex.normSq_I
  have hSource : ComplexRay.mk phasePsi = ComplexRay.mk psi :=
    ComplexRay.mk_eq_mk_iff.mpr
      (ComplexState.rightPhaseEquivalent_rightPhase
        psi Complex.I Complex.normSq_I)
  apply realColumn1State_rightPhase_I_realRay_ne psi
  calc
    RealRay.mk (realColumn1State phasePsi) =
        F (ComplexRay.mk phasePsi) := (hF phasePsi).symm
    _ = F (ComplexRay.mk psi) := congrArg F hSource
    _ = RealRay.mk (realColumn1State psi) := hF psi

/--
The canonical first-column constructor equation has a solution exactly on an
empty finite index type, where both its source and agreement condition are
vacuous.
-/
theorem complexRay_realColumn0_lift_exists_iff_isEmpty
    {I : Type u} [Fintype I] :
    (∃ F : ComplexRay I -> RealRay (I ⊕ I),
        ∀ psi : ComplexState I,
          F (ComplexRay.mk psi) = RealRay.mk (realColumn0State psi)) ↔
      IsEmpty I := by
  constructor
  · intro hLift
    apply not_nonempty_iff.mp
    intro hI
    letI : Nonempty I := hI
    exact no_complexRay_realColumn0_lift hLift
  · intro hI
    letI : IsEmpty I := hI
    refine ⟨fun r => isEmptyElim r, ?_⟩
    intro psi
    exact isEmptyElim (ComplexRay.mk psi)

/--
The canonical second-column constructor equation has the same exact empty
boundary.
-/
theorem complexRay_realColumn1_lift_exists_iff_isEmpty
    {I : Type u} [Fintype I] :
    (∃ F : ComplexRay I -> RealRay (I ⊕ I),
        ∀ psi : ComplexState I,
          F (ComplexRay.mk psi) = RealRay.mk (realColumn1State psi)) ↔
      IsEmpty I := by
  constructor
  · intro hLift
    apply not_nonempty_iff.mp
    intro hI
    letI : Nonempty I := hI
    exact no_complexRay_realColumn1_lift hLift
  · intro hI
    letI : IsEmpty I := hI
    refine ⟨fun r => isEmptyElim r, ?_⟩
    intro psi
    exact isEmptyElim (ComplexRay.mk psi)

end QuaternionicComputing.State

