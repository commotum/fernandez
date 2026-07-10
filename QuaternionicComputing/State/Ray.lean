module

public import QuaternionicComputing.State.RealPhase
public import QuaternionicComputing.State.ComplexPhase

/-!
# Normalized pure-state rays

This file quotients finite normalized real, complex, and quaternionic state
representatives by their scalar-correct unit phase relations.  Real rays use a
square-one sign, complex rays use one unit scalar on the right, and
quaternionic rays use one unit quaternion strictly on the right.

The quotient relation never identifies states merely because their basis
weights agree.  Every quotient value still has a normalized representative;
consequently these ray types are inhabited exactly when the finite index type
is inhabited.
-/

@[expose] public noncomputable section

open scoped BigOperators Quaternion RightActions

namespace QuaternionicComputing.State

universe u v

/-! ## Explicit phase setoids and quotient types -/

/-- Normalized real states modulo one square-one real sign. -/
def realRaySetoid (I : Type u) [Fintype I] : Setoid (RealState I) where
  r a b := QuaternionicComputing.Real.SignEquivalent (a : I → ℝ) b
  iseqv :=
    ⟨fun a ↦ QuaternionicComputing.Real.signEquivalent_refl a,
      fun h ↦ QuaternionicComputing.Real.signEquivalent_symm h,
      fun h₁ h₂ ↦ QuaternionicComputing.Real.signEquivalent_trans h₁ h₂⟩

/-- Normalized complex states modulo one unit complex phase on the right. -/
def complexRaySetoid (I : Type u) [Fintype I] : Setoid (ComplexState I) where
  r a b := QuaternionicComputing.Complex.RightPhaseEquivalent (a : I → ℂ) b
  iseqv :=
    ⟨fun a ↦ QuaternionicComputing.Complex.rightPhaseEquivalent_refl a,
      fun h ↦ QuaternionicComputing.Complex.rightPhaseEquivalent_symm h,
      fun h₁ h₂ ↦
        QuaternionicComputing.Complex.rightPhaseEquivalent_trans h₁ h₂⟩

/-- Normalized quaternionic states modulo one unit quaternion on the right. -/
def quaternionRaySetoid (I : Type u) [Fintype I] : Setoid (QuaternionState I) where
  r a b := QuaternionicComputing.Quaternion.RightPhaseEquivalent
    (a : I → ℍ[ℝ]) b
  iseqv :=
    ⟨fun a ↦ QuaternionicComputing.Quaternion.rightPhaseEquivalent_refl a,
      fun h ↦ QuaternionicComputing.Quaternion.rightPhaseEquivalent_symm h,
      fun h₁ h₂ ↦
        QuaternionicComputing.Quaternion.rightPhaseEquivalent_trans h₁ h₂⟩

/-- Finite normalized real pure states modulo a global sign. -/
def RealRay (I : Type u) [Fintype I] :=
  Quotient (realRaySetoid I)

/-- Finite normalized complex pure states modulo a global unit phase. -/
def ComplexRay (I : Type u) [Fintype I] :=
  Quotient (complexRaySetoid I)

/-- Finite normalized quaternionic pure states modulo a global unit right phase. -/
def QuaternionRay (I : Type u) [Fintype I] :=
  Quotient (quaternionRaySetoid I)

/-- A normalized two-level real ray. -/
abbrev RebitRay := RealRay Bool

/-- A normalized two-level complex ray. -/
abbrev QubitRay := ComplexRay Bool

/-- A normalized two-level quaternionic right-phase ray. -/
abbrev QuaterbitRay := QuaternionRay Bool

/-! ## Real-ray interface -/

namespace RealRay

variable {I : Type u} [Fintype I]

/-- Send a normalized real representative to its sign ray. -/
def mk (a : RealState I) : RealRay I :=
  Quotient.mk (realRaySetoid I) a

/-- Two normalized real representatives define the same ray exactly when they differ by a unit sign. -/
@[simp]
theorem mk_eq_mk_iff {a b : RealState I} :
    mk a = mk b ↔
      QuaternionicComputing.Real.SignEquivalent (a : I → ℝ) b :=
  Quotient.eq

/-- Every real ray has a normalized representative. -/
theorem exists_rep (r : RealRay I) : ∃ a : RealState I, mk a = r := by
  change Quotient (realRaySetoid I) at r
  exact Quotient.exists_rep r

/-- Prove a proposition about real rays by proving it on every normalized representative. -/
@[elab_as_elim]
theorem inductionOn {motive : RealRay I → Prop} (r : RealRay I)
    (h : ∀ a : RealState I, motive (mk a)) : motive r :=
  Quotient.inductionOn r h

/-- Descend a phase-invariant function from normalized real states to real rays. -/
def lift {B : Sort v} (f : RealState I → B)
    (h : ∀ (a b : RealState I),
      QuaternionicComputing.Real.SignEquivalent (a : I → ℝ) b →
        f a = f b) :
    RealRay I → B :=
  Quotient.lift f h

/-- A descended real-ray function computes on a constructor by using its representative. -/
@[simp]
theorem lift_mk {B : Sort v} (f : RealState I → B)
    (h : ∀ (a b : RealState I),
      QuaternionicComputing.Real.SignEquivalent (a : I → ℝ) b →
        f a = f b)
    (a : RealState I) :
    lift f h (mk a) = f a :=
  rfl

end RealRay

/-! ## Complex-ray interface -/

namespace ComplexRay

variable {I : Type u} [Fintype I]

/-- Send a normalized complex representative to its unit-phase ray. -/
def mk (a : ComplexState I) : ComplexRay I :=
  Quotient.mk (complexRaySetoid I) a

/-- Two normalized complex representatives define the same ray exactly when they differ by a unit right phase. -/
@[simp]
theorem mk_eq_mk_iff {a b : ComplexState I} :
    mk a = mk b ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent (a : I → ℂ) b :=
  Quotient.eq

/-- Every complex ray has a normalized representative. -/
theorem exists_rep (r : ComplexRay I) : ∃ a : ComplexState I, mk a = r := by
  change Quotient (complexRaySetoid I) at r
  exact Quotient.exists_rep r

/-- Prove a proposition about complex rays by proving it on every normalized representative. -/
@[elab_as_elim]
theorem inductionOn {motive : ComplexRay I → Prop} (r : ComplexRay I)
    (h : ∀ a : ComplexState I, motive (mk a)) : motive r :=
  Quotient.inductionOn r h

/-- Descend a phase-invariant function from normalized complex states to complex rays. -/
def lift {B : Sort v} (f : ComplexState I → B)
    (h : ∀ (a b : ComplexState I),
      QuaternionicComputing.Complex.RightPhaseEquivalent (a : I → ℂ) b →
        f a = f b) :
    ComplexRay I → B :=
  Quotient.lift f h

/-- A descended complex-ray function computes on a constructor by using its representative. -/
@[simp]
theorem lift_mk {B : Sort v} (f : ComplexState I → B)
    (h : ∀ (a b : ComplexState I),
      QuaternionicComputing.Complex.RightPhaseEquivalent (a : I → ℂ) b →
        f a = f b)
    (a : ComplexState I) :
    lift f h (mk a) = f a :=
  rfl

end ComplexRay

/-! ## Quaternionic-ray interface -/

namespace QuaternionRay

variable {I : Type u} [Fintype I]

/-- Send a normalized quaternionic representative to its unit right-phase ray. -/
def mk (a : QuaternionState I) : QuaternionRay I :=
  Quotient.mk (quaternionRaySetoid I) a

/-- Two normalized quaternionic representatives define the same ray exactly when they differ by a unit quaternion on the right. -/
@[simp]
theorem mk_eq_mk_iff {a b : QuaternionState I} :
    mk a = mk b ↔
      QuaternionicComputing.Quaternion.RightPhaseEquivalent
        (a : I → ℍ[ℝ]) b :=
  Quotient.eq

/-- Every quaternionic ray has a normalized representative. -/
theorem exists_rep (r : QuaternionRay I) :
    ∃ a : QuaternionState I, mk a = r := by
  change Quotient (quaternionRaySetoid I) at r
  exact Quotient.exists_rep r

/-- Prove a proposition about quaternionic rays by proving it on every normalized representative. -/
@[elab_as_elim]
theorem inductionOn {motive : QuaternionRay I → Prop} (r : QuaternionRay I)
    (h : ∀ a : QuaternionState I, motive (mk a)) : motive r :=
  Quotient.inductionOn r h

/-- Descend a right-phase-invariant function from normalized quaternionic states to rays. -/
def lift {B : Sort v} (f : QuaternionState I → B)
    (h : ∀ (a b : QuaternionState I),
      QuaternionicComputing.Quaternion.RightPhaseEquivalent
        (a : I → ℍ[ℝ]) b → f a = f b) :
    QuaternionRay I → B :=
  Quotient.lift f h

/-- A descended quaternionic-ray function computes on a constructor by using its representative. -/
@[simp]
theorem lift_mk {B : Sort v} (f : QuaternionState I → B)
    (h : ∀ (a b : QuaternionState I),
      QuaternionicComputing.Quaternion.RightPhaseEquivalent
        (a : I → ℍ[ℝ]) b → f a = f b)
    (a : QuaternionState I) :
    lift f h (mk a) = f a :=
  rfl

end QuaternionRay

/-! ## Exact index-inhabitation boundary -/

private theorem index_nonempty_of_normalizedState
    {I : Type u} [Fintype I] {A : Type v} {weight : A → ℝ}
    (a : NormalizedState I A weight) : Nonempty I := by
  by_contra hI
  haveI : IsEmpty I := not_nonempty_iff.mp hI
  have h := a.property
  simp [totalWeight] at h

private def realBasisState {I : Type u} [Fintype I] (i : I) : RealState I := by
  classical
  refine ⟨Pi.single i 1, ?_⟩
  simp [totalWeight, basisWeight, realWeight, Pi.single_apply]

private def complexBasisState {I : Type u} [Fintype I]
    (i : I) : ComplexState I := by
  classical
  refine ⟨Pi.single i 1, ?_⟩
  simp [totalWeight, basisWeight, complexWeight, Pi.single_apply]

private def quaternionBasisState {I : Type u} [Fintype I]
    (i : I) : QuaternionState I := by
  classical
  refine ⟨Pi.single i 1, ?_⟩
  simp [totalWeight, basisWeight, quaternionWeight, Pi.single_apply]

/-- A nonempty finite index type admits a normalized real ray. -/
noncomputable instance realRayNonempty {I : Type u} [Fintype I] [Nonempty I] :
    Nonempty (RealRay I) :=
  ⟨RealRay.mk (realBasisState (Classical.choice inferInstance))⟩

/-- A nonempty finite index type admits a normalized complex ray. -/
noncomputable instance complexRayNonempty {I : Type u} [Fintype I] [Nonempty I] :
    Nonempty (ComplexRay I) :=
  ⟨ComplexRay.mk (complexBasisState (Classical.choice inferInstance))⟩

/-- A nonempty finite index type admits a normalized quaternionic ray. -/
noncomputable instance quaternionRayNonempty {I : Type u} [Fintype I]
    [Nonempty I] : Nonempty (QuaternionRay I) :=
  ⟨QuaternionRay.mk (quaternionBasisState (Classical.choice inferInstance))⟩

/-- No normalized real ray exists on an empty index type. -/
instance realRayIsEmpty {I : Type u} [Fintype I] [IsEmpty I] :
    IsEmpty (RealRay I) where
  false r := RealRay.inductionOn r fun a ↦
    (not_nonempty_iff.mpr inferInstance) (index_nonempty_of_normalizedState a)

/-- No normalized complex ray exists on an empty index type. -/
instance complexRayIsEmpty {I : Type u} [Fintype I] [IsEmpty I] :
    IsEmpty (ComplexRay I) where
  false r := ComplexRay.inductionOn r fun a ↦
    (not_nonempty_iff.mpr inferInstance) (index_nonempty_of_normalizedState a)

/-- No normalized quaternionic ray exists on an empty index type. -/
instance quaternionRayIsEmpty {I : Type u} [Fintype I] [IsEmpty I] :
    IsEmpty (QuaternionRay I) where
  false r := QuaternionRay.inductionOn r fun a ↦
    (not_nonempty_iff.mpr inferInstance) (index_nonempty_of_normalizedState a)

/-- Normalized real rays exist exactly on nonempty finite index types. -/
theorem realRay_nonempty_iff {I : Type u} [Fintype I] :
    Nonempty (RealRay I) ↔ Nonempty I := by
  constructor
  · rintro ⟨r⟩
    exact RealRay.inductionOn r index_nonempty_of_normalizedState
  · intro hI
    letI : Nonempty I := hI
    infer_instance

/-- Normalized complex rays exist exactly on nonempty finite index types. -/
theorem complexRay_nonempty_iff {I : Type u} [Fintype I] :
    Nonempty (ComplexRay I) ↔ Nonempty I := by
  constructor
  · rintro ⟨r⟩
    exact ComplexRay.inductionOn r index_nonempty_of_normalizedState
  · intro hI
    letI : Nonempty I := hI
    infer_instance

/-- Normalized quaternionic rays exist exactly on nonempty finite index types. -/
theorem quaternionRay_nonempty_iff {I : Type u} [Fintype I] :
    Nonempty (QuaternionRay I) ↔ Nonempty I := by
  constructor
  · rintro ⟨r⟩
    exact QuaternionRay.inductionOn r index_nonempty_of_normalizedState
  · intro hI
    letI : Nonempty I := hI
    infer_instance

end QuaternionicComputing.State
