module

public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Ray

/-!
# Complex phase as rotation of doubled real state sectors

Right multiplication by a complex scalar becomes one common real linear action
on each two-sector coordinate of the doubled real encoding.  A unit complex
phase is therefore a sector rotation, not in general one global real sign.

This file defines that action, proves its exact interaction with both canonical
realification columns, and quotients normalized doubled real states by the
resulting unit-phase orbits.  The orbit quotient is explicitly equivalent to
`ComplexRay`; it is deliberately distinct from `RealRay`.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicComputing.State

universe u v

variable {I : Type u}

/-! ## The real sector action -/

/--
The doubled-real action corresponding to right multiplication by `eta : ℂ`.

In the repository's sector order it sends `(x, y)` to
`(eta.re * x + eta.im * y, -eta.im * x + eta.re * y)`.
-/
def realSectorAction (eta : ℂ) (w : I ⊕ I → ℝ) : I ⊕ I → ℝ :=
  Sum.elim
    (fun i ↦ eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i))
    (fun i ↦ -eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i))

/-- The first-sector coordinate formula for `realSectorAction`. -/
@[simp]
theorem realSectorAction_inl (eta : ℂ) (w : I ⊕ I → ℝ) (i : I) :
    realSectorAction eta w (Sum.inl i) =
      eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i) :=
  rfl

/-- The second-sector coordinate formula for `realSectorAction`. -/
@[simp]
theorem realSectorAction_inr (eta : ℂ) (w : I ⊕ I → ℝ) (i : I) :
    realSectorAction eta w (Sum.inr i) =
      -eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i) :=
  rfl

/-- The complex scalar `1` acts identically on doubled real columns. -/
@[simp]
theorem realSectorAction_one (w : I ⊕ I → ℝ) :
    realSectorAction 1 w = w := by
  ext (i | i) <;> simp

/-- Complex multiplication is represented by composition of sector actions. -/
theorem realSectorAction_mul (eta theta : ℂ) (w : I ⊕ I → ℝ) :
    realSectorAction eta (realSectorAction theta w) =
      realSectorAction (eta * theta) w := by
  ext (i | i) <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/--
Sequential source right phases use the order `theta * eta`: first `theta`,
then `eta`.
-/
theorem realSectorAction_comp_right (theta eta : ℂ) (w : I ⊕ I → ℝ) :
    realSectorAction eta (realSectorAction theta w) =
      realSectorAction (theta * eta) w := by
  rw [realSectorAction_mul, mul_comm]

/-- The phase `I` is the clockwise quarter-turn `(x, y) ↦ (y, -x)`. -/
@[simp]
theorem realSectorAction_I (w : I ⊕ I → ℝ) :
    realSectorAction Complex.I w =
      Sum.elim (fun i ↦ w (Sum.inr i)) (fun i ↦ -w (Sum.inl i)) := by
  ext (i | i) <;> simp

/-! ## Canonical columns and top-sector coefficients -/

/-- Sector action is exactly source right multiplication on the first column. -/
theorem realSectorAction_realColumn0 (eta : ℂ) (w : I → ℂ) :
    realSectorAction eta (realColumn0 w) =
      realColumn0 (fun i ↦ w i * eta) := by
  ext (i | i) <;>
    simp [realSectorAction, realColumn0, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Sector action is exactly source right multiplication on the second column. -/
theorem realSectorAction_realColumn1 (eta : ℂ) (w : I → ℂ) :
    realSectorAction eta (realColumn1 w) =
      realColumn1 (fun i ↦ w i * eta) := by
  ext (i | i) <;>
    simp [realSectorAction, realColumn1, Complex.mul_re, Complex.mul_im] <;>
    ring

/--
On the first canonical column, right phase `eta` has top coefficients
`(eta.re, -eta.im)` in the `(column0, column1)` order.
-/
theorem realColumn0_right_mul (eta : ℂ) (w : I → ℂ) :
    realColumn0 (fun i ↦ w i * eta) =
      realTopCombination eta.re (-eta.im) w := by
  ext (i | i) <;>
    simp [realTopCombination, Complex.mul_re, Complex.mul_im] <;>
    ring

/--
On the second canonical column, right phase `eta` has top coefficients
`(eta.im, eta.re)` in the `(column0, column1)` order.
-/
theorem realColumn1_right_mul (eta : ℂ) (w : I → ℂ) :
    realColumn1 (fun i ↦ w i * eta) =
      realTopCombination eta.im eta.re w := by
  ext (i | i) <;>
    simp [realTopCombination, Complex.mul_re, Complex.mul_im] <;>
    ring

/-! ## Norm scaling -/

/-- Sector action scales total real squared weight by `Complex.normSq eta`. -/
theorem realSectorAction_realTotalWeight [Fintype I] (eta : ℂ)
    (w : I ⊕ I → ℝ) :
    realTotalWeight (realSectorAction eta w) =
      Complex.normSq eta * realTotalWeight w := by
  change (∑ x : I ⊕ I, realWeight (realSectorAction eta w x)) = _
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [realWeight_apply, realSectorAction_inl, realSectorAction_inr]
  change
    (∑ i : I,
      ((eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i)) *
          (eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i)) +
        (-eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i)) *
          (-eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i)))) = _
  simp_rw [show ∀ i : I,
      (eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i)) *
          (eta.re * w (Sum.inl i) + eta.im * w (Sum.inr i)) +
        (-eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i)) *
          (-eta.im * w (Sum.inl i) + eta.re * w (Sum.inr i)) =
        Complex.normSq eta *
          (realWeight (w (Sum.inl i)) + realWeight (w (Sum.inr i))) by
    intro i
    simp only [realWeight_apply, Complex.normSq_apply]
    ring]
  rw [← Finset.mul_sum]
  congr 1
  change
    (∑ i : I, (realWeight (w (Sum.inl i)) + realWeight (w (Sum.inr i)))) =
      ∑ x : I ⊕ I, realWeight (w x)
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]

/-- A unit complex sector action preserves total real squared weight. -/
theorem realSectorAction_realTotalWeight_of_normSq_eq_one [Fintype I]
    (eta : ℂ) (heta : Complex.normSq eta = 1) (w : I ⊕ I → ℝ) :
    realTotalWeight (realSectorAction eta w) = realTotalWeight w := by
  rw [realSectorAction_realTotalWeight, heta, one_mul]

/-! ## Normalized sector rotations -/

namespace RealState

variable [Fintype I]

/-- Rotate both sectors of a normalized doubled real state by a unit complex phase. -/
def sectorRotation (w : RealState (I ⊕ I)) (eta : ℂ)
    (heta : Complex.normSq eta = 1) : RealState (I ⊕ I) :=
  ⟨realSectorAction eta w, by
    change realTotalWeight (realSectorAction eta (w : I ⊕ I → ℝ)) = 1
    rw [realSectorAction_realTotalWeight, heta, one_mul]
    exact w.property⟩

/-- A normalized sector rotation computes by the raw action. -/
@[simp]
theorem sectorRotation_apply (w : RealState (I ⊕ I)) (eta : ℂ)
    (heta : Complex.normSq eta = 1) (x : I ⊕ I) :
    sectorRotation w eta heta x = realSectorAction eta w x :=
  rfl

/-- The unit phase `1` fixes every normalized doubled real state. -/
@[simp]
theorem sectorRotation_one (w : RealState (I ⊕ I)) :
    sectorRotation w 1 (by simp) = w := by
  apply Subtype.ext
  exact realSectorAction_one w

/-- Sector rotations compose according to complex multiplication. -/
theorem sectorRotation_mul (w : RealState (I ⊕ I))
    (eta theta : ℂ) (heta : Complex.normSq eta = 1)
    (htheta : Complex.normSq theta = 1) :
    sectorRotation (sectorRotation w theta htheta) eta heta =
      sectorRotation w (eta * theta) (by
        rw [Complex.normSq_mul, heta, htheta, one_mul]) := by
  apply Subtype.ext
  exact realSectorAction_mul eta theta w

/-- Applying source right phase `theta` and then `eta` rotates by `theta * eta`. -/
theorem sectorRotation_comp_right (w : RealState (I ⊕ I))
    (theta eta : ℂ) (htheta : Complex.normSq theta = 1)
    (heta : Complex.normSq eta = 1) :
    sectorRotation (sectorRotation w theta htheta) eta heta =
      sectorRotation w (theta * eta) (by
        rw [Complex.normSq_mul, htheta, heta, one_mul]) := by
  apply Subtype.ext
  exact realSectorAction_comp_right theta eta w

end RealState

/-! ## Unit phases as normalized top rebits -/

/-- The top rebit `(eta.re, -eta.im)` for the phased first real column. -/
def realPhaseTop0 (eta : ℂ) (heta : Complex.normSq eta = 1) : Rebit :=
  ⟨fun b ↦ if b then -eta.im else eta.re, by
    simpa [realTotalWeight, totalWeight, basisWeight, realWeight,
      Fintype.univ_bool, Complex.normSq_apply, add_comm] using heta⟩

/-- The first coordinate of `realPhaseTop0`. -/
@[simp]
theorem realPhaseTop0_false (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realPhaseTop0 eta heta false = eta.re :=
  rfl

/-- The second coordinate of `realPhaseTop0`. -/
@[simp]
theorem realPhaseTop0_true (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realPhaseTop0 eta heta true = -eta.im :=
  rfl

/-- The top rebit `(eta.im, eta.re)` for the phased second real column. -/
def realPhaseTop1 (eta : ℂ) (heta : Complex.normSq eta = 1) : Rebit :=
  ⟨fun b ↦ if b then eta.re else eta.im, by
    simpa [realTotalWeight, totalWeight, basisWeight, realWeight,
      Fintype.univ_bool, Complex.normSq_apply, add_comm] using heta⟩

/-- The first coordinate of `realPhaseTop1`. -/
@[simp]
theorem realPhaseTop1_false (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realPhaseTop1 eta heta false = eta.im :=
  rfl

/-- The second coordinate of `realPhaseTop1`. -/
@[simp]
theorem realPhaseTop1_true (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realPhaseTop1 eta heta true = eta.re :=
  rfl

/-- First-column realification converts normalized source phase to sector rotation. -/
theorem realColumn0State_rightPhase [Fintype I]
    (w : ComplexState I) (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realColumn0State (ComplexState.rightPhase w eta heta) =
      RealState.sectorRotation (realColumn0State w) eta heta := by
  apply Subtype.ext
  exact (realSectorAction_realColumn0 eta w).symm

/-- Second-column realification converts normalized source phase to sector rotation. -/
theorem realColumn1State_rightPhase [Fintype I]
    (w : ComplexState I) (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realColumn1State (ComplexState.rightPhase w eta heta) =
      RealState.sectorRotation (realColumn1State w) eta heta := by
  apply Subtype.ext
  exact (realSectorAction_realColumn1 eta w).symm

/-- The phased first normalized column is its exact packaged top-rebit state. -/
theorem realColumn0State_rightPhase_eq_realTopState [Fintype I]
    (w : ComplexState I) (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realColumn0State (ComplexState.rightPhase w eta heta) =
      realTopState (realPhaseTop0 eta heta) w := by
  apply Subtype.ext
  exact realColumn0_right_mul eta w

/-- The phased second normalized column is its exact packaged top-rebit state. -/
theorem realColumn1State_rightPhase_eq_realTopState [Fintype I]
    (w : ComplexState I) (eta : ℂ) (heta : Complex.normSq eta = 1) :
    realColumn1State (ComplexState.rightPhase w eta heta) =
      realTopState (realPhaseTop1 eta heta) w := by
  apply Subtype.ext
  exact realColumn1_right_mul eta w

/-! ## The raw unit-sector-phase relation -/

/-- Two doubled real columns lie in one common unit-complex sector orbit. -/
def RealSectorPhaseEquivalent (x y : I ⊕ I → ℝ) : Prop :=
  ∃ eta : ℂ, Complex.normSq eta = 1 ∧ x = realSectorAction eta y

/-- Unit-sector-phase equivalence is reflexive. -/
theorem realSectorPhaseEquivalent_refl (x : I ⊕ I → ℝ) :
    RealSectorPhaseEquivalent x x :=
  ⟨1, by simp, (realSectorAction_one x).symm⟩

/-- Unit-sector-phase equivalence is symmetric. -/
theorem realSectorPhaseEquivalent_symm {x y : I ⊕ I → ℝ}
    (hxy : RealSectorPhaseEquivalent x y) : RealSectorPhaseEquivalent y x := by
  rcases hxy with ⟨eta, heta, rfl⟩
  refine ⟨star eta, by simpa using heta, ?_⟩
  rw [realSectorAction_mul]
  have hprod : (star eta) * eta = (1 : ℂ) := by
    rw [mul_comm]
    change eta * (starRingEnd ℂ) eta = 1
    rw [Complex.mul_conj, heta]
    norm_num
  rw [hprod, realSectorAction_one]

/-- Unit-sector-phase equivalence is transitive in source right-phase order. -/
theorem realSectorPhaseEquivalent_trans {x y z : I ⊕ I → ℝ}
    (hxy : RealSectorPhaseEquivalent x y)
    (hyz : RealSectorPhaseEquivalent y z) : RealSectorPhaseEquivalent x z := by
  rcases hxy with ⟨eta, heta, rfl⟩
  rcases hyz with ⟨theta, htheta, rfl⟩
  refine ⟨theta * eta, by
    rw [Complex.normSq_mul, htheta, heta, one_mul], ?_⟩
  exact realSectorAction_comp_right theta eta z

/-- The raw unit-sector-phase relation is an equivalence relation. -/
theorem realSectorPhaseEquivalent_equivalence :
    Equivalence (@RealSectorPhaseEquivalent I) :=
  ⟨realSectorPhaseEquivalent_refl, realSectorPhaseEquivalent_symm,
    realSectorPhaseEquivalent_trans⟩

/-! ## Decoder characterization -/

/-- Re-encoding a decoded doubled real column returns the original column. -/
@[simp]
theorem realColumn0_complexOfRealColumn0 (w : I ⊕ I → ℝ) :
    realColumn0 (complexOfRealColumn0 w) = w := by
  ext (i | i) <;> simp [realColumn0, complexOfRealColumn0]

/-- Decoding a sector action is source right multiplication by the same scalar. -/
theorem complexOfRealColumn0_realSectorAction (eta : ℂ)
    (w : I ⊕ I → ℝ) :
    complexOfRealColumn0 (realSectorAction eta w) =
      fun i ↦ complexOfRealColumn0 w i * eta := by
  funext i
  apply Complex.ext
  · simp [complexOfRealColumn0, realSectorAction, Complex.mul_re]
    ring
  · simp [complexOfRealColumn0, realSectorAction, Complex.mul_im]
    ring

/--
Sector-phase equivalence is exactly ordinary complex right-phase equivalence
after decoding the two real sectors.
-/
theorem realSectorPhaseEquivalent_iff_decode_rightPhaseEquivalent
    {x y : I ⊕ I → ℝ} :
    RealSectorPhaseEquivalent x y ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent
        (complexOfRealColumn0 x) (complexOfRealColumn0 y) := by
  constructor
  · rintro ⟨eta, heta, hxy⟩
    refine ⟨eta, heta, ?_⟩
    rw [hxy, complexOfRealColumn0_realSectorAction]
  · rintro ⟨eta, heta, hxy⟩
    refine ⟨eta, heta, ?_⟩
    calc
      x = realColumn0 (complexOfRealColumn0 x) :=
        (realColumn0_complexOfRealColumn0 x).symm
      _ = realColumn0 (fun i ↦ complexOfRealColumn0 y i * eta) :=
        congrArg realColumn0 hxy
      _ = realSectorAction eta (realColumn0 (complexOfRealColumn0 y)) :=
        (realSectorAction_realColumn0 eta (complexOfRealColumn0 y)).symm
      _ = realSectorAction eta y := by rw [realColumn0_complexOfRealColumn0]

/-- First canonical columns share a real sector orbit exactly when sources share phase. -/
theorem realColumn0_phaseEquivalent_iff_rightPhaseEquivalent {w z : I → ℂ} :
    RealSectorPhaseEquivalent (realColumn0 w) (realColumn0 z) ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent w z := by
  simpa using
    (realSectorPhaseEquivalent_iff_decode_rightPhaseEquivalent
      (x := realColumn0 w) (y := realColumn0 z))

/-- Second canonical columns share a real sector orbit exactly when sources share phase. -/
theorem realColumn1_phaseEquivalent_iff_rightPhaseEquivalent {w z : I → ℂ} :
    RealSectorPhaseEquivalent (realColumn1 w) (realColumn1 z) ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent w z := by
  constructor
  · rintro ⟨eta, heta, h⟩
    refine ⟨eta, heta, ?_⟩
    apply realColumn1_injective
    calc
      realColumn1 w = realSectorAction eta (realColumn1 z) := h
      _ = realColumn1 (fun i ↦ z i * eta) :=
        realSectorAction_realColumn1 eta z
  · rintro ⟨eta, heta, rfl⟩
    exact ⟨eta, heta, (realSectorAction_realColumn1 eta z).symm⟩

/-- Normalized first columns share an orbit exactly when their sources share phase. -/
theorem realColumn0State_phaseEquivalent_iff_rightPhaseEquivalent [Fintype I]
    {w z : ComplexState I} :
    RealSectorPhaseEquivalent
        (realColumn0State w : I ⊕ I → ℝ)
        (realColumn0State z : I ⊕ I → ℝ) ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent
        (w : I → ℂ) z :=
  realColumn0_phaseEquivalent_iff_rightPhaseEquivalent

/-- Normalized second columns share an orbit exactly when their sources share phase. -/
theorem realColumn1State_phaseEquivalent_iff_rightPhaseEquivalent [Fintype I]
    {w z : ComplexState I} :
    RealSectorPhaseEquivalent
        (realColumn1State w : I ⊕ I → ℝ)
        (realColumn1State z : I ⊕ I → ℝ) ↔
      QuaternionicComputing.Complex.RightPhaseEquivalent
        (w : I → ℂ) z :=
  realColumn1_phaseEquivalent_iff_rightPhaseEquivalent

/-- Ordinary real global-sign equivalence implies common complex-sector orbit. -/
theorem signEquivalent_realSectorPhaseEquivalent {x y : I ⊕ I → ℝ}
    (hxy : QuaternionicComputing.Real.SignEquivalent x y) :
    RealSectorPhaseEquivalent x y := by
  rcases hxy with ⟨s, hs, rfl⟩
  refine ⟨(s : ℂ), by simpa [Complex.normSq_apply] using hs, ?_⟩
  ext (i | i) <;> simp [realSectorAction] <;> ring

/-! ## Normalized orbit quotient -/

/-- Normalized doubled real states modulo unit-complex sector phase. -/
def realSectorOrbitSetoid (I : Type u) [Fintype I] :
    Setoid (RealState (I ⊕ I)) where
  r x y := RealSectorPhaseEquivalent (x : I ⊕ I → ℝ) y
  iseqv :=
    ⟨fun x ↦ realSectorPhaseEquivalent_refl (x : I ⊕ I → ℝ),
      fun h ↦ realSectorPhaseEquivalent_symm h,
      fun hxy hyz ↦ realSectorPhaseEquivalent_trans hxy hyz⟩

/-- A normalized doubled-real state modulo unit-complex sector rotations. -/
def RealSectorOrbit (I : Type u) [Fintype I] :=
  Quotient (realSectorOrbitSetoid I)

namespace RealSectorOrbit

variable [Fintype I]

/-- Send a normalized doubled real representative to its sector orbit. -/
def mk (w : RealState (I ⊕ I)) : RealSectorOrbit I :=
  Quotient.mk (realSectorOrbitSetoid I) w

/-- Constructor equality is exactly unit-sector-phase equivalence. -/
@[simp]
theorem mk_eq_mk_iff {x y : RealState (I ⊕ I)} :
    mk x = mk y ↔
      RealSectorPhaseEquivalent (x : I ⊕ I → ℝ) y :=
  Quotient.eq

/-- Every real sector orbit has a normalized representative. -/
theorem exists_rep (r : RealSectorOrbit I) :
    ∃ w : RealState (I ⊕ I), mk w = r := by
  change Quotient (realSectorOrbitSetoid I) at r
  exact Quotient.exists_rep r

/-- Prove a proposition on real sector orbits by normalized representatives. -/
@[elab_as_elim]
theorem inductionOn {motive : RealSectorOrbit I → Prop}
    (r : RealSectorOrbit I)
    (h : ∀ w : RealState (I ⊕ I), motive (mk w)) : motive r :=
  Quotient.inductionOn r h

/-- Descend a sector-phase-invariant function to normalized real sector orbits. -/
def lift {B : Sort v} (f : RealState (I ⊕ I) → B)
    (h : ∀ (x y : RealState (I ⊕ I)),
      RealSectorPhaseEquivalent (x : I ⊕ I → ℝ) y → f x = f y) :
    RealSectorOrbit I → B :=
  Quotient.lift f h

/-- A descended function computes on an orbit constructor. -/
@[simp]
theorem lift_mk {B : Sort v} (f : RealState (I ⊕ I) → B)
    (h : ∀ (x y : RealState (I ⊕ I)),
      RealSectorPhaseEquivalent (x : I ⊕ I → ℝ) y → f x = f y)
    (w : RealState (I ⊕ I)) :
    lift f h (mk w) = f w :=
  rfl

/-- Functions from real sector orbits agree if they agree on every constructor. -/
theorem function_ext {B : Sort v} {f g : RealSectorOrbit I → B}
    (h : ∀ w : RealState (I ⊕ I), f (mk w) = g (mk w)) : f = g := by
  funext r
  exact inductionOn r h

end RealSectorOrbit

/-! ## Normalized decoder and representative equivalence -/

/-- Decode a normalized doubled real state as a normalized complex state. -/
def complexStateOfRealColumn0 [Fintype I]
    (w : RealState (I ⊕ I)) : ComplexState I :=
  ⟨complexOfRealColumn0 w, by
    have h := realTotalWeight_realColumn0
      (complexOfRealColumn0 (w : I ⊕ I → ℝ))
    rw [realColumn0_complexOfRealColumn0] at h
    exact h.symm.trans w.property⟩

/-- Decoding a normalized first column returns its source state. -/
@[simp]
theorem complexStateOfRealColumn0_realColumn0State [Fintype I]
    (w : ComplexState I) :
    complexStateOfRealColumn0 (realColumn0State w) = w := by
  apply Subtype.ext
  exact complexOfRealColumn0_realColumn0 w

/-- Re-encoding a decoded normalized doubled real state returns the state. -/
@[simp]
theorem realColumn0State_complexStateOfRealColumn0 [Fintype I]
    (w : RealState (I ⊕ I)) :
    realColumn0State (complexStateOfRealColumn0 w) = w := by
  apply Subtype.ext
  exact realColumn0_complexOfRealColumn0 w

/-- First-column realification is an equivalence of normalized representatives. -/
def realColumn0StateEquiv [Fintype I] :
    ComplexState I ≃ RealState (I ⊕ I) where
  toFun := realColumn0State
  invFun := complexStateOfRealColumn0
  left_inv := complexStateOfRealColumn0_realColumn0State
  right_inv := realColumn0State_complexStateOfRealColumn0

/-! ## Exact equivalence between complex rays and real sector orbits -/

namespace ComplexRay

variable [Fintype I]

/-- Realify a complex ray into its well-defined normalized sector orbit. -/
def realificationOrbit (r : ComplexRay I) : RealSectorOrbit I :=
  lift (fun w ↦ RealSectorOrbit.mk (realColumn0State w))
    (fun _ _ h ↦ RealSectorOrbit.mk_eq_mk_iff.mpr
      (realColumn0State_phaseEquivalent_iff_rightPhaseEquivalent.mpr h)) r

/-- Ray realification computes by first-column realification on representatives. -/
@[simp]
theorem realificationOrbit_mk (w : ComplexState I) :
    realificationOrbit (mk w) = RealSectorOrbit.mk (realColumn0State w) :=
  rfl

end ComplexRay

namespace RealSectorOrbit

variable [Fintype I]

/-- Decode a normalized real sector orbit back to its complex ray. -/
def toComplexRay (r : RealSectorOrbit I) : ComplexRay I :=
  lift (fun w ↦ ComplexRay.mk (complexStateOfRealColumn0 w))
    (fun _ _ h ↦ ComplexRay.mk_eq_mk_iff.mpr
      (realSectorPhaseEquivalent_iff_decode_rightPhaseEquivalent.mp h)) r

/-- Orbit decoding computes by normalized complex decoding on representatives. -/
@[simp]
theorem toComplexRay_mk (w : RealState (I ⊕ I)) :
    toComplexRay (mk w) = ComplexRay.mk (complexStateOfRealColumn0 w) :=
  rfl

/-- Decoding a realified complex ray returns the source complex ray. -/
@[simp]
theorem toComplexRay_realificationOrbit (r : ComplexRay I) :
    toComplexRay (ComplexRay.realificationOrbit r) = r := by
  refine ComplexRay.inductionOn r ?_
  intro w
  simp

end RealSectorOrbit

namespace ComplexRay

variable [Fintype I]

/-- Realifying a decoded sector orbit returns the original orbit. -/
@[simp]
theorem realificationOrbit_toComplexRay (r : RealSectorOrbit I) :
    realificationOrbit (RealSectorOrbit.toComplexRay r) = r := by
  refine RealSectorOrbit.inductionOn r ?_
  intro w
  simp

end ComplexRay

/-- Complex rays are exactly normalized doubled-real unit-sector-phase orbits. -/
def complexRayEquivRealSectorOrbit [Fintype I] :
    ComplexRay I ≃ RealSectorOrbit I where
  toFun := ComplexRay.realificationOrbit
  invFun := RealSectorOrbit.toComplexRay
  left_inv := RealSectorOrbit.toComplexRay_realificationOrbit
  right_inv := ComplexRay.realificationOrbit_toComplexRay

namespace ComplexRay

variable [Fintype I]

/-- Realification into sector orbits is injective. -/
theorem realificationOrbit_injective :
    Function.Injective (realificationOrbit : ComplexRay I → RealSectorOrbit I) :=
  (complexRayEquivRealSectorOrbit (I := I)).injective

/-- Realification is a bijection from complex rays onto normalized sector orbits. -/
theorem realificationOrbit_bijective :
    Function.Bijective (realificationOrbit : ComplexRay I → RealSectorOrbit I) :=
  (complexRayEquivRealSectorOrbit (I := I)).bijective

/-! ## Alternative-column and arbitrary-top consumers -/

/-- The second canonical normalized column belongs to the same orbit as the first. -/
theorem realificationOrbit_mk_eq_realColumn1State (w : ComplexState I) :
    realificationOrbit (mk w) = RealSectorOrbit.mk (realColumn1State w) := by
  rw [realificationOrbit_mk, RealSectorOrbit.mk_eq_mk_iff]
  refine ⟨Complex.I, by simp [Complex.normSq_apply], ?_⟩
  ext (i | i) <;>
    simp [realSectorAction, realColumn0, realColumn1]

end ComplexRay

/-- Every normalized real top state over a source lies in its first-column orbit. -/
theorem realTopState_phaseEquivalent_realColumn0State [Fintype I]
    (top : Rebit) (w : ComplexState I) :
    RealSectorPhaseEquivalent
      (realTopState top w : I ⊕ I → ℝ)
      (realColumn0State w : I ⊕ I → ℝ) := by
  let eta : ℂ := ⟨top false, -top true⟩
  have heta : Complex.normSq eta = 1 := by
    dsimp [eta]
    simpa [Complex.normSq_apply, realWeight] using Rebit.normalization top
  refine ⟨eta, heta, ?_⟩
  ext (i | i) <;>
    simp [eta, realTopState, realTopCombinationState, realTopCombination,
      realSectorAction] ; ring

namespace ComplexRay

variable [Fintype I]

/-- Every normalized real top-state encoding represents the source complex ray orbit. -/
theorem realificationOrbit_mk_eq_realTopState
    (top : Rebit) (w : ComplexState I) :
    realificationOrbit (mk w) = RealSectorOrbit.mk (realTopState top w) := by
  rw [realificationOrbit_mk, RealSectorOrbit.mk_eq_mk_iff]
  exact realSectorPhaseEquivalent_symm
    (realTopState_phaseEquivalent_realColumn0State top w)

end ComplexRay

end QuaternionicComputing.State
