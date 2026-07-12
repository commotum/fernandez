module

public import QuaternionicComputing.Semantics.Approximation.Operator
public import QuaternionicComputing.Semantics.Approximation.Quaternion
public import QuaternionicComputing.Semantics.StatePhase

/-!
# Approximation of finite pure-state columns and rays

This leaf gives finite amplitude columns their Euclidean L2 distance and
defines additive error-budget relations both before and up to a unit scalar on
the right.  These remain predicates on normalized representatives rather than
relations descended to the quotient ray types.  Right multiplication is
essential for quaternionic states.  In a composite phase witness, the later
phase therefore occurs on the left of the earlier phase.

The normalized real, complex, and quaternionic relations recover the existing
exact state-phase relations at budget zero.  Operator error also bounds the L2
output-column error on normalized inputs, without requiring either operator
to be unitary.  No statement here identifies close representatives, compares
channels, or turns an amplitude bound directly into a probability claim.
-/

@[expose] public noncomputable section

open WithLp
open scoped BigOperators Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Finite Euclidean column distance -/

/-- Euclidean L2 distance between two finite columns over a normed additive group. -/
def columnL2Distance {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (x y : I → R) : ℝ :=
  dist (toLp 2 x : PiLp 2 (fun _ : I ↦ R)) (toLp 2 y)

/-- Two finite columns are within the supplied Euclidean L2 error budget. -/
def ColumnClose {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I]
    (epsilon : ℝ) (x y : I → R) : Prop :=
  columnL2Distance x y ≤ epsilon

/-- Every finite column has L2 distance zero from itself. -/
@[simp]
theorem columnL2Distance_self {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (x : I → R) :
    columnL2Distance x x = 0 :=
  dist_self _

/-- Finite-column L2 distance is nonnegative. -/
theorem columnL2Distance_nonneg {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (x y : I → R) :
    0 ≤ columnL2Distance x y :=
  dist_nonneg

/-- Finite-column L2 distance is symmetric. -/
theorem columnL2Distance_symm {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (x y : I → R) :
    columnL2Distance x y = columnL2Distance y x :=
  dist_comm _ _

/-- Finite-column L2 distance satisfies the triangle inequality. -/
theorem columnL2Distance_triangle {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (x y z : I → R) :
    columnL2Distance x z ≤
      columnL2Distance x y + columnL2Distance y z :=
  dist_triangle _ _ _

/-- Finite-column L2 distance vanishes exactly at literal column equality. -/
@[simp]
theorem columnL2Distance_eq_zero_iff {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {x y : I → R} :
    columnL2Distance x y = 0 ↔ x = y := by
  rw [columnL2Distance, dist_eq_zero]
  constructor
  · exact fun h ↦ congrArg WithLp.ofLp h
  · rintro rfl
    rfl

namespace ColumnClose

/-- Column closeness is reflexive at every nonnegative budget. -/
theorem refl {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (x : I → R) :
    ColumnClose epsilon x x := by
  simpa [ColumnClose] using hepsilon

/-- Increasing a column-error budget preserves closeness. -/
theorem mono {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {epsilon delta : ℝ} {x y : I → R}
    (h : ColumnClose epsilon x y) (hbudget : epsilon ≤ delta) :
    ColumnClose delta x y :=
  h.trans hbudget

/-- Column closeness is symmetric at a fixed budget. -/
theorem symm {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {epsilon : ℝ} {x y : I → R}
    (h : ColumnClose epsilon x y) : ColumnClose epsilon y x := by
  simpa [ColumnClose, columnL2Distance_symm] using h

/-- Chaining column comparisons adds their error budgets. -/
theorem additive_trans {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {epsilon delta : ℝ} {x y z : I → R}
    (hxy : ColumnClose epsilon x y) (hyz : ColumnClose delta y z) :
    ColumnClose (epsilon + delta) x z :=
  (columnL2Distance_triangle x y z).trans (add_le_add hxy hyz)

/-- Zero-budget column closeness is literal equality. -/
@[simp]
theorem zero_iff_eq {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] {x y : I → R} :
    ColumnClose 0 x y ↔ x = y := by
  constructor
  · intro h
    exact columnL2Distance_eq_zero_iff.mp
      (le_antisymm h (columnL2Distance_nonneg x y))
  · rintro rfl
    exact refl le_rfl x

end ColumnClose

/-! ## Approximation up to a unit scalar on the right -/

/--
Simultaneous right multiplication by a unit scalar preserves finite-column L2
distance.  This holds without commutativity of the scalar ring.
-/
theorem columnL2Distance_right_mul
    {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I]
    (x y : I → R) (eta : R) (heta : ‖eta‖ = 1) :
    columnL2Distance (fun i ↦ x i * eta) (fun i ↦ y i * eta) =
      columnL2Distance x y := by
  apply (sq_eq_sq₀ (columnL2Distance_nonneg _ _)
    (columnL2Distance_nonneg _ _)).mp
  rw [columnL2Distance, columnL2Distance,
    PiLp.dist_sq_eq_of_L2, PiLp.dist_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [dist_eq_norm, ← sub_mul, norm_mul, heta]

/--
Budgeted finite-column approximation up to one unit scalar on the right.
The scalar witness acts on every coordinate uniformly.
-/
def RightUnitPhaseColumnClose
    {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I]
    (epsilon : ℝ) (x y : I → R) : Prop :=
  ∃ eta : R, ‖eta‖ = 1 ∧
    ColumnClose epsilon x (fun i ↦ y i * eta)

namespace RightUnitPhaseColumnClose

/-- Right-unit-phase column closeness is reflexive at nonnegative budgets. -/
theorem refl {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (x : I → R) :
    RightUnitPhaseColumnClose epsilon x x := by
  refine ⟨1, norm_one, ?_⟩
  simpa using ColumnClose.refl hepsilon x

/-- Increasing the error budget preserves right-unit-phase closeness. -/
theorem mono {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] {epsilon delta : ℝ} {x y : I → R}
    (h : RightUnitPhaseColumnClose epsilon x y)
    (hbudget : epsilon ≤ delta) :
    RightUnitPhaseColumnClose delta x y := by
  rcases h with ⟨eta, heta, hclose⟩
  exact ⟨eta, heta, hclose.mono hbudget⟩

/-- Right-unit-phase column closeness is symmetric at a fixed budget. -/
theorem symm {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] {epsilon : ℝ} {x y : I → R}
    (h : RightUnitPhaseColumnClose epsilon x y) :
    RightUnitPhaseColumnClose epsilon y x := by
  rcases h with ⟨eta, heta, hclose⟩
  have heta0 : eta ≠ 0 := by
    intro hzero
    subst eta
    simp at heta
  refine ⟨eta⁻¹, by simp [heta], ?_⟩
  have hcancel : (fun i ↦ (x i * eta⁻¹) * eta) = x := by
    funext i
    rw [mul_assoc, inv_mul_cancel₀ heta0, mul_one]
  calc
    columnL2Distance y (fun i ↦ x i * eta⁻¹) =
        columnL2Distance (fun i ↦ y i * eta)
          (fun i ↦ (x i * eta⁻¹) * eta) := by
      symm
      exact columnL2Distance_right_mul y (fun i ↦ x i * eta⁻¹) eta heta
    _ = columnL2Distance (fun i ↦ y i * eta) x := by rw [hcancel]
    _ = columnL2Distance x (fun i ↦ y i * eta) :=
      columnL2Distance_symm _ _
    _ ≤ epsilon := hclose

/--
Chaining right-unit-phase comparisons adds budgets.  If the first witness is
`eta` and the second is `theta`, the composite witness is `theta * eta`; this
order is required for noncommutative scalars.
-/
theorem additive_trans {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] {epsilon delta : ℝ} {x y z : I → R}
    (hxy : RightUnitPhaseColumnClose epsilon x y)
    (hyz : RightUnitPhaseColumnClose delta y z) :
    RightUnitPhaseColumnClose (epsilon + delta) x z := by
  rcases hxy with ⟨eta, heta, hxy⟩
  rcases hyz with ⟨theta, htheta, hyz⟩
  refine ⟨theta * eta, by rw [norm_mul, htheta, heta, one_mul], ?_⟩
  have hphase : (fun i ↦ z i * (theta * eta)) =
      fun i ↦ (z i * theta) * eta := by
    funext i
    rw [mul_assoc]
  rw [hphase]
  exact (columnL2Distance_triangle x (fun i ↦ y i * eta)
    (fun i ↦ (z i * theta) * eta)).trans
      (add_le_add hxy
        ((columnL2Distance_right_mul y
          (fun i ↦ z i * theta) eta heta).le.trans hyz))

/--
Zero-budget right-unit-phase closeness is exact equality after one unit scalar
on the right.
-/
@[simp]
theorem zero_iff {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] {x y : I → R} :
    RightUnitPhaseColumnClose 0 x y ↔
      ∃ eta : R, ‖eta‖ = 1 ∧ x = fun i ↦ y i * eta := by
  constructor
  · rintro ⟨eta, heta, hclose⟩
    exact ⟨eta, heta, ColumnClose.zero_iff_eq.mp hclose⟩
  · rintro ⟨eta, heta, hxy⟩
    exact ⟨eta, heta, ColumnClose.zero_iff_eq.mpr hxy⟩

end RightUnitPhaseColumnClose

/-! ## Normalized state-ray approximation -/

/-- A normalized real state is close up to one unit sign on the right. -/
def RealStateRayClose {I : Type u} [Fintype I]
    (epsilon : ℝ) (a b : State.RealState I) : Prop :=
  RightUnitPhaseColumnClose epsilon (a : I → ℝ) b

/-- A normalized complex state is close up to one unit phase on the right. -/
def ComplexStateRayClose {I : Type u} [Fintype I]
    (epsilon : ℝ) (a b : State.ComplexState I) : Prop :=
  RightUnitPhaseColumnClose epsilon (a : I → ℂ) b

/-- A normalized quaternionic state is close up to one unit right phase. -/
def QuaternionStateRayClose {I : Type u} [Fintype I]
    (epsilon : ℝ) (a b : State.QuaternionState I) : Prop :=
  RightUnitPhaseColumnClose epsilon (a : I → ℍ[ℝ]) b

namespace RealStateRayClose

/-- Real state-ray closeness is reflexive at nonnegative budgets. -/
theorem refl {I : Type u} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (a : State.RealState I) :
    RealStateRayClose epsilon a a :=
  RightUnitPhaseColumnClose.refl hepsilon a

/-- Increasing the budget preserves real state-ray closeness. -/
theorem mono {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b : State.RealState I} (h : RealStateRayClose epsilon a b)
    (hbudget : epsilon ≤ delta) : RealStateRayClose delta a b :=
  RightUnitPhaseColumnClose.mono h hbudget

/-- Real state-ray closeness is symmetric at a fixed budget. -/
theorem symm {I : Type u} [Fintype I] {epsilon : ℝ}
    {a b : State.RealState I} (h : RealStateRayClose epsilon a b) :
    RealStateRayClose epsilon b a :=
  RightUnitPhaseColumnClose.symm h

/-- Chaining real state-ray comparisons adds their budgets. -/
theorem additive_trans {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b c : State.RealState I} (hab : RealStateRayClose epsilon a b)
    (hbc : RealStateRayClose delta b c) :
    RealStateRayClose (epsilon + delta) a c :=
  RightUnitPhaseColumnClose.additive_trans hab hbc

end RealStateRayClose

namespace ComplexStateRayClose

/-- Complex state-ray closeness is reflexive at nonnegative budgets. -/
theorem refl {I : Type u} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (a : State.ComplexState I) :
    ComplexStateRayClose epsilon a a :=
  RightUnitPhaseColumnClose.refl hepsilon a

/-- Increasing the budget preserves complex state-ray closeness. -/
theorem mono {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b : State.ComplexState I} (h : ComplexStateRayClose epsilon a b)
    (hbudget : epsilon ≤ delta) : ComplexStateRayClose delta a b :=
  RightUnitPhaseColumnClose.mono h hbudget

/-- Complex state-ray closeness is symmetric at a fixed budget. -/
theorem symm {I : Type u} [Fintype I] {epsilon : ℝ}
    {a b : State.ComplexState I} (h : ComplexStateRayClose epsilon a b) :
    ComplexStateRayClose epsilon b a :=
  RightUnitPhaseColumnClose.symm h

/-- Chaining complex state-ray comparisons adds their budgets. -/
theorem additive_trans {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b c : State.ComplexState I} (hab : ComplexStateRayClose epsilon a b)
    (hbc : ComplexStateRayClose delta b c) :
    ComplexStateRayClose (epsilon + delta) a c :=
  RightUnitPhaseColumnClose.additive_trans hab hbc

end ComplexStateRayClose

namespace QuaternionStateRayClose

/-- Quaternionic state-ray closeness is reflexive at nonnegative budgets. -/
theorem refl {I : Type u} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (a : State.QuaternionState I) :
    QuaternionStateRayClose epsilon a a :=
  RightUnitPhaseColumnClose.refl hepsilon a

/-- Increasing the budget preserves quaternionic state-ray closeness. -/
theorem mono {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b : State.QuaternionState I} (h : QuaternionStateRayClose epsilon a b)
    (hbudget : epsilon ≤ delta) : QuaternionStateRayClose delta a b :=
  RightUnitPhaseColumnClose.mono h hbudget

/-- Quaternionic state-ray closeness is symmetric at a fixed budget. -/
theorem symm {I : Type u} [Fintype I] {epsilon : ℝ}
    {a b : State.QuaternionState I} (h : QuaternionStateRayClose epsilon a b) :
    QuaternionStateRayClose epsilon b a :=
  RightUnitPhaseColumnClose.symm h

/--
Chaining quaternionic state-ray comparisons adds budgets and retains the
noncommutative right-phase order from `RightUnitPhaseColumnClose`.
-/
theorem additive_trans {I : Type u} [Fintype I] {epsilon delta : ℝ}
    {a b c : State.QuaternionState I}
    (hab : QuaternionStateRayClose epsilon a b)
    (hbc : QuaternionStateRayClose delta b c) :
    QuaternionStateRayClose (epsilon + delta) a c :=
  RightUnitPhaseColumnClose.additive_trans hab hbc

end QuaternionStateRayClose

private theorem real_norm_eq_one_iff_sq_eq_one (s : ℝ) :
    ‖s‖ = 1 ↔ s * s = 1 := by
  constructor
  · intro h
    rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs s]
  · intro h
    rcases Real.sign_sq_eq_one_iff.mp h with rfl | rfl <;> norm_num

private theorem complex_norm_eq_one_iff_normSq_eq_one (eta : ℂ) :
    ‖eta‖ = 1 ↔ Complex.normSq eta = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    nlinarith [norm_nonneg eta]

private theorem quaternion_norm_eq_one_iff_normSq_eq_one (eta : ℍ[ℝ]) :
    ‖eta‖ = 1 ↔ _root_.Quaternion.normSq eta = 1 := by
  rw [_root_.Quaternion.normSq_eq_norm_mul_self]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    nlinarith [norm_nonneg eta]

/-- Zero-budget real state-ray closeness is existing exact real sign equality. -/
@[simp]
theorem realStateRayClose_zero_iff_realStatePhaseEq
    {I : Type u} [Fintype I] {a b : State.RealState I} :
    RealStateRayClose 0 a b ↔ RealStatePhaseEq a b := by
  rw [RealStateRayClose, RightUnitPhaseColumnClose.zero_iff]
  constructor
  · rintro ⟨s, hs, hab⟩
    exact ⟨s, (real_norm_eq_one_iff_sq_eq_one s).mp hs, hab⟩
  · rintro ⟨s, hs, hab⟩
    exact ⟨s, (real_norm_eq_one_iff_sq_eq_one s).mpr hs, hab⟩

/-- Zero-budget complex state-ray closeness is existing exact right-phase equality. -/
@[simp]
theorem complexStateRayClose_zero_iff_complexStatePhaseEq
    {I : Type u} [Fintype I] {a b : State.ComplexState I} :
    ComplexStateRayClose 0 a b ↔ ComplexStatePhaseEq a b := by
  rw [ComplexStateRayClose, RightUnitPhaseColumnClose.zero_iff]
  constructor
  · rintro ⟨eta, heta, hab⟩
    exact ⟨eta, (complex_norm_eq_one_iff_normSq_eq_one eta).mp heta, hab⟩
  · rintro ⟨eta, heta, hab⟩
    exact ⟨eta, (complex_norm_eq_one_iff_normSq_eq_one eta).mpr heta, hab⟩

/--
Zero-budget quaternionic state-ray closeness is existing exact right-phase
equality, with the phase retained on the right.
-/
@[simp]
theorem quaternionStateRayClose_zero_iff_quaternionStatePhaseEq
    {I : Type u} [Fintype I] {a b : State.QuaternionState I} :
    QuaternionStateRayClose 0 a b ↔ QuaternionStatePhaseEq a b := by
  rw [QuaternionStateRayClose, RightUnitPhaseColumnClose.zero_iff]
  constructor
  · rintro ⟨eta, heta, hab⟩
    exact ⟨eta, (quaternion_norm_eq_one_iff_normSq_eq_one eta).mp heta, hab⟩
  · rintro ⟨eta, heta, hab⟩
    exact ⟨eta, (quaternion_norm_eq_one_iff_normSq_eq_one eta).mpr heta, hab⟩

/-! ## Normalized input and output-column bounds -/

/-- Every normalized finite real state has Euclidean L2 norm one. -/
theorem realState_l2Norm_eq_one {I : Type u} [Fintype I]
    (psi : State.RealState I) :
    ‖toLp 2 (psi : I → ℝ)‖ = 1 := by
  have hsquare : ‖toLp 2 (psi : I → ℝ)‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [State.realTotalWeight, State.totalWeight, State.basisWeight,
      State.realWeight, pow_two] using psi.property
  nlinarith [norm_nonneg (toLp 2 (psi : I → ℝ))]

/-- Every normalized finite complex state has Euclidean L2 norm one. -/
theorem complexState_l2Norm_eq_one {I : Type u} [Fintype I]
    (psi : State.ComplexState I) :
    ‖toLp 2 (psi : I → ℂ)‖ = 1 := by
  have hsquare : ‖toLp 2 (psi : I → ℂ)‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, Complex.normSq_eq_norm_sq] using psi.property
  nlinarith [norm_nonneg (toLp 2 (psi : I → ℂ))]

/-- Every normalized finite quaternionic state has Euclidean L2 norm one. -/
theorem quaternionState_l2Norm_eq_one {I : Type u} [Fintype I]
    (psi : State.QuaternionState I) :
    ‖toLp 2 (psi : I → ℍ[ℝ])‖ = 1 := by
  have hsquare : ‖toLp 2 (psi : I → ℍ[ℝ])‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [State.quaternionTotalWeight, State.totalWeight, State.basisWeight,
      State.quaternionWeight, _root_.Quaternion.normSq_eq_norm_mul_self,
      pow_two] using psi.property
  nlinarith [norm_nonneg (toLp 2 (psi : I → ℍ[ℝ]))]

/--
Real operator distance bounds output-column L2 error on every normalized real
input.  The matrices may be rectangular and need not be unitary.
-/
theorem operatorDistance_realState_output_le
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (U V : Matrix O I ℝ) (psi : State.RealState I) :
    columnL2Distance (U *ᵥ (psi : I → ℝ))
      (V *ᵥ (psi : I → ℝ)) ≤ operatorDistance U V := by
  rw [columnL2Distance]
  simpa [realState_l2Norm_eq_one] using
    operatorDistance_mulVec_le U V (psi : I → ℝ)

/--
Complex operator distance bounds output-column L2 error on every normalized
complex input.  The matrices may be rectangular and need not be unitary.
-/
theorem operatorDistance_complexState_output_le
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (U V : Matrix O I ℂ) (psi : State.ComplexState I) :
    columnL2Distance (U *ᵥ (psi : I → ℂ))
      (V *ᵥ (psi : I → ℂ)) ≤ operatorDistance U V := by
  rw [columnL2Distance]
  simpa [complexState_l2Norm_eq_one] using
    operatorDistance_mulVec_le U V (psi : I → ℂ)

/--
Native quaternionic operator distance bounds output-column L2 error on every
normalized quaternionic input.  The matrices may be rectangular and need not
be unitary.
-/
theorem quaternionOperatorDistance_quaternionState_output_le
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (U V : Matrix O I ℍ[ℝ]) (psi : State.QuaternionState I) :
    columnL2Distance (U *ᵥ (psi : I → ℍ[ℝ]))
      (V *ᵥ (psi : I → ℍ[ℝ])) ≤
        quaternionOperatorDistance U V := by
  simpa [columnL2Distance, dist_eq_norm, WithLp.toLp_sub,
    quaternionState_l2Norm_eq_one] using
      quaternionOperatorDistance_mulVec U V (psi : I → ℍ[ℝ])

end QuaternionicComputing.Semantics
