module

public import QuaternionicComputing.State.Distribution

/-!
# Approximation of finite classical distributions

This leaf defines total-variation distance on the library's finite probability
distributions using the standard half-L1 convention.  It proves the metric
laws, the corresponding additive-budget laws, the sharp bound on every finite
event, and contraction under deterministic classical postprocessing.

These declarations concern already packaged classical distributions.  They do
not state a trace-distance, quantum-channel, randomized-postprocessing,
finite-precision, or runtime result.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.Semantics

universe u v

/-- Half the L1 distance between the weights of two finite distributions. -/
def totalVariationDistance {I : Type u} [Fintype I]
    (mu nu : State.FiniteDistribution I) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |mu.weight i - nu.weight i|

/-- A budgeted total-variation comparison of two finite distributions. -/
def DistributionClose {I : Type u} [Fintype I]
    (epsilon : ℝ) (mu nu : State.FiniteDistribution I) : Prop :=
  totalVariationDistance mu nu ≤ epsilon

/-- A finite distribution has total-variation distance zero from itself. -/
@[simp]
theorem totalVariationDistance_self {I : Type u} [Fintype I]
    (mu : State.FiniteDistribution I) :
    totalVariationDistance mu mu = 0 := by
  simp [totalVariationDistance]

/-- Total-variation distance is nonnegative. -/
theorem totalVariationDistance_nonneg {I : Type u} [Fintype I]
    (mu nu : State.FiniteDistribution I) :
    0 ≤ totalVariationDistance mu nu := by
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- Total-variation distance is symmetric. -/
theorem totalVariationDistance_symm {I : Type u} [Fintype I]
    (mu nu : State.FiniteDistribution I) :
    totalVariationDistance mu nu = totalVariationDistance nu mu := by
  unfold totalVariationDistance
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact abs_sub_comm _ _

/-- Total-variation distance satisfies the triangle inequality. -/
theorem totalVariationDistance_triangle {I : Type u} [Fintype I]
    (mu nu xi : State.FiniteDistribution I) :
    totalVariationDistance mu xi ≤
      totalVariationDistance mu nu + totalVariationDistance nu xi := by
  unfold totalVariationDistance
  rw [← mul_add]
  gcongr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ abs_sub_le _ _ _

/-- Total-variation distance is zero exactly for equal finite distributions. -/
@[simp]
theorem totalVariationDistance_eq_zero_iff
    {I : Type u} [Fintype I] {mu nu : State.FiniteDistribution I} :
    totalVariationDistance mu nu = 0 ↔ mu = nu := by
  constructor
  · intro h
    have hsum : (∑ i, |mu.weight i - nu.weight i|) = 0 := by
      have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left hhalf
    apply State.FiniteDistribution.ext
    intro i
    have hi : |mu.weight i - nu.weight i| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ abs_nonneg (mu.weight j - nu.weight j))).mp hsum
        i (Finset.mem_univ i)
    exact sub_eq_zero.mp (abs_eq_zero.mp hi)
  · rintro rfl
    exact totalVariationDistance_self mu

namespace DistributionClose

/-- Closeness is reflexive at every nonnegative budget. -/
theorem refl {I : Type u} [Fintype I] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (mu : State.FiniteDistribution I) :
    DistributionClose epsilon mu mu := by
  simpa [DistributionClose] using hepsilon

/-- A valid closeness bound remains valid after increasing the budget. -/
theorem mono {I : Type u} [Fintype I]
    {epsilon delta : ℝ} {mu nu : State.FiniteDistribution I}
    (h : DistributionClose epsilon mu nu) (hbound : epsilon ≤ delta) :
    DistributionClose delta mu nu :=
  h.trans hbound

/-- Closeness is symmetric at a fixed budget. -/
theorem symm {I : Type u} [Fintype I]
    {epsilon : ℝ} {mu nu : State.FiniteDistribution I}
    (h : DistributionClose epsilon mu nu) :
    DistributionClose epsilon nu mu := by
  change totalVariationDistance nu mu ≤ epsilon
  rw [totalVariationDistance_symm nu mu]
  exact h

/-- Chaining two comparisons adds their error budgets. -/
theorem additive_trans {I : Type u} [Fintype I]
    {epsilon delta : ℝ} {mu nu xi : State.FiniteDistribution I}
    (hmunu : DistributionClose epsilon mu nu)
    (hnuxi : DistributionClose delta nu xi) :
    DistributionClose (epsilon + delta) mu xi :=
  (totalVariationDistance_triangle mu nu xi).trans
    (add_le_add hmunu hnuxi)

end DistributionClose

/-- Zero-budget distribution closeness is literal distribution equality. -/
@[simp]
theorem distributionClose_zero_iff {I : Type u} [Fintype I]
    {mu nu : State.FiniteDistribution I} :
    DistributionClose 0 mu nu ↔ mu = nu := by
  constructor
  · intro h
    exact totalVariationDistance_eq_zero_iff.mp
      (le_antisymm h (totalVariationDistance_nonneg mu nu))
  · rintro rfl
    exact DistributionClose.refl le_rfl mu

/-- The total-variation distance between finite distributions is at most one. -/
theorem totalVariationDistance_le_one {I : Type u} [Fintype I]
    (mu nu : State.FiniteDistribution I) :
    totalVariationDistance mu nu ≤ 1 := by
  calc
    totalVariationDistance mu nu ≤
        (1 / 2 : ℝ) * ∑ i, (mu.weight i + nu.weight i) := by
      unfold totalVariationDistance
      gcongr with i
      rw [abs_le]
      constructor <;> linarith [mu.nonnegative i, nu.nonnegative i]
    _ = 1 := by
      rw [Finset.sum_add_distrib, mu.normalized, nu.normalized]
      norm_num

private theorem abs_event_sum_le_half_sum_abs
    {I : Type u} [Fintype I] (d : I → ℝ)
    (hzero : (∑ i, d i) = 0) (event : Finset I) :
    |∑ i ∈ event, d i| ≤ (1 / 2 : ℝ) * ∑ i, |d i| := by
  classical
  have hparts :
      (∑ i ∈ event, d i) + (∑ i ∈ eventᶜ, d i) = 0 := by
    rw [Finset.sum_add_sum_compl]
    exact hzero
  have hcomp :
      (∑ i ∈ eventᶜ, d i) = -(∑ i ∈ event, d i) := by
    linarith
  have hevent :
      |∑ i ∈ event, d i| ≤ ∑ i ∈ event, |d i| :=
    Finset.abs_sum_le_sum_abs d event
  have hcomplement :
      |∑ i ∈ eventᶜ, d i| ≤ ∑ i ∈ eventᶜ, |d i| :=
    Finset.abs_sum_le_sum_abs d eventᶜ
  have hdouble :
      2 * |∑ i ∈ event, d i| ≤ ∑ i, |d i| := by
    calc
      2 * |∑ i ∈ event, d i| =
          |∑ i ∈ event, d i| + |∑ i ∈ eventᶜ, d i| := by
        rw [hcomp, abs_neg]
        ring
      _ ≤ (∑ i ∈ event, |d i|) + (∑ i ∈ eventᶜ, |d i|) :=
        add_le_add hevent hcomplement
      _ = ∑ i, |d i| := Finset.sum_add_sum_compl event _
  nlinarith

/-- Every finite-event probability difference is bounded sharply by TV distance. -/
theorem abs_eventWeight_sub_le_totalVariationDistance
    {I : Type u} [Fintype I] (mu nu : State.FiniteDistribution I)
    (event : Finset I) :
    |mu.eventWeight event - nu.eventWeight event| ≤
      totalVariationDistance mu nu := by
  have hzero : (∑ i, (mu.weight i - nu.weight i)) = 0 := by
    rw [Finset.sum_sub_distrib, mu.normalized, nu.normalized]
    norm_num
  have h := abs_event_sum_le_half_sum_abs
    (fun i ↦ mu.weight i - nu.weight i) hzero event
  simpa [State.FiniteDistribution.eventWeight, Finset.sum_sub_distrib,
    totalVariationDistance] using h

/-- Every single-outcome probability difference is bounded sharply by TV distance. -/
theorem abs_weight_sub_le_totalVariationDistance
    {I : Type u} [Fintype I] (mu nu : State.FiniteDistribution I) (i : I) :
    |mu.weight i - nu.weight i| ≤ totalVariationDistance mu nu := by
  simpa [State.FiniteDistribution.eventWeight] using
    abs_eventWeight_sub_le_totalVariationDistance mu nu ({i} : Finset I)

/-- Deterministic classical postprocessing cannot increase TV distance. -/
theorem totalVariationDistance_pushforward_le
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (mu nu : State.FiniteDistribution I) (f : I → J) :
    totalVariationDistance (mu.pushforward f) (nu.pushforward f) ≤
      totalVariationDistance mu nu := by
  classical
  unfold totalVariationDistance
  gcongr
  calc
    (∑ j : J,
        |(mu.pushforward f).weight j - (nu.pushforward f).weight j|) =
        ∑ j : J, |∑ i with f i = j, (mu.weight i - nu.weight i)| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [State.FiniteDistribution.pushforward_weight,
        State.FiniteDistribution.pushforward_weight,
        Finset.sum_sub_distrib]
    _ ≤ ∑ j : J, ∑ i with f i = j,
        |mu.weight i - nu.weight i| := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : I, |mu.weight i - nu.weight i| :=
      Finset.sum_fiberwise Finset.univ f
        (fun i ↦ |mu.weight i - nu.weight i|)

namespace DistributionClose

/-- Deterministic pushforward preserves every valid TV error budget. -/
theorem pushforward {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    {epsilon : ℝ} {mu nu : State.FiniteDistribution I}
    (h : DistributionClose epsilon mu nu) (f : I → J) :
    DistributionClose epsilon (mu.pushforward f) (nu.pushforward f) :=
  (totalVariationDistance_pushforward_le mu nu f).trans h

end DistributionClose

end QuaternionicComputing.Semantics
