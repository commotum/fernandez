module

public import QuaternionicComputing.Semantics.Approximation.Operator
public import QuaternionicComputing.Semantics.Approximation.Distribution

/-!
# Strict metric-approximation boundaries

This leaf gives exact finite witnesses showing that a fixed positive error
budget is not transitive.  The operator witnesses include both an elementary
real chain and a chain of genuine one-dimensional complex unitaries.  The
distribution witness uses the two Boolean point masses and the fair Boolean
distribution.

These examples justify treating `OperatorClose` and `DistributionClose` as
budgeted relations whose valid composition law adds budgets, rather than as
equivalence relations at a fixed budget.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace QuaternionicComputing.Semantics.ApproximationStrictness

open QuaternionicComputing.State
open QuaternionicComputing.Semantics

universe u

local instance {X : Type*} : DecidableEq X := Classical.decEq X

/-! ## One-dimensional operator witnesses -/

/-- A scalar represented as a one-dimensional matrix. -/
def scalarMatrix {K : Type u} (z : K) : Matrix Unit Unit K :=
  fun _ _ ↦ z

private theorem scalarMatrix_eq_diagonal {K : Type u} [Zero K]
    (z : K) : scalarMatrix z = Matrix.diagonal (fun _ : Unit ↦ z) := by
  ext i j
  have hi : i = () := Subsingleton.elim _ _
  have hj : j = () := Subsingleton.elim _ _
  subst i
  subst j
  simp [scalarMatrix]

/-- The induced operator distance on scalar matrices is scalar distance. -/
theorem operatorDistance_scalarMatrix {K : Type u} [RCLike K]
    (z w : K) : operatorDistance (scalarMatrix z) (scalarMatrix w) = dist z w := by
  have hsub : scalarMatrix z - scalarMatrix w = scalarMatrix (z - w) := by
    ext
    simp [scalarMatrix]
  calc
    operatorDistance (scalarMatrix z) (scalarMatrix w) =
        ‖scalarMatrix z - scalarMatrix w‖ :=
      operatorDistance_eq_l2_opNorm _ _
    _ = ‖z - w‖ := by
      rw [hsub, scalarMatrix_eq_diagonal, Matrix.l2_opNorm_diagonal]
      simp
    _ = dist z w := (dist_eq_norm z w).symm

/-- Fixed budget `1` is not transitive even for one-dimensional real matrices. -/
theorem operatorClose_one_not_transitive :
    OperatorClose 1 (scalarMatrix (0 : ℝ)) (scalarMatrix 1) ∧
      OperatorClose 1 (scalarMatrix (1 : ℝ)) (scalarMatrix 2) ∧
      ¬ OperatorClose 1 (scalarMatrix (0 : ℝ)) (scalarMatrix 2) := by
  constructor
  · norm_num [OperatorClose, operatorDistance_scalarMatrix, Real.dist_eq]
  constructor
  · norm_num [OperatorClose, operatorDistance_scalarMatrix, Real.dist_eq]
  · norm_num [OperatorClose, operatorDistance_scalarMatrix, Real.dist_eq]

/-- A one-dimensional complex scalar matrix is unitary when its norm square is one. -/
theorem complexScalarMatrix_mem_unitary (z : ℂ)
    (hz : Complex.normSq z = 1) :
    scalarMatrix z ∈ unitary (Matrix Unit Unit ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have hi : i = () := Subsingleton.elim _ _
  have hj : j = () := Subsingleton.elim _ _
  subst i
  subst j
  simp [scalarMatrix, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, ← Complex.normSq_eq_conj_mul_self, hz]

/-- The matrices with scalar entries `1`, `I`, and `-1` are all unitary. -/
theorem complexScalarPhaseChain_unitary :
    scalarMatrix (1 : ℂ) ∈ unitary (Matrix Unit Unit ℂ) ∧
      scalarMatrix Complex.I ∈ unitary (Matrix Unit Unit ℂ) ∧
      scalarMatrix (-1 : ℂ) ∈ unitary (Matrix Unit Unit ℂ) := by
  exact
    ⟨complexScalarMatrix_mem_unitary 1 (by norm_num [Complex.normSq_apply]),
      complexScalarMatrix_mem_unitary Complex.I
        (by norm_num [Complex.normSq_apply]),
      complexScalarMatrix_mem_unitary (-1)
        (by norm_num [Complex.normSq_apply])⟩

/-- Exact distances in the complex unitary chain `1`, `I`, `-1`. -/
theorem complexScalarPhaseChain_distances :
    operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix Complex.I) = √2 ∧
      operatorDistance (scalarMatrix Complex.I) (scalarMatrix (-1 : ℂ)) = √2 ∧
      operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) = 2 := by
  simp only [operatorDistance_scalarMatrix, dist_eq_norm]
  constructor
  · rw [Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply]
  constructor
  · rw [Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply]
  · rw [Complex.norm_def]
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num [Complex.normSq_apply]

/-- Fixed budget `√2` is not transitive even on the displayed complex unitaries. -/
theorem operatorClose_sqrtTwo_not_transitive_on_complex_unitaries :
    OperatorClose √2 (scalarMatrix (1 : ℂ)) (scalarMatrix Complex.I) ∧
      OperatorClose √2 (scalarMatrix Complex.I) (scalarMatrix (-1 : ℂ)) ∧
      ¬ OperatorClose √2 (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) := by
  rcases complexScalarPhaseChain_distances with ⟨h₁, h₂, h₃⟩
  rw [OperatorClose, h₁, OperatorClose, h₂, OperatorClose, h₃]
  exact
    ⟨le_rfl, le_rfl,
      not_le.mpr ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by norm_num))⟩

/-- Raw operator distance detects the global phase between `I` and `-I`. -/
theorem rawDistance_one_negOne_eq_two :
    operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) = 2 :=
  complexScalarPhaseChain_distances.2.2

/-! ## Boolean-distribution witness -/

/-- The point mass at `false`. -/
def deltaFalse : FiniteDistribution Bool where
  weight b := if b then 0 else 1
  nonnegative b := by split <;> norm_num
  normalized := by simp

/-- The uniform distribution on `Bool`. -/
def fairBool : FiniteDistribution Bool where
  weight _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by simp

/-- The point mass at `true`. -/
def deltaTrue : FiniteDistribution Bool where
  weight b := if b then 1 else 0
  nonnegative b := by split <;> norm_num
  normalized := by simp

/-- Exact total-variation distances in the point-mass/uniform/point-mass chain. -/
theorem totalVariation_bool_chain :
    totalVariationDistance deltaFalse fairBool = 1 / 2 ∧
      totalVariationDistance fairBool deltaTrue = 1 / 2 ∧
      totalVariationDistance deltaFalse deltaTrue = 1 := by
  norm_num [totalVariationDistance, deltaFalse, fairBool, deltaTrue,
    Fintype.sum_bool, abs_of_nonneg, abs_of_nonpos]

/-- Fixed total-variation budget `1/2` is not transitive. -/
theorem distributionClose_half_not_transitive :
    DistributionClose (1 / 2) deltaFalse fairBool ∧
      DistributionClose (1 / 2) fairBool deltaTrue ∧
      ¬ DistributionClose (1 / 2) deltaFalse deltaTrue := by
  rcases totalVariation_bool_chain with ⟨h₁, h₂, h₃⟩
  constructor
  · rw [DistributionClose, h₁]
  constructor
  · rw [DistributionClose, h₂]
  · rw [DistributionClose, h₃]
    norm_num

end QuaternionicComputing.Semantics.ApproximationStrictness
