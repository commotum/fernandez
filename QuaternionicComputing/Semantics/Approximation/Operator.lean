module

public import QuaternionicComputing.Semantics.Core
public import QuaternionicComputing.Semantics.Simulation
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm approximation

This leaf defines approximation for finite rectangular matrices over an
`RCLike` scalar using mathlib's scoped Euclidean induced operator norm.
`OperatorClose` is an error-budget relation: it is symmetric, but composition
adds budgets and reflexivity requires a nonnegative budget.  In particular, no
fixed-budget transitivity or `Equivalence` instance is provided.

The mapped variants are directional cross-model comparisons.  They retain the
embedding in their types and therefore do not identify source and target
matrix spaces.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace QuaternionicComputing.Semantics

local instance {X : Type*} : DecidableEq X := Classical.decEq X

universe u v w x y z

/-! ## Euclidean induced operator distance -/

/--
Distance in the Euclidean induced operator norm on finite rectangular
`RCLike` matrices.
-/
def operatorDistance {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) : ℝ :=
  dist U V

/-- `U` and `V` differ by at most the nonnegative error budget `ε`. -/
def OperatorClose {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (ε : ℝ) (U V : Matrix O I K) : Prop :=
  operatorDistance U V ≤ ε

/-- Operator distance is the L2 operator norm of the matrix difference. -/
theorem operatorDistance_eq_l2_opNorm {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) :
    operatorDistance U V = ‖U - V‖ :=
  dist_eq_norm U V

/--
The scoped matrix norm used by `operatorDistance` is the norm of the induced
continuous linear map between finite Euclidean spaces.
-/
theorem operatorDistance_eq_continuousLinearMapNorm
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) :
    operatorDistance U V =
      ‖(Matrix.toEuclideanLin (𝕜 := K) (m := O) (n := I)).trans
        LinearMap.toContinuousLinearMap (U - V)‖ := by
  rw [operatorDistance_eq_l2_opNorm, Matrix.l2_opNorm_def]

/-- On square matrices, operator distance is the norm after `toEuclideanCLM`. -/
theorem operatorDistance_eq_toEuclideanCLM_norm
    {K : Type u} [RCLike K]
    {I : Type v} [Fintype I] (U V : Matrix I I K) :
    operatorDistance U V =
      ‖Matrix.toEuclideanCLM (n := I) (𝕜 := K) (U - V)‖ := by
  rw [operatorDistance_eq_l2_opNorm]
  exact (Matrix.l2_opNorm_toEuclideanCLM (U - V)).symm

@[simp]
theorem operatorDistance_self {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U : Matrix O I K) : operatorDistance U U = 0 :=
  dist_self U

theorem operatorDistance_nonneg {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) : 0 ≤ operatorDistance U V :=
  dist_nonneg

theorem operatorDistance_symm {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) :
    operatorDistance U V = operatorDistance V U :=
  dist_comm U V

theorem operatorDistance_triangle {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V T : Matrix O I K) :
    operatorDistance U T ≤ operatorDistance U V + operatorDistance V T :=
  dist_triangle U V T

@[simp]
theorem operatorDistance_eq_zero_iff_exactOperatorEq
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {U V : Matrix O I K} :
    operatorDistance U V = 0 ↔ ExactOperatorEq U V := by
  simp [operatorDistance, ExactOperatorEq]

@[simp]
theorem operatorClose_zero_iff_exactOperatorEq
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {U V : Matrix O I K} :
    OperatorClose 0 U V ↔ ExactOperatorEq U V := by
  constructor
  · intro h
    exact operatorDistance_eq_zero_iff_exactOperatorEq.mp
      (le_antisymm h (operatorDistance_nonneg U V))
  · intro h
    exact le_of_eq (operatorDistance_eq_zero_iff_exactOperatorEq.mpr h)

namespace OperatorClose

/-- A matrix is close to itself exactly when the supplied budget is nonnegative. -/
theorem refl {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U : Matrix O I K) {ε : ℝ} (hε : 0 ≤ ε) :
    OperatorClose ε U U := by
  simpa [OperatorClose] using hε

/-- Increasing the error budget preserves closeness. -/
theorem mono {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V : Matrix O I K}
    (h : OperatorClose ε U V) (hεδ : ε ≤ δ) :
    OperatorClose δ U V :=
  h.trans hεδ

/-- Operator closeness is symmetric at a fixed budget. -/
theorem symm {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I K}
    (h : OperatorClose ε U V) : OperatorClose ε V U := by
  simpa [OperatorClose, operatorDistance_symm] using h

/-- Approximation composes by adding, rather than preserving, error budgets. -/
theorem additive_trans {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V T : Matrix O I K}
    (hUV : OperatorClose ε U V) (hVT : OperatorClose δ V T) :
    OperatorClose (ε + δ) U T :=
  (operatorDistance_triangle U V T).trans (add_le_add hUV hVT)

end OperatorClose

/-! ## Perturbation bounds -/

/-- Left multiplication amplifies operator distance by at most `‖A‖`. -/
theorem operatorDistance_mul_left_le
    {K : Type u} [RCLike K]
    {O : Type v} {M : Type w} {I : Type x}
    [Fintype O] [Fintype M] [Fintype I]
    (A : Matrix O M K) (B B' : Matrix M I K) :
    operatorDistance (A * B) (A * B') ≤
      ‖A‖ * operatorDistance B B' := by
  rw [operatorDistance_eq_l2_opNorm, ← Matrix.mul_sub]
  simpa only [operatorDistance_eq_l2_opNorm] using
    Matrix.l2_opNorm_mul A (B - B')

/-- Right multiplication amplifies operator distance by at most `‖B‖`. -/
theorem operatorDistance_mul_right_le
    {K : Type u} [RCLike K]
    {O : Type v} {M : Type w} {I : Type x}
    [Fintype O] [Fintype M] [Fintype I]
    (A A' : Matrix O M K) (B : Matrix M I K) :
    operatorDistance (A * B) (A' * B) ≤
      operatorDistance A A' * ‖B‖ := by
  rw [operatorDistance_eq_l2_opNorm, ← Matrix.sub_mul]
  simpa only [operatorDistance_eq_l2_opNorm] using
    Matrix.l2_opNorm_mul (A - A') B

/-- Two-factor perturbation bound for compatible rectangular matrices. -/
theorem operatorDistance_mul_le
    {K : Type u} [RCLike K]
    {O : Type v} {M : Type w} {I : Type x}
    [Fintype O] [Fintype M] [Fintype I]
    (A A' : Matrix O M K) (B B' : Matrix M I K) :
    operatorDistance (A * B) (A' * B') ≤
      ‖A‖ * operatorDistance B B' + operatorDistance A A' * ‖B'‖ := by
  have hdecomp : A * B - A' * B' =
      A * (B - B') + (A - A') * B' := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  calc
    operatorDistance (A * B) (A' * B') =
        ‖A * (B - B') + (A - A') * B'‖ := by
      rw [operatorDistance_eq_l2_opNorm, hdecomp]
    _ ≤ ‖A * (B - B')‖ + ‖(A - A') * B'‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖B - B'‖ + ‖A - A'‖ * ‖B'‖ :=
      add_le_add (Matrix.l2_opNorm_mul A (B - B'))
        (Matrix.l2_opNorm_mul (A - A') B')
    _ = ‖A‖ * operatorDistance B B' + operatorDistance A A' * ‖B'‖ := by
      rw [operatorDistance_eq_l2_opNorm, operatorDistance_eq_l2_opNorm]

/--
For square matrices, unitary outer factors reduce the two-factor bound to the
sum of the supplied budgets.  `Nonempty I` is explicit because the norm of a
unitary element is `1` only in a nontrivial matrix algebra.
-/
theorem OperatorClose.mul_of_unitary
    {K : Type u} [RCLike K]
    {I : Type v} [Fintype I] [Nonempty I]
    {ε δ : ℝ} {A A' B B' : Matrix I I K}
    (hA : A ∈ unitary (Matrix I I K))
    (hB' : B' ∈ unitary (Matrix I I K))
    (hAA' : OperatorClose ε A A')
    (hBB' : OperatorClose δ B B') :
    OperatorClose (ε + δ) (A * B) (A' * B') := by
  have hnormA : ‖A‖ = 1 := CStarRing.norm_of_mem_unitary hA
  have hnormB' : ‖B'‖ = 1 := CStarRing.norm_of_mem_unitary hB'
  unfold OperatorClose at hAA' hBB' ⊢
  calc
    operatorDistance (A * B) (A' * B') ≤
        ‖A‖ * operatorDistance B B' + operatorDistance A A' * ‖B'‖ :=
      operatorDistance_mul_le A A' B B'
    _ ≤ ‖A‖ * δ + ε * ‖B'‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hBB' (norm_nonneg A))
        (mul_le_mul_of_nonneg_right hAA' (norm_nonneg B'))
    _ = ε + δ := by rw [hnormA, hnormB']; ring

/--
Raw output-column error is bounded by operator error times the input L2 norm.
No normalization or unitarity assumption is needed.
-/
theorem operatorDistance_mulVec_le
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V : Matrix O I K) (input : I → K) :
    dist (WithLp.toLp 2 (U *ᵥ input)) (WithLp.toLp 2 (V *ᵥ input)) ≤
      operatorDistance U V * ‖WithLp.toLp 2 input‖ := by
  rw [operatorDistance_eq_l2_opNorm]
  have h := Matrix.l2_opNorm_mulVec (U - V) (WithLp.toLp 2 input)
  change ‖WithLp.toLp 2 ((U - V) *ᵥ input)‖ ≤
    ‖U - V‖ * ‖WithLp.toLp 2 input‖ at h
  rw [Matrix.sub_mulVec] at h
  simpa only [dist_eq_norm, WithLp.toLp_sub] using h

/-! ## Directional mapped approximation -/

/--
Distance from a mapped source operator to a target in one common `RCLike`
matrix space.  The source scalar and index types remain unrestricted.
-/
def mappedOperatorDistance
    {RS : Type u} {K : Type v} [RCLike K]
    {OS : Type w} {IS : Type x} {OT : Type y} {IT : Type z}
    [Fintype OT] [Fintype IT]
    (embed : Matrix OS IS RS → Matrix OT IT K)
    (source : Matrix OS IS RS) (target : Matrix OT IT K) : ℝ :=
  operatorDistance (embed source) target

/-- Directional mapped operator comparison at error budget `ε`. -/
def MappedOperatorClose
    {RS : Type u} {K : Type v} [RCLike K]
    {OS : Type w} {IS : Type x} {OT : Type y} {IT : Type z}
    [Fintype OT] [Fintype IT]
    (ε : ℝ) (embed : Matrix OS IS RS → Matrix OT IT K)
    (source : Matrix OS IS RS) (target : Matrix OT IT K) : Prop :=
  OperatorClose ε (embed source) target

@[simp]
theorem mappedOperatorDistance_eq_zero_iff_exactOperatorEmbedding
    {RS : Type u} {K : Type v} [RCLike K]
    {OS : Type w} {IS : Type x} {OT : Type y} {IT : Type z}
    [Fintype OT] [Fintype IT]
    {embed : Matrix OS IS RS → Matrix OT IT K}
    {source : Matrix OS IS RS} {target : Matrix OT IT K} :
    mappedOperatorDistance embed source target = 0 ↔
      ExactOperatorEmbedding embed source target := by
  rw [mappedOperatorDistance, operatorDistance_eq_zero_iff_exactOperatorEq]
  simp only [ExactOperatorEq.iff_eq, ExactOperatorEmbedding, eq_comm]

@[simp]
theorem mappedOperatorClose_zero_iff_exactOperatorEmbedding
    {RS : Type u} {K : Type v} [RCLike K]
    {OS : Type w} {IS : Type x} {OT : Type y} {IT : Type z}
    [Fintype OT] [Fintype IT]
    {embed : Matrix OS IS RS → Matrix OT IT K}
    {source : Matrix OS IS RS} {target : Matrix OT IT K} :
    MappedOperatorClose 0 embed source target ↔
      ExactOperatorEmbedding embed source target := by
  rw [MappedOperatorClose, operatorClose_zero_iff_exactOperatorEq]
  simp only [ExactOperatorEq.iff_eq, ExactOperatorEmbedding, eq_comm]

end QuaternionicComputing.Semantics
