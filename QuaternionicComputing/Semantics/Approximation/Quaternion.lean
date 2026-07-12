module

public import QuaternionicComputing.Semantics.OperatorPhase.Quaternion
public import QuaternionicComputing.Semantics.SimulationEncoding
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Quaternionic operator approximation

This leaf equips finite quaternionic matrices with the Euclidean induced
operator norm without installing a `Norm`, `Metric`, `RCLike`, or C⋆ instance
on quaternionic matrix types.  A quaternionic matrix acts as an underlying-real
continuous linear map between finite `PiLp 2` spaces; its operator norm is the
ordinary norm of that map.

Fixed-budget closeness is deliberately not an equivalence relation.  Its
triangle law adds the two budgets.  Phase-aware operator closeness minimizes
only over central real unit signs, matching `QuaternionCentralSignEq`; it never
uses arbitrary unit quaternions.

The final comparison theorem proves, rather than assumes, that this native
quaternionic norm equals the L2 operator norm of the canonical complexified
matrix.
-/

@[expose] public noncomputable section

open WithLp
open scoped Matrix Matrix.Norms.L2Operator Quaternion

namespace QuaternionicComputing.Semantics

universe u v w

/-- Finite quaternionic columns with their Euclidean L2 norm. -/
abbrev QuaternionEuclidean (ι : Type*) := PiLp 2 (fun _ : ι => ℍ[ℝ])

/-- Quaternionic matrix action, bundled as an underlying-real linear map. -/
def quaternionMulVecLinear {m : Type u} {n : Type v} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) :
    QuaternionEuclidean n →ₗ[ℝ] QuaternionEuclidean m :=
  (WithLp.linearEquiv 2 ℝ (m → ℍ[ℝ])).symm.toLinearMap.comp <|
    ((Matrix.mulVecBilin ℝ ℝ A).comp
      (WithLp.linearEquiv 2 ℝ (n → ℍ[ℝ])).toLinearMap)

@[simp]
theorem quaternionMulVecLinear_toLp {m : Type u} {n : Type v} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (x : n → ℍ[ℝ]) :
    quaternionMulVecLinear A (toLp 2 x) = toLp 2 (A *ᵥ x) :=
  rfl

/-- Quaternionic matrix action as a continuous real-linear map.

Continuity follows because the source is finite-dimensional over `ℝ`.
-/
def quaternionMulVecCLM {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) :
    QuaternionEuclidean n →L[ℝ] QuaternionEuclidean m :=
  ⟨quaternionMulVecLinear A,
    (quaternionMulVecLinear A).continuous_of_finiteDimensional⟩

@[simp]
theorem quaternionMulVecCLM_toLp {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (x : n → ℍ[ℝ]) :
    quaternionMulVecCLM A (toLp 2 x) = toLp 2 (A *ᵥ x) :=
  rfl

theorem quaternionMulVecCLM_apply {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (x : QuaternionEuclidean n) :
    quaternionMulVecCLM A x = toLp 2 (A *ᵥ x.ofLp) := by
  change quaternionMulVecCLM A (toLp 2 x.ofLp) = _
  exact quaternionMulVecCLM_toLp A x.ofLp

@[simp]
theorem quaternionMulVecCLM_zero {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] :
    quaternionMulVecCLM (0 : Matrix m n ℍ[ℝ]) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [quaternionMulVecCLM_apply]
  simp

@[simp]
theorem quaternionMulVecCLM_add {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    quaternionMulVecCLM (A + B) =
      quaternionMulVecCLM A + quaternionMulVecCLM B := by
  apply ContinuousLinearMap.ext
  intro x
  rw [quaternionMulVecCLM_apply]
  change toLp 2 ((A + B) *ᵥ x.ofLp) =
    quaternionMulVecCLM A x + quaternionMulVecCLM B x
  rw [quaternionMulVecCLM_apply, quaternionMulVecCLM_apply]
  exact congrArg (toLp 2) (Matrix.add_mulVec A B x.ofLp)

@[simp]
theorem quaternionMulVecCLM_neg {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℍ[ℝ]) :
    quaternionMulVecCLM (-A) = -quaternionMulVecCLM A := by
  apply ContinuousLinearMap.ext
  intro x
  rw [quaternionMulVecCLM_apply]
  change toLp 2 ((-A) *ᵥ x.ofLp) = -quaternionMulVecCLM A x
  rw [quaternionMulVecCLM_apply]
  exact congrArg (toLp 2) (Matrix.neg_mulVec x.ofLp A)

@[simp]
theorem quaternionMulVecCLM_sub {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    quaternionMulVecCLM (A - B) =
      quaternionMulVecCLM A - quaternionMulVecCLM B := by
  rw [sub_eq_add_neg, quaternionMulVecCLM_add, quaternionMulVecCLM_neg]
  rfl

@[simp]
theorem quaternionMulVecCLM_real_smul {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (r : ℝ) (A : Matrix m n ℍ[ℝ]) :
    quaternionMulVecCLM (r • A) = r • quaternionMulVecCLM A := by
  apply ContinuousLinearMap.ext
  intro x
  rw [quaternionMulVecCLM_apply]
  change toLp 2 ((r • A) *ᵥ x.ofLp) = r • quaternionMulVecCLM A x
  rw [quaternionMulVecCLM_apply]
  exact congrArg (toLp 2) (Matrix.smul_mulVec r A x.ofLp)

/-- Quaternionic matrix multiplication becomes composition of the real CLMs. -/
theorem quaternionMulVecCLM_mul {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n l ℍ[ℝ]) :
    quaternionMulVecCLM (A * B) =
      (quaternionMulVecCLM A).comp (quaternionMulVecCLM B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change ((A * B) *ᵥ x.ofLp) i = (A *ᵥ (B *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

/-- The real-CLM representation loses no quaternionic matrix entries. -/
theorem quaternionMulVecCLM_injective {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] :
    Function.Injective
      (quaternionMulVecCLM : Matrix m n ℍ[ℝ] →
        QuaternionEuclidean n →L[ℝ] QuaternionEuclidean m) := by
  classical
  intro A B h
  apply Matrix.ext_of_mulVec_single
  intro j
  have hx := congrArg (fun f => f (toLp 2 (Pi.single j 1))) h
  rw [quaternionMulVecCLM_toLp, quaternionMulVecCLM_toLp] at hx
  exact WithLp.toLp_injective 2 hx

/-- The native Euclidean induced operator norm of a quaternionic matrix. -/
def quaternionOperatorNorm {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℍ[ℝ]) : ℝ :=
  ‖quaternionMulVecCLM A‖

/-- Euclidean induced operator distance between quaternionic matrices. -/
def quaternionOperatorDistance {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) : ℝ :=
  quaternionOperatorNorm (A - B)

/-- Fixed-budget quaternionic operator closeness.  This is not an equivalence relation. -/
def QuaternionOperatorClose {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (ε : ℝ) (A B : Matrix m n ℍ[ℝ]) : Prop :=
  quaternionOperatorDistance A B ≤ ε

theorem quaternionOperatorNorm_nonneg {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℍ[ℝ]) :
    0 ≤ quaternionOperatorNorm A :=
  (quaternionMulVecCLM A).opNorm_nonneg

@[simp]
theorem quaternionOperatorNorm_zero {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] :
    quaternionOperatorNorm (0 : Matrix m n ℍ[ℝ]) = 0 := by
  rw [quaternionOperatorNorm, quaternionMulVecCLM_zero]
  exact ContinuousLinearMap.opNorm_zero

@[simp]
theorem quaternionOperatorNorm_neg {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm (-A) = quaternionOperatorNorm A := by
  rw [quaternionOperatorNorm, quaternionMulVecCLM_neg]
  exact ContinuousLinearMap.opNorm_neg _

theorem quaternionOperatorNorm_eq_zero_iff {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    change ‖quaternionMulVecCLM A‖ = 0 at h
    have hmap : quaternionMulVecCLM A = 0 :=
      (norm_eq_zero
        (E := QuaternionEuclidean n →L[ℝ] QuaternionEuclidean m)).mp h
    exact quaternionMulVecCLM_injective <| hmap.trans quaternionMulVecCLM_zero.symm
  · rintro rfl
    exact quaternionOperatorNorm_zero

theorem quaternionOperatorNorm_add_le {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm (A + B) ≤
      quaternionOperatorNorm A + quaternionOperatorNorm B := by
  rw [quaternionOperatorNorm, quaternionMulVecCLM_add]
  exact ContinuousLinearMap.opNorm_add_le
    (quaternionMulVecCLM A) (quaternionMulVecCLM B)

theorem quaternionOperatorNorm_sub_le {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm (A - B) ≤
      quaternionOperatorNorm A + quaternionOperatorNorm B := by
  simpa only [sub_eq_add_neg, quaternionOperatorNorm_neg] using
    quaternionOperatorNorm_add_le A (-B)

/-- Quaternionic operator norm is submultiplicative. -/
theorem quaternionOperatorNorm_mul {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n l ℍ[ℝ]) :
    quaternionOperatorNorm (A * B) ≤
      quaternionOperatorNorm A * quaternionOperatorNorm B := by
  rw [quaternionOperatorNorm, quaternionOperatorNorm, quaternionOperatorNorm,
    quaternionMulVecCLM_mul]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- The operator norm bounds quaternionic matrix action on every L2 column. -/
theorem quaternionOperatorNorm_mulVec {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (x : QuaternionEuclidean n) :
    ‖quaternionMulVecCLM A x‖ ≤ quaternionOperatorNorm A * ‖x‖ :=
  (quaternionMulVecCLM A).le_opNorm x

@[simp]
theorem quaternionOperatorDistance_self {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance A A = 0 := by
  simp [quaternionOperatorDistance]

theorem quaternionOperatorDistance_nonneg {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    0 ≤ quaternionOperatorDistance A B :=
  quaternionOperatorNorm_nonneg _

theorem quaternionOperatorDistance_symm {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance A B = quaternionOperatorDistance B A := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (A - B) = quaternionOperatorNorm (-(B - A)) := by
      congr 1
      abel
    _ = quaternionOperatorNorm (B - A) := quaternionOperatorNorm_neg _

theorem quaternionOperatorDistance_triangle {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A B C : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance A C ≤
      quaternionOperatorDistance A B + quaternionOperatorDistance B C := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance,
    quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (A - C) =
        quaternionOperatorNorm ((A - B) + (B - C)) := by
      congr 1
      abel
    _ ≤ quaternionOperatorNorm (A - B) + quaternionOperatorNorm (B - C) :=
      quaternionOperatorNorm_add_le _ _

theorem quaternionOperatorDistance_eq_zero_iff {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance A B = 0 ↔ A = B := by
  rw [quaternionOperatorDistance, quaternionOperatorNorm_eq_zero_iff, sub_eq_zero]

theorem quaternionOperatorDistance_add {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A B C D : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance (A + B) (C + D) ≤
      quaternionOperatorDistance A C + quaternionOperatorDistance B D := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance,
    quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (A + B - (C + D)) =
        quaternionOperatorNorm ((A - C) + (B - D)) := by
      congr 1
      abel
    _ ≤ quaternionOperatorNorm (A - C) + quaternionOperatorNorm (B - D) :=
      quaternionOperatorNorm_add_le _ _

theorem quaternionOperatorDistance_sub {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (A B C D : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance (A - B) (C - D) ≤
      quaternionOperatorDistance A C + quaternionOperatorDistance B D := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance,
    quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (A - B - (C - D)) =
        quaternionOperatorNorm ((A - C) - (B - D)) := by
      congr 1
      abel
    _ ≤ quaternionOperatorNorm (A - C) + quaternionOperatorNorm (B - D) :=
      quaternionOperatorNorm_sub_le _ _

theorem quaternionOperatorDistance_mul_right
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A C : Matrix m n ℍ[ℝ]) (B : Matrix n l ℍ[ℝ]) :
    quaternionOperatorDistance (A * B) (C * B) ≤
      quaternionOperatorDistance A C * quaternionOperatorNorm B := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance]
  rw [← Matrix.sub_mul]
  exact quaternionOperatorNorm_mul (A - C) B

theorem quaternionOperatorDistance_mul_left
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A : Matrix m n ℍ[ℝ]) (B D : Matrix n l ℍ[ℝ]) :
    quaternionOperatorDistance (A * B) (A * D) ≤
      quaternionOperatorNorm A * quaternionOperatorDistance B D := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance]
  rw [← Matrix.mul_sub]
  exact quaternionOperatorNorm_mul A (B - D)

/-- Two-factor product perturbation bound. -/
theorem quaternionOperatorDistance_mul
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A C : Matrix m n ℍ[ℝ]) (B D : Matrix n l ℍ[ℝ]) :
    quaternionOperatorDistance (A * B) (C * D) ≤
      quaternionOperatorDistance A C * quaternionOperatorNorm B +
        quaternionOperatorNorm C * quaternionOperatorDistance B D := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance,
    quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (A * B - C * D) =
        quaternionOperatorNorm ((A - C) * B + C * (B - D)) := by
      congr 1
      rw [Matrix.sub_mul, Matrix.mul_sub]
      abel
    _ ≤ quaternionOperatorNorm ((A - C) * B) +
          quaternionOperatorNorm (C * (B - D)) :=
      quaternionOperatorNorm_add_le _ _
    _ ≤ quaternionOperatorNorm (A - C) * quaternionOperatorNorm B +
          quaternionOperatorNorm C * quaternionOperatorNorm (B - D) :=
      add_le_add (quaternionOperatorNorm_mul _ _) (quaternionOperatorNorm_mul _ _)

/-- Operator distance controls the L2 error on every common input column. -/
theorem quaternionOperatorDistance_mulVec
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A B : Matrix m n ℍ[ℝ]) (x : n → ℍ[ℝ]) :
    ‖toLp 2 (A *ᵥ x - B *ᵥ x)‖ ≤
      quaternionOperatorDistance A B * ‖toLp 2 x‖ := by
  simpa [quaternionOperatorDistance, quaternionOperatorNorm, Matrix.sub_mulVec] using
    (quaternionMulVecCLM (A - B)).le_opNorm (toLp 2 x)

namespace QuaternionOperatorClose

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]
variable {ε δ : ℝ} {A B C : Matrix m n ℍ[ℝ]}

theorem refl (hε : 0 ≤ ε) (A : Matrix m n ℍ[ℝ]) :
    QuaternionOperatorClose ε A A := by
  simpa [QuaternionOperatorClose] using hε

theorem mono (h : QuaternionOperatorClose ε A B) (hεδ : ε ≤ δ) :
    QuaternionOperatorClose δ A B :=
  h.trans hεδ

theorem symm (h : QuaternionOperatorClose ε A B) :
    QuaternionOperatorClose ε B A := by
  simpa [QuaternionOperatorClose, quaternionOperatorDistance_symm] using h

theorem additive_trans (hAB : QuaternionOperatorClose ε A B)
    (hBC : QuaternionOperatorClose δ B C) :
    QuaternionOperatorClose (ε + δ) A C :=
  (quaternionOperatorDistance_triangle A B C).trans (add_le_add hAB hBC)

theorem zero_iff_exactOperatorEq :
    QuaternionOperatorClose 0 A B ↔ ExactOperatorEq A B := by
  constructor
  · intro h
    exact (quaternionOperatorDistance_eq_zero_iff A B).mp <|
      le_antisymm h (quaternionOperatorDistance_nonneg A B)
  · intro h
    subst B
    exact refl le_rfl A

end QuaternionOperatorClose

/-- Approximation up to one central real unit sign, oriented as `V ≈ s • U`. -/
def QuaternionCentralSignClose {m : Type u} {n : Type v}
    [Fintype m] [Fintype n]
    (ε : ℝ) (U V : Matrix m n ℍ[ℝ]) : Prop :=
  ∃ s : ℝ, s * s = 1 ∧ QuaternionOperatorClose ε V (s • U)

private theorem quaternionOperatorDistance_neg_neg
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance (-A) (-B) = quaternionOperatorDistance A B := by
  rw [quaternionOperatorDistance, quaternionOperatorDistance]
  calc
    quaternionOperatorNorm (-A - -B) = quaternionOperatorNorm (-(A - B)) := by
      congr 1
      abel
    _ = quaternionOperatorNorm (A - B) := quaternionOperatorNorm_neg _

private theorem quaternionOperatorDistance_sign_smul
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (s : ℝ) (hs : s * s = 1) (A B : Matrix m n ℍ[ℝ]) :
    quaternionOperatorDistance (s • A) (s • B) =
      quaternionOperatorDistance A B := by
  rcases mul_self_eq_one_iff.mp hs with rfl | rfl
  · simp
  · simpa using quaternionOperatorDistance_neg_neg A B

namespace QuaternionOperatorClose

theorem sign_smul {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {ε : ℝ} {A B : Matrix m n ℍ[ℝ]}
    (h : QuaternionOperatorClose ε A B) (s : ℝ) (hs : s * s = 1) :
    QuaternionOperatorClose ε (s • A) (s • B) := by
  simpa [QuaternionOperatorClose,
    quaternionOperatorDistance_sign_smul s hs A B] using h

end QuaternionOperatorClose

namespace QuaternionCentralSignClose

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]
variable {ε δ : ℝ} {U V T : Matrix m n ℍ[ℝ]}

theorem refl (hε : 0 ≤ ε) (U : Matrix m n ℍ[ℝ]) :
    QuaternionCentralSignClose ε U U :=
  ⟨1, by norm_num, by simpa using QuaternionOperatorClose.refl hε U⟩

theorem mono (h : QuaternionCentralSignClose ε U V) (hεδ : ε ≤ δ) :
    QuaternionCentralSignClose δ U V := by
  rcases h with ⟨s, hs, hclose⟩
  exact ⟨s, hs, hclose.mono hεδ⟩

theorem symm (h : QuaternionCentralSignClose ε U V) :
    QuaternionCentralSignClose ε V U := by
  rcases h with ⟨s, hs, hclose⟩
  refine ⟨s, hs, ?_⟩
  have hscaled := hclose.sign_smul s hs
  have hsymm := hscaled.symm
  simpa [smul_smul, hs] using hsymm

theorem additive_trans (hUV : QuaternionCentralSignClose ε U V)
    (hVT : QuaternionCentralSignClose δ V T) :
    QuaternionCentralSignClose (ε + δ) U T := by
  rcases hUV with ⟨s, hs, hUV⟩
  rcases hVT with ⟨t, ht, hVT⟩
  refine ⟨t * s, ?_, ?_⟩
  · calc
      (t * s) * (t * s) = (t * t) * (s * s) := by ring
      _ = 1 := by rw [ht, hs, one_mul]
  · have hscaled : QuaternionOperatorClose ε (t • V) (t • (s • U)) :=
      hUV.sign_smul t ht
    have hchain := hVT.additive_trans hscaled
    simpa [add_comm, smul_smul] using hchain

theorem zero_iff_quaternionCentralSignEq :
    QuaternionCentralSignClose 0 U V ↔ QuaternionCentralSignEq U V := by
  constructor
  · rintro ⟨s, hs, hclose⟩
    exact ⟨s, hs, (QuaternionOperatorClose.zero_iff_exactOperatorEq.mp hclose)⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, QuaternionOperatorClose.refl le_rfl _⟩

end QuaternionCentralSignClose

/-! ## Comparison with canonical complexification -/

private def complexColumn0LpLinearEquiv (n : Type*) :
    QuaternionEuclidean n ≃ₗ[ℝ] EuclideanSpace ℂ (n ⊕ n) :=
  (WithLp.linearEquiv 2 ℝ (n → ℍ[ℝ])).trans <|
    (complexColumn0LinearEquiv n).trans <|
      (WithLp.linearEquiv 2 ℝ (n ⊕ n → ℂ)).symm

private def complexColumn0LIE (n : Type*) [Fintype n] :
    QuaternionEuclidean n ≃ₗᵢ[ℝ] EuclideanSpace ℂ (n ⊕ n) where
  toLinearEquiv := complexColumn0LpLinearEquiv n
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    change ‖toLp 2 (State.complexColumn0 x.ofLp)‖ ^ 2 = ‖x‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq,
      PiLp.norm_sq_eq_of_L2 (fun _ : n => ℍ[ℝ])]
    simp only [Fintype.sum_sum_type, State.complexColumn0_inl,
      State.complexColumn0_inr, Complex.sq_norm]
    rw [← Finset.sum_add_distrib]
    congr 1 with i
    rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self,
      QuaternionicComputing.Quaternion.normSq_eq_complexPart_add_jPart]
    simp

private abbrev complexMatrixCLM
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans
    LinearMap.toContinuousLinearMap A

private theorem complexMatrixCLM_complexify_restrictScalars
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℍ[ℝ]) :
    (complexMatrixCLM (Quaternion.complexify A)).restrictScalars ℝ =
      (complexColumn0LIE m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((quaternionMulVecCLM A).comp
          (complexColumn0LIE n).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [complexMatrixCLM, ContinuousLinearMap.comp_apply,
    LinearEquiv.trans_apply, LinearIsometryEquiv.coe_coe'',
    complexColumn0LIE, complexColumn0LpLinearEquiv,
    quaternionMulVecCLM_apply]
  change (Quaternion.complexify A *ᵥ x.ofLp) i =
    State.complexColumn0 (A *ᵥ State.quaternionOfComplexColumn0 x.ofLp) i
  rw [← State.complexify_mulVec_complexColumn0]
  exact congrFun (congrArg (fun y => Quaternion.complexify A *ᵥ y)
    (complexColumn0_rightInverse x.ofLp).symm) i

/-- The native quaternionic operator norm equals the L2 norm of complexification. -/
theorem quaternionOperatorNorm_eq_l2_opNorm_complexify
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm A = ‖Quaternion.complexify A‖ := by
  symm
  simp only [Matrix.l2_opNorm_def]
  change ‖complexMatrixCLM (Quaternion.complexify A)‖ =
    ‖quaternionMulVecCLM A‖
  rw [← ContinuousLinearMap.norm_restrictScalars
    (𝕜' := ℝ) (complexMatrixCLM (Quaternion.complexify A)),
    complexMatrixCLM_complexify_restrictScalars,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end QuaternionicComputing.Semantics
