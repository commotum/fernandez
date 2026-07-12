module

public import QuaternionicComputing.Semantics.Approximation.Operator
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal

/-!
# Approximation up to one global phase

This leaf compares finite real and complex matrices after multiplying the
entire source matrix by one unit scalar.  The generic `RCLike` relation exposes
the common metric argument; the stable real and complex names retain the exact
witness conventions used by `RealGlobalSignEq` and `ComplexGlobalPhaseEq`.

These are error-budget relations, not fixed-budget equivalence relations.
Reflexivity requires a nonnegative budget and composition adds budgets.  No
quaternionic operator-phase relation is defined here: arbitrary quaternion
scalars are not valid global operator phases.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace QuaternionicComputing.Semantics

local instance {X : Type*} : DecidableEq X := Classical.decEq X

universe u v w

/-! ## Scalar isometry -/

/-- Scaling both matrices scales their operator distance by the scalar norm. -/
theorem operatorDistance_smul
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (z : K) (U V : Matrix O I K) :
    operatorDistance (z • U) (z • V) = ‖z‖ * operatorDistance U V := by
  simp [operatorDistance, dist_eq_norm, ← smul_sub, norm_smul]

/-- Multiplication by one unit `RCLike` scalar preserves operator distance. -/
theorem operatorDistance_smul_of_norm_eq_one
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (z : K) (hz : ‖z‖ = 1) (U V : Matrix O I K) :
    operatorDistance (z • U) (z • V) = operatorDistance U V := by
  rw [operatorDistance_smul, hz, one_mul]

/-! ## Generic one-phase approximation -/

/--
`V` is within `ε` of one unit-scalar multiple of `U`.  One scalar acts on the
whole matrix; this is not an input-column or output-row phase family.
-/
def RCLikeGlobalPhaseClose
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (ε : ℝ) (U V : Matrix O I K) : Prop :=
  ∃ z : K, ‖z‖ = 1 ∧ OperatorClose ε V (z • U)

namespace RCLikeGlobalPhaseClose

/-- Every matrix is globally phase-close to itself at a nonnegative budget. -/
theorem refl
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε : ℝ} (hε : 0 ≤ ε) (U : Matrix O I K) :
    RCLikeGlobalPhaseClose ε U U := by
  refine ⟨1, norm_one, ?_⟩
  simpa using OperatorClose.refl U hε

/-- Increasing the error budget preserves one-phase closeness. -/
theorem mono
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V : Matrix O I K}
    (h : RCLikeGlobalPhaseClose ε U V) (hεδ : ε ≤ δ) :
    RCLikeGlobalPhaseClose δ U V := by
  rcases h with ⟨z, hz, hclose⟩
  exact ⟨z, hz, hclose.mono hεδ⟩

/-- One-global-phase closeness is symmetric at a fixed budget. -/
theorem symm
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I K}
    (h : RCLikeGlobalPhaseClose ε U V) :
    RCLikeGlobalPhaseClose ε V U := by
  rcases h with ⟨z, hz, hclose⟩
  refine ⟨star z, by simpa using hz, ?_⟩
  have hinv : star z • (z • U) = U := by
    rw [smul_smul]
    change ((starRingEnd K) z * z) • U = U
    rw [RCLike.conj_mul, hz]
    simp
  calc
    operatorDistance U (star z • V) =
        operatorDistance (star z • V) U := operatorDistance_symm _ _
    _ = operatorDistance (star z • V) (star z • (z • U)) := by
      rw [hinv]
    _ = operatorDistance V (z • U) :=
      operatorDistance_smul_of_norm_eq_one (star z) (by simpa using hz) _ _
    _ ≤ ε := hclose

/-- Composing one-phase approximations adds their error budgets. -/
theorem additive_trans
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V T : Matrix O I K}
    (hUV : RCLikeGlobalPhaseClose ε U V)
    (hVT : RCLikeGlobalPhaseClose δ V T) :
    RCLikeGlobalPhaseClose (ε + δ) U T := by
  rcases hUV with ⟨z, hz, hUV⟩
  rcases hVT with ⟨q, hq, hVT⟩
  refine ⟨q * z, by rw [norm_mul, hq, hz, one_mul], ?_⟩
  have hscaled : OperatorClose ε (q • V) (q • (z • U)) :=
    (operatorDistance_smul_of_norm_eq_one q hq V (z • U)).le.trans hUV
  have hcomposed : OperatorClose (δ + ε) T (q • (z • U)) :=
    hVT.additive_trans hscaled
  simpa only [smul_smul, add_comm] using hcomposed

end RCLikeGlobalPhaseClose

/-! ## Stable real global-sign approximation -/

/-- Real global-sign approximation, with the exact convention `s * s = 1`. -/
def RealGlobalSignClose
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (ε : ℝ) (U V : Matrix O I ℝ) : Prop :=
  ∃ s : ℝ, s * s = 1 ∧ OperatorClose ε V (s • U)

/-- For real scalars, unit norm is equivalent to the exact sign convention. -/
theorem real_norm_eq_one_iff_mul_self_eq_one (s : ℝ) :
    ‖s‖ = 1 ↔ s * s = 1 := by
  rw [Real.norm_eq_abs]
  constructor
  · intro hs
    nlinarith [sq_abs s]
  · intro hs
    nlinarith [sq_abs s, abs_nonneg s]

/-- The stable real relation is the real instance of the generic relation. -/
theorem realGlobalSignClose_iff_rclike
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I ℝ} :
    RealGlobalSignClose ε U V ↔ RCLikeGlobalPhaseClose ε U V := by
  constructor <;> rintro ⟨s, hs, hclose⟩
  · exact ⟨s, (real_norm_eq_one_iff_mul_self_eq_one s).mpr hs, hclose⟩
  · exact ⟨s, (real_norm_eq_one_iff_mul_self_eq_one s).mp hs, hclose⟩

@[simp]
theorem realGlobalSignClose_zero_iff
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {U V : Matrix O I ℝ} :
    RealGlobalSignClose 0 U V ↔ RealGlobalSignEq U V := by
  constructor
  · rintro ⟨s, hs, hclose⟩
    exact ⟨s, hs, (operatorClose_zero_iff_exactOperatorEq.mp hclose).eq⟩
  · rintro ⟨s, hs, hEq⟩
    exact ⟨s, hs, operatorClose_zero_iff_exactOperatorEq.mpr
      (ExactOperatorEq.of_eq hEq)⟩

namespace RealGlobalSignClose

theorem refl
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} (hε : 0 ≤ ε) (U : Matrix O I ℝ) :
    RealGlobalSignClose ε U U :=
  realGlobalSignClose_iff_rclike.mpr
    (RCLikeGlobalPhaseClose.refl hε U)

theorem mono
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V : Matrix O I ℝ}
    (h : RealGlobalSignClose ε U V) (hεδ : ε ≤ δ) :
    RealGlobalSignClose δ U V :=
  realGlobalSignClose_iff_rclike.mpr
    ((realGlobalSignClose_iff_rclike.mp h).mono hεδ)

theorem symm
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I ℝ}
    (h : RealGlobalSignClose ε U V) : RealGlobalSignClose ε V U :=
  realGlobalSignClose_iff_rclike.mpr
    (realGlobalSignClose_iff_rclike.mp h).symm

theorem additive_trans
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V T : Matrix O I ℝ}
    (hUV : RealGlobalSignClose ε U V)
    (hVT : RealGlobalSignClose δ V T) :
    RealGlobalSignClose (ε + δ) U T :=
  realGlobalSignClose_iff_rclike.mpr
    ((realGlobalSignClose_iff_rclike.mp hUV).additive_trans
      (realGlobalSignClose_iff_rclike.mp hVT))

end RealGlobalSignClose

/-! ## Stable complex global-phase approximation -/

/-- Complex global-phase approximation, with the exact `normSq` convention. -/
def ComplexGlobalPhaseClose
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (ε : ℝ) (U V : Matrix O I ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 ∧ OperatorClose ε V (z • U)

/-- For complex scalars, unit norm is equivalent to unit squared norm. -/
theorem complex_norm_eq_one_iff_normSq_eq_one (z : ℂ) :
    ‖z‖ = 1 ↔ Complex.normSq z = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro hz
    rw [hz]
    norm_num
  · intro hz
    nlinarith [norm_nonneg z]

/-- The stable complex relation is the complex instance of the generic relation. -/
theorem complexGlobalPhaseClose_iff_rclike
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I ℂ} :
    ComplexGlobalPhaseClose ε U V ↔ RCLikeGlobalPhaseClose ε U V := by
  constructor <;> rintro ⟨z, hz, hclose⟩
  · exact ⟨z, (complex_norm_eq_one_iff_normSq_eq_one z).mpr hz, hclose⟩
  · exact ⟨z, (complex_norm_eq_one_iff_normSq_eq_one z).mp hz, hclose⟩

@[simp]
theorem complexGlobalPhaseClose_zero_iff
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {U V : Matrix O I ℂ} :
    ComplexGlobalPhaseClose 0 U V ↔ ComplexGlobalPhaseEq U V := by
  constructor
  · rintro ⟨z, hz, hclose⟩
    exact ⟨z, hz, (operatorClose_zero_iff_exactOperatorEq.mp hclose).eq⟩
  · rintro ⟨z, hz, hEq⟩
    exact ⟨z, hz, operatorClose_zero_iff_exactOperatorEq.mpr
      (ExactOperatorEq.of_eq hEq)⟩

namespace ComplexGlobalPhaseClose

theorem refl
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} (hε : 0 ≤ ε) (U : Matrix O I ℂ) :
    ComplexGlobalPhaseClose ε U U :=
  complexGlobalPhaseClose_iff_rclike.mpr
    (RCLikeGlobalPhaseClose.refl hε U)

theorem mono
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V : Matrix O I ℂ}
    (h : ComplexGlobalPhaseClose ε U V) (hεδ : ε ≤ δ) :
    ComplexGlobalPhaseClose δ U V :=
  complexGlobalPhaseClose_iff_rclike.mpr
    ((complexGlobalPhaseClose_iff_rclike.mp h).mono hεδ)

theorem symm
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε : ℝ} {U V : Matrix O I ℂ}
    (h : ComplexGlobalPhaseClose ε U V) : ComplexGlobalPhaseClose ε V U :=
  complexGlobalPhaseClose_iff_rclike.mpr
    (complexGlobalPhaseClose_iff_rclike.mp h).symm

theorem additive_trans
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {ε δ : ℝ} {U V T : Matrix O I ℂ}
    (hUV : ComplexGlobalPhaseClose ε U V)
    (hVT : ComplexGlobalPhaseClose δ V T) :
    ComplexGlobalPhaseClose (ε + δ) U T :=
  complexGlobalPhaseClose_iff_rclike.mpr
    ((complexGlobalPhaseClose_iff_rclike.mp hUV).additive_trans
      (complexGlobalPhaseClose_iff_rclike.mp hVT))

end ComplexGlobalPhaseClose

end QuaternionicComputing.Semantics
