module

public import QuaternionicComputing.Semantics.Approximation.Operator
public import QuaternionicComputing.Semantics.Approximation.OperatorPhase
public import QuaternionicComputing.Semantics.Approximation.Quaternion
public import QuaternionicComputing.Semantics.Approximation.State
public import QuaternionicComputing.Semantics.Approximation.Distribution
public import QuaternionicComputing.Semantics.Approximation.Strictness

/-!
# Metric approximation audit

This non-root leaf allocates every stable Stage 10 approximation declaration
to one documented aggregate consumer and exercises the principal boundaries on
concrete finite examples.  The public root deliberately does not import this
file.

The allocation is by source leaf and source order:

* operator metric, perturbation, and mapped APIs: `15 + 5 + 4 = 24`;
* scalar isometry, generic phase, real sign, and complex phase APIs:
  `2 + 5 + 8 + 8 = 23`;
* quaternionic action, norm, distance, close, central-sign, and comparison APIs:
  `13 + 11 + 11 + 5 + 7 + 1 = 48`;
* column, right-phase, three normalized-ray, exact bridge, and output APIs:
  `12 + 7 + 5 + 5 + 5 + 3 + 6 = 43`;
* total-variation metric and observable APIs: `13 + 4 = 17`;
* exact strictness witnesses: `14`.

Thus the aggregates below allocate exactly
`24 + 23 + 48 + 43 + 17 + 14 = 169` stable declarations.  Approximation is
always budgeted: no aggregate supplies a fixed-budget transitivity theorem or
an equivalence instance.
-/

@[expose] public noncomputable section

open WithLp
open scoped BigOperators Matrix Matrix.Norms.L2Operator Quaternion RightActions

namespace QuaternionicComputing.Semantics.ApproximationAudit

open QuaternionicComputing.State
open QuaternionicComputing.Semantics.ApproximationStrictness

local instance {X : Type*} : DecidableEq X := Classical.decEq X

universe u v w x

/-! ## Exact allocation of the 24 RCLike operator declarations -/

/-- Complete consumer for the 15 operator metric and budget declarations. -/
theorem operatorMetric_api
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (U V T : Matrix O I K) (S Q : Matrix I I K)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hUV : OperatorClose ε U V) (hVT : OperatorClose δ V T) :
    operatorDistance U V = ‖U - V‖ ∧
      operatorDistance U V =
        ‖(Matrix.toEuclideanLin (𝕜 := K) (m := O) (n := I)).trans
          LinearMap.toContinuousLinearMap (U - V)‖ ∧
      operatorDistance S Q =
        ‖Matrix.toEuclideanCLM (n := I) (𝕜 := K) (S - Q)‖ ∧
      operatorDistance U U = 0 ∧
      0 ≤ operatorDistance U V ∧
      operatorDistance U V = operatorDistance V U ∧
      operatorDistance U T ≤ operatorDistance U V + operatorDistance V T ∧
      (operatorDistance U V = 0 ↔ ExactOperatorEq U V) ∧
      (OperatorClose 0 U V ↔ ExactOperatorEq U V) ∧
      OperatorClose ε U U ∧
      OperatorClose δ U V ∧
      OperatorClose ε V U ∧
      OperatorClose (ε + δ) U T :=
  ⟨operatorDistance_eq_l2_opNorm U V,
    operatorDistance_eq_continuousLinearMapNorm U V,
    operatorDistance_eq_toEuclideanCLM_norm S Q,
    operatorDistance_self U,
    operatorDistance_nonneg U V,
    operatorDistance_symm U V,
    operatorDistance_triangle U V T,
    operatorDistance_eq_zero_iff_exactOperatorEq,
    operatorClose_zero_iff_exactOperatorEq,
    OperatorClose.refl U hε,
    hUV.mono hεδ,
    hUV.symm,
    hUV.additive_trans hVT⟩

/-- Complete consumer for the five operator perturbation declarations. -/
theorem operatorPerturbation_api
    {K : Type u} [RCLike K]
    {O : Type v} {M : Type w} {I : Type x}
    [Fintype O] [Fintype M] [Fintype I]
    (A A' : Matrix O M K) (B B' : Matrix M I K) (input : M → K)
    {X : Type*} [Fintype X] [Nonempty X]
    {P P' Q Q' : Matrix X X K} {ε δ : ℝ}
    (hP : P ∈ unitary (Matrix X X K))
    (hQ' : Q' ∈ unitary (Matrix X X K))
    (hPP' : OperatorClose ε P P') (hQQ' : OperatorClose δ Q Q') :
    operatorDistance (A * B) (A * B') ≤
        ‖A‖ * operatorDistance B B' ∧
      operatorDistance (A * B) (A' * B) ≤
        operatorDistance A A' * ‖B‖ ∧
      operatorDistance (A * B) (A' * B') ≤
        ‖A‖ * operatorDistance B B' + operatorDistance A A' * ‖B'‖ ∧
      OperatorClose (ε + δ) (P * Q) (P' * Q') ∧
      dist (toLp 2 (A *ᵥ input)) (toLp 2 (A' *ᵥ input)) ≤
        operatorDistance A A' * ‖toLp 2 input‖ :=
  ⟨operatorDistance_mul_left_le A B B',
    operatorDistance_mul_right_le A A' B,
    operatorDistance_mul_le A A' B B',
    OperatorClose.mul_of_unitary hP hQ' hPP' hQQ',
    operatorDistance_mulVec_le A A' input⟩

/-- Complete consumer for the four directional mapped-operator declarations. -/
theorem mappedOperator_api
    {RS : Type u} {K : Type v} [RCLike K]
    {OS : Type w} {IS : Type x} {OT IT : Type*}
    [Fintype OT] [Fintype IT]
    (embed : Matrix OS IS RS → Matrix OT IT K)
    (source : Matrix OS IS RS) (target : Matrix OT IT K) :
    (mappedOperatorDistance embed source target = 0 ↔
        ExactOperatorEmbedding embed source target) ∧
      (MappedOperatorClose 0 embed source target ↔
        ExactOperatorEmbedding embed source target) :=
  ⟨mappedOperatorDistance_eq_zero_iff_exactOperatorEmbedding,
    mappedOperatorClose_zero_iff_exactOperatorEmbedding⟩

/-! ## Exact allocation of the 23 global-phase declarations -/

/-- Complete consumer for the two scalar-isometry declarations. -/
theorem operatorScalarIsometry_api
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    (z : K) (hz : ‖z‖ = 1) (U V : Matrix O I K) :
    operatorDistance (z • U) (z • V) = ‖z‖ * operatorDistance U V ∧
      operatorDistance (z • U) (z • V) = operatorDistance U V :=
  ⟨operatorDistance_smul z U V,
    operatorDistance_smul_of_norm_eq_one z hz U V⟩

/-- Complete consumer for all five generic one-global-phase declarations. -/
theorem rclikeGlobalPhaseClose_api
    {K : Type u} [RCLike K]
    {O : Type v} {I : Type w} [Fintype O] [Fintype I]
    {U V T : Matrix O I K} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hUV : RCLikeGlobalPhaseClose ε U V)
    (hVT : RCLikeGlobalPhaseClose δ V T) :
    RCLikeGlobalPhaseClose ε U U ∧
      RCLikeGlobalPhaseClose δ U V ∧
      RCLikeGlobalPhaseClose ε V U ∧
      RCLikeGlobalPhaseClose (ε + δ) U T :=
  ⟨RCLikeGlobalPhaseClose.refl hε U,
    hUV.mono hεδ,
    hUV.symm,
    hUV.additive_trans hVT⟩

/-- Complete consumer for all eight stable real global-sign declarations. -/
theorem realGlobalSignClose_api
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {U V T : Matrix O I ℝ} (s : ℝ) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hUV : RealGlobalSignClose ε U V)
    (hVT : RealGlobalSignClose δ V T) :
    (‖s‖ = 1 ↔ s * s = 1) ∧
      (RealGlobalSignClose ε U V ↔ RCLikeGlobalPhaseClose ε U V) ∧
      (RealGlobalSignClose 0 U V ↔ RealGlobalSignEq U V) ∧
      RealGlobalSignClose ε U U ∧
      RealGlobalSignClose δ U V ∧
      RealGlobalSignClose ε V U ∧
      RealGlobalSignClose (ε + δ) U T :=
  ⟨real_norm_eq_one_iff_mul_self_eq_one s,
    realGlobalSignClose_iff_rclike,
    realGlobalSignClose_zero_iff,
    RealGlobalSignClose.refl hε U,
    hUV.mono hεδ,
    hUV.symm,
    hUV.additive_trans hVT⟩

/-- Complete consumer for all eight stable complex global-phase declarations. -/
theorem complexGlobalPhaseClose_api
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    {U V T : Matrix O I ℂ} (z : ℂ) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hUV : ComplexGlobalPhaseClose ε U V)
    (hVT : ComplexGlobalPhaseClose δ V T) :
    (‖z‖ = 1 ↔ Complex.normSq z = 1) ∧
      (ComplexGlobalPhaseClose ε U V ↔
        RCLikeGlobalPhaseClose ε U V) ∧
      (ComplexGlobalPhaseClose 0 U V ↔ ComplexGlobalPhaseEq U V) ∧
      ComplexGlobalPhaseClose ε U U ∧
      ComplexGlobalPhaseClose δ U V ∧
      ComplexGlobalPhaseClose ε V U ∧
      ComplexGlobalPhaseClose (ε + δ) U T :=
  ⟨complex_norm_eq_one_iff_normSq_eq_one z,
    complexGlobalPhaseClose_iff_rclike,
    complexGlobalPhaseClose_zero_iff,
    ComplexGlobalPhaseClose.refl hε U,
    hUV.mono hεδ,
    hUV.symm,
    hUV.additive_trans hVT⟩

/-! ## Exact allocation of the 48 quaternionic operator declarations -/

/-- Complete consumer for all 13 underlying-real quaternionic action declarations. -/
theorem quaternionAction_api
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A B : Matrix m n ℍ[ℝ]) (C : Matrix n l ℍ[ℝ])
    (raw : n → ℍ[ℝ]) (x : QuaternionEuclidean n) (r : ℝ) :
    quaternionMulVecLinear A (toLp 2 raw) = toLp 2 (A *ᵥ raw) ∧
      quaternionMulVecCLM A (toLp 2 raw) = toLp 2 (A *ᵥ raw) ∧
      quaternionMulVecCLM A x = toLp 2 (A *ᵥ x.ofLp) ∧
      quaternionMulVecCLM (0 : Matrix m n ℍ[ℝ]) = 0 ∧
      quaternionMulVecCLM (A + B) =
        quaternionMulVecCLM A + quaternionMulVecCLM B ∧
      quaternionMulVecCLM (-A) = -quaternionMulVecCLM A ∧
      quaternionMulVecCLM (A - B) =
        quaternionMulVecCLM A - quaternionMulVecCLM B ∧
      quaternionMulVecCLM (r • A) = r • quaternionMulVecCLM A ∧
      quaternionMulVecCLM (A * C) =
        (quaternionMulVecCLM A).comp (quaternionMulVecCLM C) ∧
      Function.Injective
        (quaternionMulVecCLM : Matrix m n ℍ[ℝ] →
          QuaternionEuclidean n →L[ℝ] QuaternionEuclidean m) :=
  ⟨quaternionMulVecLinear_toLp A raw,
    quaternionMulVecCLM_toLp A raw,
    quaternionMulVecCLM_apply A x,
    quaternionMulVecCLM_zero,
    quaternionMulVecCLM_add A B,
    quaternionMulVecCLM_neg A,
    quaternionMulVecCLM_sub A B,
    quaternionMulVecCLM_real_smul r A,
    quaternionMulVecCLM_mul A C,
    quaternionMulVecCLM_injective⟩

/-- Complete consumer for the three native definitions and eight norm laws. -/
theorem quaternionNorm_api
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A B : Matrix m n ℍ[ℝ]) (C : Matrix n l ℍ[ℝ])
    (x : QuaternionEuclidean n) {ε : ℝ}
    (hclose : QuaternionOperatorClose ε A B) :
    quaternionOperatorDistance A B = quaternionOperatorNorm (A - B) ∧
      QuaternionOperatorClose ε A B ∧
      0 ≤ quaternionOperatorNorm A ∧
      quaternionOperatorNorm (0 : Matrix m n ℍ[ℝ]) = 0 ∧
      quaternionOperatorNorm (-A) = quaternionOperatorNorm A ∧
      (quaternionOperatorNorm A = 0 ↔ A = 0) ∧
      quaternionOperatorNorm (A + B) ≤
        quaternionOperatorNorm A + quaternionOperatorNorm B ∧
      quaternionOperatorNorm (A - B) ≤
        quaternionOperatorNorm A + quaternionOperatorNorm B ∧
      quaternionOperatorNorm (A * C) ≤
        quaternionOperatorNorm A * quaternionOperatorNorm C ∧
      ‖quaternionMulVecCLM A x‖ ≤ quaternionOperatorNorm A * ‖x‖ :=
  ⟨rfl,
    hclose,
    quaternionOperatorNorm_nonneg A,
    quaternionOperatorNorm_zero,
    quaternionOperatorNorm_neg A,
    quaternionOperatorNorm_eq_zero_iff A,
    quaternionOperatorNorm_add_le A B,
    quaternionOperatorNorm_sub_le A B,
    quaternionOperatorNorm_mul A C,
    quaternionOperatorNorm_mulVec A x⟩

/-- Complete consumer for all 11 native quaternionic distance laws. -/
theorem quaternionDistance_api
    {m : Type u} {n : Type v} {l : Type w}
    [Fintype m] [Fintype n] [Fintype l]
    (A B C D : Matrix m n ℍ[ℝ]) (P Q : Matrix n l ℍ[ℝ])
    (raw : n → ℍ[ℝ]) :
    quaternionOperatorDistance A A = 0 ∧
      0 ≤ quaternionOperatorDistance A B ∧
      quaternionOperatorDistance A B = quaternionOperatorDistance B A ∧
      quaternionOperatorDistance A C ≤
        quaternionOperatorDistance A B + quaternionOperatorDistance B C ∧
      (quaternionOperatorDistance A B = 0 ↔ A = B) ∧
      quaternionOperatorDistance (A + B) (C + D) ≤
        quaternionOperatorDistance A C + quaternionOperatorDistance B D ∧
      quaternionOperatorDistance (A - B) (C - D) ≤
        quaternionOperatorDistance A C + quaternionOperatorDistance B D ∧
      quaternionOperatorDistance (A * P) (C * P) ≤
        quaternionOperatorDistance A C * quaternionOperatorNorm P ∧
      quaternionOperatorDistance (A * P) (A * Q) ≤
        quaternionOperatorNorm A * quaternionOperatorDistance P Q ∧
      quaternionOperatorDistance (A * P) (C * Q) ≤
        quaternionOperatorDistance A C * quaternionOperatorNorm P +
          quaternionOperatorNorm C * quaternionOperatorDistance P Q ∧
      ‖toLp 2 (A *ᵥ raw - B *ᵥ raw)‖ ≤
        quaternionOperatorDistance A B * ‖toLp 2 raw‖ :=
  ⟨quaternionOperatorDistance_self A,
    quaternionOperatorDistance_nonneg A B,
    quaternionOperatorDistance_symm A B,
    quaternionOperatorDistance_triangle A B C,
    quaternionOperatorDistance_eq_zero_iff A B,
    quaternionOperatorDistance_add A B C D,
    quaternionOperatorDistance_sub A B C D,
    quaternionOperatorDistance_mul_right A C P,
    quaternionOperatorDistance_mul_left A P Q,
    quaternionOperatorDistance_mul A C P Q,
    quaternionOperatorDistance_mulVec A B raw⟩

/-- Complete consumer for all five raw quaternionic close laws. -/
theorem quaternionOperatorClose_api
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {A B C : Matrix m n ℍ[ℝ]} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hAB : QuaternionOperatorClose ε A B)
    (hBC : QuaternionOperatorClose δ B C) :
    QuaternionOperatorClose ε A A ∧
      QuaternionOperatorClose δ A B ∧
      QuaternionOperatorClose ε B A ∧
      QuaternionOperatorClose (ε + δ) A C ∧
      (QuaternionOperatorClose 0 A B ↔ ExactOperatorEq A B) :=
  ⟨QuaternionOperatorClose.refl hε A,
    hAB.mono hεδ,
    hAB.symm,
    hAB.additive_trans hBC,
    QuaternionOperatorClose.zero_iff_exactOperatorEq⟩

/-- Complete consumer for the seven central-sign approximation declarations. -/
theorem quaternionCentralSignClose_api
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {U V T : Matrix m n ℍ[ℝ]} {ε δ : ℝ}
    (s : ℝ) (hs : s * s = 1)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hraw : QuaternionOperatorClose ε U V)
    (hUV : QuaternionCentralSignClose ε U V)
    (hVT : QuaternionCentralSignClose δ V T) :
    QuaternionOperatorClose ε (s • U) (s • V) ∧
      QuaternionCentralSignClose ε U U ∧
      QuaternionCentralSignClose δ U V ∧
      QuaternionCentralSignClose ε V U ∧
      QuaternionCentralSignClose (ε + δ) U T ∧
      (QuaternionCentralSignClose 0 U V ↔ QuaternionCentralSignEq U V) :=
  ⟨hraw.sign_smul s hs,
    QuaternionCentralSignClose.refl hε U,
    hUV.mono hεδ,
    hUV.symm,
    hUV.additive_trans hVT,
    QuaternionCentralSignClose.zero_iff_quaternionCentralSignEq⟩

/-- Complete consumer for the complexification/native-norm identification. -/
theorem quaternionComplexificationNorm_api
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) :
    quaternionOperatorNorm A = ‖Quaternion.complexify A‖ :=
  quaternionOperatorNorm_eq_l2_opNorm_complexify A

