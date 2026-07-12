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

/-! ## Exact allocation of the 43 column and state-ray declarations -/

/-- Complete consumer for all 12 raw finite-column metric declarations. -/
theorem columnMetric_api
    {R : Type u} [NormedAddCommGroup R]
    {I : Type v} [Fintype I] (a b c : I → R)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hab : ColumnClose ε a b) (hbc : ColumnClose δ b c) :
    columnL2Distance a a = 0 ∧
      0 ≤ columnL2Distance a b ∧
      columnL2Distance a b = columnL2Distance b a ∧
      columnL2Distance a c ≤ columnL2Distance a b + columnL2Distance b c ∧
      (columnL2Distance a b = 0 ↔ a = b) ∧
      ColumnClose ε a a ∧
      ColumnClose δ a b ∧
      ColumnClose ε b a ∧
      ColumnClose (ε + δ) a c ∧
      (ColumnClose 0 a b ↔ a = b) :=
  ⟨columnL2Distance_self a,
    columnL2Distance_nonneg a b,
    columnL2Distance_symm a b,
    columnL2Distance_triangle a b c,
    columnL2Distance_eq_zero_iff,
    ColumnClose.refl hε a,
    hab.mono hεδ,
    hab.symm,
    hab.additive_trans hbc,
    ColumnClose.zero_iff_eq⟩

/-- Complete consumer for all seven generic right-unit-phase declarations. -/
theorem rightUnitPhaseColumnClose_api
    {R : Type u} [NormedDivisionRing R]
    {I : Type v} [Fintype I] (a b c : I → R)
    (eta : R) (heta : ‖eta‖ = 1)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hab : RightUnitPhaseColumnClose ε a b)
    (hbc : RightUnitPhaseColumnClose δ b c) :
    columnL2Distance (fun i ↦ a i * eta) (fun i ↦ b i * eta) =
        columnL2Distance a b ∧
      RightUnitPhaseColumnClose ε a a ∧
      RightUnitPhaseColumnClose δ a b ∧
      RightUnitPhaseColumnClose ε b a ∧
      RightUnitPhaseColumnClose (ε + δ) a c ∧
      (RightUnitPhaseColumnClose 0 a b ↔
        ∃ q : R, ‖q‖ = 1 ∧ a = fun i ↦ b i * q) :=
  ⟨columnL2Distance_right_mul a b eta heta,
    RightUnitPhaseColumnClose.refl hε a,
    hab.mono hεδ,
    hab.symm,
    hab.additive_trans hbc,
    RightUnitPhaseColumnClose.zero_iff⟩

/-- Complete consumer for the five stable real state-ray declarations. -/
theorem realStateRayClose_api
    {I : Type u} [Fintype I] {a b c : RealState I} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hab : RealStateRayClose ε a b) (hbc : RealStateRayClose δ b c) :
    RealStateRayClose ε a a ∧
      RealStateRayClose δ a b ∧
      RealStateRayClose ε b a ∧
      RealStateRayClose (ε + δ) a c :=
  ⟨RealStateRayClose.refl hε a,
    hab.mono hεδ,
    hab.symm,
    hab.additive_trans hbc⟩

/-- Complete consumer for the five stable complex state-ray declarations. -/
theorem complexStateRayClose_api
    {I : Type u} [Fintype I] {a b c : ComplexState I} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hab : ComplexStateRayClose ε a b)
    (hbc : ComplexStateRayClose δ b c) :
    ComplexStateRayClose ε a a ∧
      ComplexStateRayClose δ a b ∧
      ComplexStateRayClose ε b a ∧
      ComplexStateRayClose (ε + δ) a c :=
  ⟨ComplexStateRayClose.refl hε a,
    hab.mono hεδ,
    hab.symm,
    hab.additive_trans hbc⟩

/-- Complete consumer for the five stable quaternionic state-ray declarations. -/
theorem quaternionStateRayClose_api
    {I : Type u} [Fintype I] {a b c : QuaternionState I} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hab : QuaternionStateRayClose ε a b)
    (hbc : QuaternionStateRayClose δ b c) :
    QuaternionStateRayClose ε a a ∧
      QuaternionStateRayClose δ a b ∧
      QuaternionStateRayClose ε b a ∧
      QuaternionStateRayClose (ε + δ) a c :=
  ⟨QuaternionStateRayClose.refl hε a,
    hab.mono hεδ,
    hab.symm,
    hab.additive_trans hbc⟩

/-- Complete consumer for the three exact zero-budget state-ray bridges. -/
theorem stateRayZeroBridges_api
    {I : Type u} [Fintype I]
    {aR bR : RealState I} {aC bC : ComplexState I}
    {aQ bQ : QuaternionState I} :
    (RealStateRayClose 0 aR bR ↔ RealStatePhaseEq aR bR) ∧
      (ComplexStateRayClose 0 aC bC ↔ ComplexStatePhaseEq aC bC) ∧
      (QuaternionStateRayClose 0 aQ bQ ↔ QuaternionStatePhaseEq aQ bQ) :=
  ⟨realStateRayClose_zero_iff_realStatePhaseEq,
    complexStateRayClose_zero_iff_complexStatePhaseEq,
    quaternionStateRayClose_zero_iff_quaternionStatePhaseEq⟩

/-- Complete consumer for the six normalized-input norm and output declarations. -/
theorem normalizedStateOutput_api
    {O : Type u} {I : Type v} [Fintype O] [Fintype I]
    (aR : RealState I) (aC : ComplexState I) (aQ : QuaternionState I)
    (UR VR : Matrix O I ℝ) (UC VC : Matrix O I ℂ)
    (UQ VQ : Matrix O I ℍ[ℝ]) :
    ‖toLp 2 (aR : I → ℝ)‖ = 1 ∧
      ‖toLp 2 (aC : I → ℂ)‖ = 1 ∧
      ‖toLp 2 (aQ : I → ℍ[ℝ])‖ = 1 ∧
      columnL2Distance (UR *ᵥ (aR : I → ℝ)) (VR *ᵥ (aR : I → ℝ)) ≤
        operatorDistance UR VR ∧
      columnL2Distance (UC *ᵥ (aC : I → ℂ)) (VC *ᵥ (aC : I → ℂ)) ≤
        operatorDistance UC VC ∧
      columnL2Distance (UQ *ᵥ (aQ : I → ℍ[ℝ]))
          (VQ *ᵥ (aQ : I → ℍ[ℝ])) ≤
        quaternionOperatorDistance UQ VQ :=
  ⟨realState_l2Norm_eq_one aR,
    complexState_l2Norm_eq_one aC,
    quaternionState_l2Norm_eq_one aQ,
    operatorDistance_realState_output_le UR VR aR,
    operatorDistance_complexState_output_le UC VC aC,
    quaternionOperatorDistance_quaternionState_output_le UQ VQ aQ⟩

/-! ## Exact allocation of the 17 total-variation declarations -/

/-- Complete consumer for the 13 total-variation metric and budget declarations. -/
theorem distributionMetric_api
    {I : Type u} [Fintype I]
    (mu nu xi : FiniteDistribution I) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hmunu : DistributionClose ε mu nu)
    (hnuxi : DistributionClose δ nu xi) :
    totalVariationDistance mu mu = 0 ∧
      0 ≤ totalVariationDistance mu nu ∧
      totalVariationDistance mu nu = totalVariationDistance nu mu ∧
      totalVariationDistance mu xi ≤
        totalVariationDistance mu nu + totalVariationDistance nu xi ∧
      (totalVariationDistance mu nu = 0 ↔ mu = nu) ∧
      DistributionClose ε mu mu ∧
      DistributionClose δ mu nu ∧
      DistributionClose ε nu mu ∧
      DistributionClose (ε + δ) mu xi ∧
      (DistributionClose 0 mu nu ↔ mu = nu) ∧
      totalVariationDistance mu nu ≤ 1 :=
  ⟨totalVariationDistance_self mu,
    totalVariationDistance_nonneg mu nu,
    totalVariationDistance_symm mu nu,
    totalVariationDistance_triangle mu nu xi,
    totalVariationDistance_eq_zero_iff,
    DistributionClose.refl hε mu,
    hmunu.mono hεδ,
    hmunu.symm,
    hmunu.additive_trans hnuxi,
    distributionClose_zero_iff,
    totalVariationDistance_le_one mu nu⟩

/-- Complete consumer for the four TV event, point, and pushforward declarations. -/
theorem distributionObservable_api
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (mu nu : FiniteDistribution I) (event : Finset I) (i : I)
    (f : I → J) {ε : ℝ} (hclose : DistributionClose ε mu nu) :
    |mu.eventWeight event - nu.eventWeight event| ≤
        totalVariationDistance mu nu ∧
      |mu.weight i - nu.weight i| ≤ totalVariationDistance mu nu ∧
      totalVariationDistance (mu.pushforward f) (nu.pushforward f) ≤
        totalVariationDistance mu nu ∧
      DistributionClose ε (mu.pushforward f) (nu.pushforward f) :=
  ⟨abs_eventWeight_sub_le_totalVariationDistance mu nu event,
    abs_weight_sub_le_totalVariationDistance mu nu i,
    totalVariationDistance_pushforward_le mu nu f,
    hclose.pushforward f⟩

/-! ## Exact allocation of the 14 strictness declarations -/

/-- Complete consumer for the nine exact scalar-matrix strictness declarations. -/
theorem operatorStrictness_api :
    operatorDistance (scalarMatrix (0 : ℝ)) (scalarMatrix 1) =
        dist (0 : ℝ) 1 ∧
      (OperatorClose 1 (scalarMatrix (0 : ℝ)) (scalarMatrix 1) ∧
        OperatorClose 1 (scalarMatrix (1 : ℝ)) (scalarMatrix 2) ∧
        ¬ OperatorClose 1 (scalarMatrix (0 : ℝ)) (scalarMatrix 2)) ∧
      scalarMatrix (1 : ℂ) ∈ unitary (Matrix Unit Unit ℂ) ∧
      (scalarMatrix (1 : ℂ) ∈ unitary (Matrix Unit Unit ℂ) ∧
        scalarMatrix Complex.I ∈ unitary (Matrix Unit Unit ℂ) ∧
        scalarMatrix (-1 : ℂ) ∈ unitary (Matrix Unit Unit ℂ)) ∧
      (operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix Complex.I) = √2 ∧
        operatorDistance (scalarMatrix Complex.I) (scalarMatrix (-1 : ℂ)) = √2 ∧
        operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) = 2) ∧
      (OperatorClose √2 (scalarMatrix (1 : ℂ)) (scalarMatrix Complex.I) ∧
        OperatorClose √2 (scalarMatrix Complex.I) (scalarMatrix (-1 : ℂ)) ∧
        ¬ OperatorClose √2 (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ))) ∧
      operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) = 2 ∧
      (operatorDistance (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ)) = 2 ∧
        ComplexGlobalPhaseClose 0 (scalarMatrix (1 : ℂ)) (scalarMatrix (-1 : ℂ))) :=
  ⟨operatorDistance_scalarMatrix (0 : ℝ) (1 : ℝ),
    operatorClose_one_not_transitive,
    complexScalarMatrix_mem_unitary 1 (by norm_num [Complex.normSq_apply]),
    complexScalarPhaseChain_unitary,
    complexScalarPhaseChain_distances,
    operatorClose_sqrtTwo_not_transitive_on_complex_unitaries,
    rawDistance_one_negOne_eq_two,
    rawDistance_one_negOne_eq_two_and_complexGlobalPhaseClose_zero⟩

/-- Complete consumer for the five exact Boolean-distribution strictness declarations. -/
theorem distributionStrictness_api :
    (totalVariationDistance deltaFalse fairBool = 1 / 2 ∧
      totalVariationDistance fairBool deltaTrue = 1 / 2 ∧
      totalVariationDistance deltaFalse deltaTrue = 1) ∧
    (DistributionClose (1 / 2) deltaFalse fairBool ∧
      DistributionClose (1 / 2) fairBool deltaTrue ∧
      ¬ DistributionClose (1 / 2) deltaFalse deltaTrue) :=
  ⟨totalVariation_bool_chain, distributionClose_half_not_transitive⟩

/-! ## Concrete boundary consumers -/

/-- The singleton zero-wire basis and a nontrivial scalar phase are genuine unitaries. -/
theorem zeroWire_and_nontrivialUnitary :
    (1 : Matrix (Circuit.BitBasis Empty) (Circuit.BitBasis Empty) ℂ) ∈
        unitary (Matrix (Circuit.BitBasis Empty) (Circuit.BitBasis Empty) ℂ) ∧
      OperatorClose 0
        (1 : Matrix (Circuit.BitBasis Empty) (Circuit.BitBasis Empty) ℂ) 1 ∧
      scalarMatrix Complex.I ∈ unitary (Matrix Unit Unit ℂ) := by
  exact ⟨(unitary
      (Matrix (Circuit.BitBasis Empty) (Circuit.BitBasis Empty) ℂ)).one_mem,
    OperatorClose.refl 1 le_rfl,
    complexScalarPhaseChain_unitary.2.1⟩

/-- Entrywise real-to-complex embedding used by the concrete mapped consumer. -/
def realToComplexMatrix {O : Type u} {I : Type v} (A : Matrix O I ℝ) :
    Matrix O I ℂ :=
  fun i j ↦ A i j

/-- The mapped zero budget recovers the exact directional embedding certificate. -/
theorem mapped_realToComplex_zero :
    ExactOperatorEmbedding realToComplexMatrix (scalarMatrix (1 : ℝ))
        (realToComplexMatrix (scalarMatrix (1 : ℝ))) ∧
      MappedOperatorClose 0 realToComplexMatrix (scalarMatrix (1 : ℝ))
        (realToComplexMatrix (scalarMatrix (1 : ℝ))) := by
  have hexact : ExactOperatorEmbedding realToComplexMatrix
      (scalarMatrix (1 : ℝ))
      (realToComplexMatrix (scalarMatrix (1 : ℝ))) := rfl
  exact ⟨hexact,
    mappedOperatorClose_zero_iff_exactOperatorEmbedding.mpr hexact⟩

/-- The generic state phase is visibly on the right, including for quaternions. -/
theorem quaternion_rightPhase_side
    (x : Unit → ℍ[ℝ]) (eta : ℍ[ℝ]) (heta : ‖eta‖ = 1) :
    RightUnitPhaseColumnClose 0 (fun i ↦ x i * eta) x := by
  exact ⟨eta, heta, ColumnClose.zero_iff_eq.mpr rfl⟩

/-- Concrete normalized singleton states for all three scalar conventions. -/
def unitRealState : RealState Unit :=
  ⟨fun _ ↦ 1, by simp [State.totalWeight, State.basisWeight, State.realWeight]⟩

def unitComplexState : ComplexState Unit :=
  ⟨fun _ ↦ 1, by simp [State.totalWeight, State.basisWeight, State.complexWeight]⟩

def unitQuaternionState : QuaternionState Unit :=
  ⟨fun _ ↦ 1, by
    simp [State.totalWeight, State.basisWeight, State.quaternionWeight,
      _root_.Quaternion.normSq_def']⟩

/-- Normalized singleton inputs instantiate all three output-column error bounds. -/
theorem normalizedSingleton_outputBounds :
    columnL2Distance
        ((1 : Matrix Unit Unit ℝ) *ᵥ (unitRealState : Unit → ℝ))
        ((0 : Matrix Unit Unit ℝ) *ᵥ (unitRealState : Unit → ℝ)) ≤
        operatorDistance (1 : Matrix Unit Unit ℝ) 0 ∧
      columnL2Distance
        ((1 : Matrix Unit Unit ℂ) *ᵥ (unitComplexState : Unit → ℂ))
        ((0 : Matrix Unit Unit ℂ) *ᵥ (unitComplexState : Unit → ℂ)) ≤
        operatorDistance (1 : Matrix Unit Unit ℂ) 0 ∧
      columnL2Distance
        ((1 : Matrix Unit Unit ℍ[ℝ]) *ᵥ (unitQuaternionState : Unit → ℍ[ℝ]))
        ((0 : Matrix Unit Unit ℍ[ℝ]) *ᵥ (unitQuaternionState : Unit → ℍ[ℝ])) ≤
        quaternionOperatorDistance (1 : Matrix Unit Unit ℍ[ℝ]) 0 :=
  ⟨operatorDistance_realState_output_le 1 0 unitRealState,
    operatorDistance_complexState_output_le 1 0 unitComplexState,
    quaternionOperatorDistance_quaternionState_output_le 1 0 unitQuaternionState⟩

/-- Boolean event bounds and deterministic postprocessing are concrete TV consumers. -/
theorem boolEvent_and_pushforward :
    |deltaFalse.eventWeight {false} - fairBool.eventWeight {false}| ≤
        totalVariationDistance deltaFalse fairBool ∧
      totalVariationDistance
          (deltaFalse.pushforward fun _ ↦ ()) (fairBool.pushforward fun _ ↦ ()) ≤
        totalVariationDistance deltaFalse fairBool ∧
      DistributionClose (1 / 2)
        (deltaFalse.pushforward fun _ ↦ ()) (fairBool.pushforward fun _ ↦ ()) := by
  exact ⟨abs_eventWeight_sub_le_totalVariationDistance
      deltaFalse fairBool {false},
    totalVariationDistance_pushforward_le deltaFalse fairBool (fun _ ↦ ()),
    distributionClose_half_not_transitive.1.pushforward (fun _ ↦ ())⟩

/-! ## Representative local axiom audit -/

#print axioms operatorMetric_api
#print axioms operatorPerturbation_api
#print axioms mappedOperator_api
#print axioms complexGlobalPhaseClose_api
#print axioms quaternionAction_api
#print axioms quaternionComplexificationNorm_api
#print axioms quaternionStateRayClose_api
#print axioms normalizedStateOutput_api
#print axioms distributionObservable_api
#print axioms operatorStrictness_api
#print axioms distributionStrictness_api
#print axioms zeroWire_and_nontrivialUnitary
#print axioms mapped_realToComplex_zero
#print axioms quaternion_rightPhase_side
#print axioms normalizedSingleton_outputBounds
#print axioms boolEvent_and_pushforward

end QuaternionicComputing.Semantics.ApproximationAudit
