module

public import QuaternionicComputing.Semantics.EffectSeparation

/-!
# Density, effect, and physical-separation audit

This non-root diagnostic leaf is the complete Stage 6 consumer.  It imports
only `EffectSeparation`, exercises every explicitly named stable declaration
from `Density`, `Effect`, and `EffectSeparation`, and gives concrete real and
complex two-level examples.

The exact aggregate allocation is `33 + 1 + 6 = 40` density declarations,
`17 + 11 + 20 + 4 = 52` effect declarations, and `5` separation declarations,
for `97/97` total coverage.  Generated structure projections are excluded
consistently.  The two anonymous matrix-coercion instances are exercised by
the aggregate statements but are not counted as named declarations.

The examples include normalized pure states, computational-basis densities
and effects, the genuinely mixed real state `(1/2) I`, unitary conjugation,
Born bounds and complementation, physical-effect separation, and the exact
empty-index obstruction.  This file is intentionally absent from the public
root.
-/

@[expose] public noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix

namespace QuaternionicComputing.Semantics.DensityAudit

open QuaternionicComputing.State

universe u v w

/-! ## Complete density consumers -/

/-- Complete aggregate consumer for 33 generic nonempty density declarations. -/
theorem density_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (ρ σ : DensityMatrix 𝕜 I) (hρσ : ρ = σ)
    (ψ : I → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1) (x i j : I)
    (U V : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜))
    (hV : V ∈ unitary (Matrix I I 𝕜)) :
    ((ρ : Matrix I I 𝕜) = ρ.matrix) ∧
      ρ = σ ∧
      ρ = σ ∧
      (ρ = σ ↔
        ∀ a b, (ρ : Matrix I I 𝕜) a b = (σ : Matrix I I 𝕜) a b) ∧
      (ρ : Matrix I I 𝕜).IsHermitian ∧
      (ρ : Matrix I I 𝕜)ᴴ = (ρ : Matrix I I 𝕜) ∧
      Matrix.trace (ρ : Matrix I I 𝕜) = 1 ∧
      Nonempty I ∧
      DensityMatrix.pureMatrix ψ i j = ψ i * star (ψ j) ∧
      (DensityMatrix.pureMatrix ψ).PosSemidef ∧
      Matrix.trace (DensityMatrix.pureMatrix ψ) = star ψ ⬝ᵥ ψ ∧
      (((DensityMatrix.pure ψ hψ : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
        DensityMatrix.pureMatrix ψ) ∧
      ((DensityMatrix.pure ψ hψ : DensityMatrix 𝕜 I) : Matrix I I 𝕜) i j =
        ψ i * star (ψ j) ∧
      (((DensityMatrix.pure ψ hψ : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜)).PosSemidef ∧
      Matrix.trace
        ((DensityMatrix.pure ψ hψ : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = 1 ∧
      (((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜) = DensityMatrix.pureMatrix (Pi.single x 1)) ∧
      ((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜) i j = (if i = x ∧ j = x then 1 else 0) ∧
      (((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜)).PosSemidef ∧
      Matrix.trace
        ((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = 1 ∧
      (Nonempty (DensityMatrix 𝕜 I) ↔ Nonempty I) ∧
      (((DensityMatrix.unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜) = U * (ρ : Matrix I I 𝕜) * Uᴴ) ∧
      (((DensityMatrix.unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜)).PosSemidef ∧
      (((DensityMatrix.unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜)).IsHermitian ∧
      Matrix.trace
        ((DensityMatrix.unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) :
          Matrix I I 𝕜) = 1 ∧
      DensityMatrix.unitaryConjugate 1
        (unitary (Matrix I I 𝕜)).one_mem ρ = ρ ∧
      DensityMatrix.unitaryConjugate V hV
          (DensityMatrix.unitaryConjugate U hU ρ) =
        DensityMatrix.unitaryConjugate (V * U)
          ((unitary (Matrix I I 𝕜)).mul_mem hV hU) ρ ∧
      (((DensityMatrix.unitaryConjugate U hU
          (DensityMatrix.pure ψ hψ) : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
        DensityMatrix.pureMatrix (U *ᵥ ψ)) ∧
      DensityMatrix.unitaryConjugate U hU (DensityMatrix.pure ψ hψ) =
        DensityMatrix.pure (U *ᵥ ψ) (by
          calc
            star (U *ᵥ ψ) ⬝ᵥ (U *ᵥ ψ) = star ψ ⬝ᵥ ψ :=
              State.star_dotProduct_mulVec_of_mem_unitary hU ψ
            _ = 1 := hψ) := by
  have hmatrix : (ρ : Matrix I I 𝕜) = (σ : Matrix I I 𝕜) :=
    congrArg (fun τ : DensityMatrix 𝕜 I ↦ (τ : Matrix I I 𝕜)) hρσ
  have hentries :
      ∀ a b, (ρ : Matrix I I 𝕜) a b = (σ : Matrix I I 𝕜) a b :=
    fun a b ↦ congrFun (congrFun hmatrix a) b
  exact ⟨DensityMatrix.coe_matrix ρ,
    DensityMatrix.ext_matrix hmatrix,
    DensityMatrix.ext hentries,
    DensityMatrix.eq_iff_entries,
    DensityMatrix.isHermitian ρ,
    DensityMatrix.conjTranspose_eq ρ,
    DensityMatrix.trace_eq_one ρ,
    DensityMatrix.index_nonempty ρ,
    DensityMatrix.pureMatrix_apply ψ i j,
    DensityMatrix.pureMatrix_posSemidef ψ,
    DensityMatrix.trace_pureMatrix ψ,
    DensityMatrix.pure_coe ψ hψ,
    DensityMatrix.pure_apply ψ hψ i j,
    DensityMatrix.pure_posSemidef ψ hψ,
    DensityMatrix.trace_pure ψ hψ,
    DensityMatrix.basis_coe (𝕜 := 𝕜) x,
    DensityMatrix.basis_apply (𝕜 := 𝕜) x i j,
    DensityMatrix.basis_posSemidef (𝕜 := 𝕜) x,
    DensityMatrix.trace_basis (𝕜 := 𝕜) x,
    DensityMatrix.nonempty_iff,
    DensityMatrix.unitaryConjugate_coe U hU ρ,
    DensityMatrix.unitaryConjugate_posSemidef U hU ρ,
    DensityMatrix.unitaryConjugate_isHermitian U hU ρ,
    DensityMatrix.trace_unitaryConjugate U hU ρ,
    DensityMatrix.unitaryConjugate_one ρ,
    DensityMatrix.unitaryConjugate_comp U V hU hV ρ,
    DensityMatrix.unitaryConjugate_pure_coe U hU ψ hψ,
    DensityMatrix.unitaryConjugate_pure U hU ψ hψ⟩

/-- Complete consumer for the one density obstruction declaration on an empty index type. -/
theorem density_empty_api {𝕜 : Type u} [RCLike 𝕜] :
    IsEmpty (DensityMatrix 𝕜 Empty) :=
  DensityMatrix.isEmpty_of_index_isEmpty

/-- Complete consumer for six real/complex density aliases and state declarations. -/
theorem density_scalar_api
    (r : State.RealState Bool) (c : State.ComplexState Bool) (i j : Bool) :
    (((RealDensityMatrix.ofState r : RealDensityMatrix Bool) :
        Matrix Bool Bool ℝ) i j = r i * r j) ∧
      (((ComplexDensityMatrix.ofState c : ComplexDensityMatrix Bool) :
        Matrix Bool Bool ℂ) i j = c i * star (c j)) :=
  ⟨RealDensityMatrix.ofState_apply r i j,
    ComplexDensityMatrix.ofState_apply c i j⟩

/-! ## Complete effect consumers -/

/-- Complete aggregate consumer for 17 effect structure, order, and complement declarations. -/
theorem effect_structure_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (E F : Effect 𝕜 I) (hEF : E = F) :
    ((E : Matrix I I 𝕜) = E.matrix) ∧
      E = F ∧
      E = F ∧
      (E = F ↔ ∀ i j, (E : Matrix I I 𝕜) i j = (F : Matrix I I 𝕜) i j) ∧
      (E : Matrix I I 𝕜).PosSemidef ∧
      (E : Matrix I I 𝕜).IsHermitian ∧
      (1 - (E : Matrix I I 𝕜)).PosSemidef ∧
      (((Effect.zero : Effect 𝕜 I) : Matrix I I 𝕜) = 0) ∧
      (((Effect.one : Effect 𝕜 I) : Matrix I I 𝕜) = 1) ∧
      (((Effect.complement E : Effect 𝕜 I) : Matrix I I 𝕜) =
        1 - (E : Matrix I I 𝕜)) ∧
      Effect.complement (Effect.complement E) = E ∧
      Effect.complement (Effect.zero : Effect 𝕜 I) = Effect.one ∧
      Effect.complement (Effect.one : Effect 𝕜 I) = Effect.zero := by
  have hmatrix : (E : Matrix I I 𝕜) = (F : Matrix I I 𝕜) :=
    congrArg (fun G : Effect 𝕜 I ↦ (G : Matrix I I 𝕜)) hEF
  have hentries :
      ∀ i j, (E : Matrix I I 𝕜) i j = (F : Matrix I I 𝕜) i j :=
    fun i j ↦ congrFun (congrFun hmatrix i) j
  exact ⟨Effect.coe_matrix E,
    Effect.ext_matrix hmatrix,
    Effect.ext hentries,
    Effect.eq_iff_entries,
    Effect.posSemidef E,
    Effect.isHermitian E,
    Effect.complement_posSemidef E,
    Effect.zero_coe,
    Effect.one_coe,
    Effect.complement_coe E,
    Effect.complement_complement E,
    Effect.complement_zero,
    Effect.complement_one⟩

/-- Complete aggregate consumer for 11 normalized rank-one and basis-effect declarations. -/
theorem effect_projector_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (z : EuclideanSpace 𝕜 I) (hz : ‖z‖ = 1) (x i j : I) :
    Effect.rankOneProjector z = Matrix.vecMulVec z.ofLp (star z.ofLp) ∧
      Effect.rankOneProjector z i j = z i * star (z j) ∧
      (Effect.rankOneProjector z).PosSemidef ∧
      Effect.rankOneProjector z ≤ (1 : Matrix I I 𝕜) ∧
      (((Effect.projector z hz : Effect 𝕜 I) : Matrix I I 𝕜) =
        Effect.rankOneProjector z) ∧
      ((Effect.basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) i j =
        (if i = x ∧ j = x then 1 else 0) ∧
      (((Effect.basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) =
        Matrix.single x x 1) ∧
      (((Effect.basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) =
        ((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜)) :=
  ⟨Effect.rankOneProjector_eq_vecMulVec z,
    Effect.rankOneProjector_apply z i j,
    Effect.rankOneProjector_posSemidef z hz,
    Effect.rankOneProjector_le_one z hz,
    Effect.projector_coe z hz,
    Effect.basis_apply (𝕜 := 𝕜) x i j,
    Effect.basis_coe_eq_single (𝕜 := 𝕜) x,
    Effect.basis_coe_eq_density_basis (𝕜 := 𝕜) x⟩

/-- Complete aggregate consumer for 20 Born-pairing, bound, and basis declarations. -/
theorem effect_born_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (E : Effect 𝕜 I) (ρ : DensityMatrix 𝕜 I)
    {A B : Matrix I I 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (ψ : I → 𝕜) (hψ : star ψ ⬝ᵥ ψ = 1) (x y : I) :
    0 ≤ Matrix.trace (A * B) ∧
      0 ≤ Effect.bornScalar E ρ ∧
      RCLike.im (Effect.bornScalar E ρ) = 0 ∧
      (Effect.bornValue E ρ : 𝕜) = Effect.bornScalar E ρ ∧
      0 ≤ Effect.bornValue E ρ ∧
      Effect.bornScalar E ρ ≤ 1 ∧
      Effect.bornValue E ρ ≤ 1 ∧
      Effect.bornValue E ρ ∈ Set.Icc (0 : ℝ) 1 ∧
      Effect.bornScalar (Effect.zero : Effect 𝕜 I) ρ = 0 ∧
      Effect.bornValue (Effect.zero : Effect 𝕜 I) ρ = 0 ∧
      Effect.bornScalar (Effect.one : Effect 𝕜 I) ρ = 1 ∧
      Effect.bornValue (Effect.one : Effect 𝕜 I) ρ = 1 ∧
      Effect.bornScalar (Effect.complement E) ρ =
        1 - Effect.bornScalar E ρ ∧
      Effect.bornValue (Effect.complement E) ρ =
        1 - Effect.bornValue E ρ ∧
      Effect.bornScalar (Effect.basis (𝕜 := 𝕜) x) ρ =
        (ρ : Matrix I I 𝕜) x x ∧
      Effect.bornValue (Effect.basis (𝕜 := 𝕜) x) ρ =
        RCLike.re ((ρ : Matrix I I 𝕜) x x) ∧
      Effect.bornValue (Effect.basis (𝕜 := 𝕜) x)
          (DensityMatrix.pure ψ hψ) = RCLike.normSq (ψ x) ∧
      Effect.bornValue (Effect.basis (𝕜 := 𝕜) y)
          (DensityMatrix.basis (𝕜 := 𝕜) x) =
        (if y = x then 1 else 0) :=
  ⟨Effect.trace_mul_nonneg_of_posSemidef hA hB,
    Effect.bornScalar_nonneg E ρ,
    Effect.bornScalar_im_eq_zero E ρ,
    Effect.ofReal_bornValue E ρ,
    Effect.bornValue_nonneg E ρ,
    Effect.bornScalar_le_one E ρ,
    Effect.bornValue_le_one E ρ,
    Effect.bornValue_mem_Icc E ρ,
    Effect.bornScalar_zero ρ,
    Effect.bornValue_zero ρ,
    Effect.bornScalar_one ρ,
    Effect.bornValue_one ρ,
    Effect.bornScalar_complement E ρ,
    Effect.bornValue_complement E ρ,
    Effect.bornScalar_basis x ρ,
    Effect.bornValue_basis x ρ,
    Effect.bornValue_basis_pure x ψ hψ,
    Effect.bornValue_basis_basis x y⟩

/-- Complete consumer for four real/complex effect aliases and state declarations. -/
theorem effect_scalar_api
    (r : State.RealState Bool) (c : State.ComplexState Bool) (x : Bool) :
    Nonempty (RealEffect Bool) ∧
      Nonempty (ComplexEffect Bool) ∧
      Effect.bornValue (Effect.basis (𝕜 := ℝ) x)
          (RealDensityMatrix.ofState r) = State.realBasisWeight r x ∧
      Effect.bornValue (Effect.basis (𝕜 := ℂ) x)
          (ComplexDensityMatrix.ofState c) = State.complexBasisWeight c x :=
  ⟨⟨Effect.basis (𝕜 := ℝ) x⟩,
    ⟨Effect.basis (𝕜 := ℂ) x⟩,
    RealEffect.bornValue_basis_ofState x r,
    ComplexEffect.bornValue_basis_ofState x c⟩

/-! ## Complete separation consumer -/

/-- Complete aggregate consumer for all five physical-effect separation exports. -/
theorem separation_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (z : EuclideanSpace 𝕜 I) (A B : Matrix I I 𝕜)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : ∀ E : Effect 𝕜 I,
      RCLike.re (Matrix.trace ((E : Matrix I I 𝕜) * A)) =
        RCLike.re (Matrix.trace ((E : Matrix I I 𝕜) * B)))
    (S T : EuclideanSpace 𝕜 I →ₗ[𝕜] EuclideanSpace 𝕜 I)
    (hunit : ∀ y, ‖y‖ = 1 → inner 𝕜 (S y) y = inner 𝕜 (T y) y)
    (ρ σ : DensityMatrix 𝕜 I)
    (hborn : ∀ E : Effect 𝕜 I,
      Effect.bornValue E ρ = Effect.bornValue E σ) :
    Matrix.trace (Effect.rankOneProjector z * A) =
        inner 𝕜 z (Matrix.toEuclideanLin A z) ∧
      (∀ y, inner 𝕜 (S y) y = inner 𝕜 (T y) y) ∧
      A = B ∧
      (ρ = σ ↔ ∀ E : Effect 𝕜 I,
        Effect.bornValue E ρ = Effect.bornValue E σ) ∧
      ρ = σ :=
  ⟨Effect.trace_rankOneProjector_mul_eq_inner z A,
    quadratic_eq_of_unit_sphere S T hunit,
    posSemidef_eq_of_forall_effect_trace_re_eq hA hB htrace,
    DensityMatrix.eq_iff_forall_effect_bornValue_eq ρ σ,
    DensityMatrix.eq_of_forall_effect_bornValue_eq ρ σ hborn⟩

/-! ## Concrete real and complex two-level examples -/

/-- The real computational-basis state at `false`. -/
def realFalseState : State.RealState Bool :=
  ⟨Pi.single false 1, by
    simp [State.totalWeight, State.basisWeight,
      State.realWeight, Fintype.univ_bool, Pi.single_apply]⟩

/-- The complex computational-basis state at `true`, with amplitude `I`. -/
def complexIState : State.ComplexState Bool :=
  ⟨Pi.single true Complex.I, by
    simp [State.totalWeight, State.basisWeight,
      State.complexWeight, Fintype.univ_bool, Pi.single_apply]⟩

/-- The real basis state becomes the matching basis density and is detected certainly. -/
theorem real_pure_basis_compatibility :
    RealDensityMatrix.ofState realFalseState =
        DensityMatrix.basis (𝕜 := ℝ) false ∧
      Effect.bornValue (Effect.basis (𝕜 := ℝ) false)
        (RealDensityMatrix.ofState realFalseState) = 1 := by
  constructor
  · apply DensityMatrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [realFalseState, RealDensityMatrix.ofState_apply,
        DensityMatrix.basis_apply]
  · simpa [realFalseState, State.realBasisWeight, State.basisWeight,
      State.realWeight, Pi.single_apply] using
      RealEffect.bornValue_basis_ofState false realFalseState

/-- The phase-`I` complex basis state has the same density as the matching basis ket. -/
theorem complex_pure_basis_compatibility :
    ComplexDensityMatrix.ofState complexIState =
        DensityMatrix.basis (𝕜 := ℂ) true ∧
      Effect.bornValue (Effect.basis (𝕜 := ℂ) true)
        (ComplexDensityMatrix.ofState complexIState) = 1 := by
  constructor
  · apply DensityMatrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [complexIState, ComplexDensityMatrix.ofState_apply,
        DensityMatrix.basis_apply]
  · simpa [complexIState, State.complexBasisWeight, State.basisWeight,
      State.complexWeight, Pi.single_apply] using
      ComplexEffect.bornValue_basis_ofState true complexIState

/-- The maximally mixed real two-level density `(1/2) I`. -/
def realMaximallyMixed : RealDensityMatrix Bool where
  matrix := (1 / 2 : ℝ) • (1 : Matrix Bool Bool ℝ)
  posSemidef := Matrix.PosSemidef.smul Matrix.PosSemidef.one (by norm_num)
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num

/-- The maximally mixed density is not a rank-one pure density. -/
theorem realMaximallyMixed_not_pure
    (ψ : Bool → ℝ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    realMaximallyMixed ≠ DensityMatrix.pure ψ hψ := by
  intro h
  have hm :
      (realMaximallyMixed : Matrix Bool Bool ℝ) =
        (DensityMatrix.pure ψ hψ : Matrix Bool Bool ℝ) :=
    congrArg (fun ρ : RealDensityMatrix Bool ↦ (ρ : Matrix Bool Bool ℝ)) h
  have hff := congrFun (congrFun hm false) false
  have htt := congrFun (congrFun hm true) true
  have hft := congrFun (congrFun hm false) true
  have hψf : ψ false ≠ 0 := by
    intro hz
    simp [realMaximallyMixed, DensityMatrix.pure_apply, hz] at hff
  have hψt : ψ true ≠ 0 := by
    intro hz
    simp [realMaximallyMixed, DensityMatrix.pure_apply, hz] at htt
  have : ψ false * ψ true = 0 := by
    simpa [realMaximallyMixed, DensityMatrix.pure_apply] using hft.symm
  exact (mul_ne_zero hψf hψt) this

/-- Every basis outcome of the maximally mixed rebit has probability `1/2`. -/
theorem realMaximallyMixed_basis_probability (x : Bool) :
    Effect.bornValue (Effect.basis (𝕜 := ℝ) x) realMaximallyMixed = 1 / 2 := by
  rw [Effect.bornValue_basis]
  simp [realMaximallyMixed]

/-- Complementary basis outcomes on the maximally mixed state also have probability `1/2`. -/
theorem realMaximallyMixed_complement_probability (x : Bool) :
    Effect.bornValue (Effect.complement (Effect.basis (𝕜 := ℝ) x))
        realMaximallyMixed = 1 / 2 := by
  rw [Effect.bornValue_complement, realMaximallyMixed_basis_probability]
  norm_num

/-- The general Born bounds specialize nonvacuously to the maximally mixed state. -/
theorem realMaximallyMixed_bounds (E : RealEffect Bool) :
    Effect.bornValue E realMaximallyMixed ∈ Set.Icc (0 : ℝ) 1 :=
  Effect.bornValue_mem_Icc E realMaximallyMixed

/-- The real global-sign matrix is unitary. -/
theorem realNegIdentity_mem_unitary :
    (-1 : Matrix Bool Bool ℝ) ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> simp

/-- Global-sign unitary conjugation fixes the maximally mixed density. -/
theorem realMaximallyMixed_globalSign_conjugate :
    DensityMatrix.unitaryConjugate (-1 : Matrix Bool Bool ℝ)
        realNegIdentity_mem_unitary realMaximallyMixed = realMaximallyMixed := by
  apply DensityMatrix.ext_matrix
  simp [DensityMatrix.unitaryConjugate_coe]

/-- A genuine basis effect physically separates the two real basis densities. -/
theorem real_basis_densities_effect_separated :
    ∃ E : RealEffect Bool,
      Effect.bornValue E (DensityMatrix.basis (𝕜 := ℝ) false) ≠
        Effect.bornValue E (DensityMatrix.basis (𝕜 := ℝ) true) := by
  refine ⟨Effect.basis (𝕜 := ℝ) false, ?_⟩
  norm_num [Effect.bornValue_basis_basis]

/-- Equality of all genuine complex-effect outcomes forces equality of states. -/
theorem complex_effects_separate
    (ρ σ : ComplexDensityMatrix Bool)
    (h : ∀ E : ComplexEffect Bool,
      Effect.bornValue E ρ = Effect.bornValue E σ) :
    ρ = σ :=
  DensityMatrix.eq_of_forall_effect_bornValue_eq ρ σ h

/-- No real density matrix exists on the empty finite index type. -/
theorem real_empty_density_impossible :
    ¬ Nonempty (RealDensityMatrix Empty) := by
  rintro ⟨ρ⟩
  exact (DensityMatrix.isEmpty_of_index_isEmpty (𝕜 := ℝ)).false ρ

/-! ## Representative axiom audit -/

#print axioms density_api
#print axioms effect_structure_api
#print axioms effect_born_api
#print axioms separation_api
#print axioms realMaximallyMixed_not_pure
#print axioms complex_effects_separate
#print axioms real_empty_density_impossible

end QuaternionicComputing.Semantics.DensityAudit
