module

public import QuaternionicComputing.Semantics.Effect

/-!
# Separation by genuine physical effects

This leaf proves that finite real or complex density matrices are separated by
their Born values against all genuine physical effects.  The proof uses the
normalized rank-one projector effects constructed in `Semantics.Effect`, not
arbitrary trace-test matrices.

The rank-one trace pairing is first identified with the corresponding
quadratic form.  Equality on normalized vectors is extended to every vector
by an explicit zero/nonzero split, after which symmetric/Hermitian
polarization separates the underlying matrices.  No nonempty index hypothesis
is required: the vector argument handles the zero-dimensional space directly,
while `DensityMatrix.isEmpty_of_index_isEmpty` already proves that a trace-one
density cannot exist there.
-/

@[expose] public noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix

namespace QuaternionicComputing.Semantics

universe u v w

namespace Effect

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]

/--
The trace pairing with the rank-one projector onto `x` is the quadratic form
of the tested matrix at `x`.
-/
theorem trace_rankOneProjector_mul_eq_inner
    (x : EuclideanSpace 𝕜 I) (A : Matrix I I 𝕜) :
    Matrix.trace (rankOneProjector x * A) =
      inner 𝕜 x (Matrix.toEuclideanLin A x) := by
  change Matrix.trace (rankOneProjector x * A) =
    dotProduct (Matrix.mulVec A x.ofLp) (star x.ofLp)
  rw [dotProduct_comm, rankOneProjector_eq_vecMulVec]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.mul_sum, dotProduct,
    Matrix.mulVec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Effect

/-!
## From normalized quadratic forms to matrix equality
-/

/--
Equality of two quadratic forms on the unit sphere implies equality on every
vector.  The zero vector is handled separately; a nonzero vector is scaled by
the inverse of its norm.  Thus the theorem is valid even for a zero-dimensional
space and does not assume an inhabitant or normalized vector exists.
-/
theorem quadratic_eq_of_unit_sphere
    {𝕜 : Type u} {E : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (S T : E →ₗ[𝕜] E)
    (hunit : ∀ y : E, ‖y‖ = 1 →
      inner 𝕜 (S y) y = inner 𝕜 (T y) y) :
    ∀ x : E, inner 𝕜 (S x) x = inner 𝕜 (T x) x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · let y : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
    have hy : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul]
      simp [norm_ne_zero_iff.mpr hx]
    have h := hunit y hy
    dsimp only [y] at h
    simp only [map_smul, inner_smul_left, inner_smul_right,
      map_inv₀, RCLike.conj_ofReal] at h
    have ha : ((algebraMap ℝ 𝕜) ‖x‖)⁻¹ ≠ 0 := by
      simp [norm_ne_zero_iff.mpr hx]
    have hb : ((‖x‖ : 𝕜))⁻¹ ≠ 0 := by
      simp [norm_ne_zero_iff.mpr hx]
    exact mul_left_cancel₀ hb (mul_left_cancel₀ ha h)

/--
Positive-semidefinite matrices are separated by the real parts of their trace
pairings with all genuine physical effects.

Only normalized rank-one projector effects are used in the proof.  In
particular, this theorem does not reinterpret arbitrary matrices from an
algebraic trace-extensionality lemma as physical effects.
-/
theorem posSemidef_eq_of_forall_effect_trace_re_eq
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    {A B : Matrix I I 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : ∀ E : Effect 𝕜 I,
      RCLike.re (Matrix.trace ((E : Matrix I I 𝕜) * A)) =
        RCLike.re (Matrix.trace ((E : Matrix I I 𝕜) * B))) :
    A = B := by
  let S := Matrix.toEuclideanLin A
  let T := Matrix.toEuclideanLin B
  have hS : S.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB.isHermitian
  have hunit : ∀ x : EuclideanSpace 𝕜 I, ‖x‖ = 1 →
      inner 𝕜 (S x) x = inner 𝕜 (T x) x := by
    intro x hx
    have hre := htrace (Effect.projector x hx)
    rw [Effect.projector_coe, Effect.trace_rankOneProjector_mul_eq_inner,
      Effect.trace_rankOneProjector_mul_eq_inner] at hre
    calc
      inner 𝕜 (S x) x = inner 𝕜 x (S x) := hS x x
      _ = (RCLike.re (inner 𝕜 x (S x)) : 𝕜) :=
        (hS.coe_re_inner_self_apply x).symm
      _ = (RCLike.re (inner 𝕜 x (T x)) : 𝕜) := by rw [hre]
      _ = inner 𝕜 x (T x) := hT.coe_re_inner_self_apply x
      _ = inner 𝕜 (T x) x := (hT x x).symm
  have hall : ∀ x : EuclideanSpace 𝕜 I,
      inner 𝕜 (S x) x = inner 𝕜 (T x) x :=
    quadratic_eq_of_unit_sphere S T hunit
  have hsub : S - T = 0 := (hS.sub hT).inner_map_self_eq_zero.mp (by
    intro x
    rw [LinearMap.sub_apply, inner_sub_left, hall x, sub_self])
  exact Matrix.toEuclideanLin.injective (sub_eq_zero.mp hsub)

namespace DensityMatrix

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]

/--
Two density matrices are equal exactly when every genuine physical effect has
the same Born value on them.

The reverse implication is the physical-effect separation theorem.  It is
uniform in the index type; when the index is empty, the imported
`DensityMatrix.isEmpty_of_index_isEmpty` theorem records that neither density
argument can exist.
-/
theorem eq_iff_forall_effect_bornValue_eq (rho sigma : DensityMatrix 𝕜 I) :
    rho = sigma ↔
      ∀ E : Effect 𝕜 I, Effect.bornValue E rho = Effect.bornValue E sigma := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro hborn
    apply ext_matrix
    apply posSemidef_eq_of_forall_effect_trace_re_eq
      rho.posSemidef sigma.posSemidef
    intro E
    simpa only [Effect.bornValue, Effect.bornScalar] using hborn E

end DensityMatrix

end QuaternionicComputing.Semantics
