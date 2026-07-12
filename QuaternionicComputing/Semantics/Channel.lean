module

public import QuaternionicComputing.Semantics.EffectSeparation

/-!
# Finite real and complex unitary channels

This leaf bundles a square `RCLike` matrix with its unitary certificate and
defines its action on finite density matrices.  Composition is exposed in
chronological order: `U.followedBy V` means first apply `U`, then apply `V`, so its
underlying matrix is `V * U`.

`ChannelEq U V` requires equality of the complete evolved density matrix for
every density input.  `AllMeasurementEq U V` requires equality of the Born
value for every density input and every genuine physical `Effect`.  The two
relations are proved equivalent using physical-effect separation from
`Semantics.EffectSeparation`.

The implementation is uniform over `RCLike`, hence covers the intended real
and complex models.  It introduces no quaternionic density semantics,
arbitrary trace tests, phase relation, circuit wrapper, or empty-dimensional
phase characterization.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Bundled unitary operators -/

/-- A finite square matrix bundled with a proof that it is unitary. -/
structure UnitaryOperator (𝕜 : Type u) (I : Type v) [RCLike 𝕜]
    [Fintype I] [DecidableEq I] where
  /-- The underlying square matrix. -/
  matrix : Matrix I I 𝕜
  /-- The underlying matrix is unitary. -/
  mem_unitary : matrix ∈ unitary (Matrix I I 𝕜)

/-- A finite real unitary operator. -/
abbrev RealUnitaryOperator (I : Type v) [Fintype I] [DecidableEq I] :=
  UnitaryOperator ℝ I

/-- A finite complex unitary operator. -/
abbrev ComplexUnitaryOperator (I : Type v) [Fintype I] [DecidableEq I] :=
  UnitaryOperator ℂ I

namespace UnitaryOperator

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]

/-- Use a bundled unitary operator as its underlying matrix. -/
instance : Coe (UnitaryOperator 𝕜 I) (Matrix I I 𝕜) where
  coe U := U.matrix

/-- Coercion exposes the stored unitary matrix definitionally. -/
@[simp]
theorem coe_matrix (U : UnitaryOperator 𝕜 I) :
    ((U : Matrix I I 𝕜)) = U.matrix :=
  rfl

/-- Two bundled unitary operators are equal when their matrices are equal. -/
theorem ext_matrix {U V : UnitaryOperator 𝕜 I}
    (h : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜)) : U = V := by
  cases U
  cases V
  simpa using h

/-- Bundled unitary operators are extensional in their matrix entries. -/
@[ext]
theorem ext {U V : UnitaryOperator 𝕜 I}
    (h : ∀ i j, (U : Matrix I I 𝕜) i j = (V : Matrix I I 𝕜) i j) :
    U = V :=
  ext_matrix (Matrix.ext fun i j ↦ h i j)

/-- Bundled operator equality is exactly equality of the underlying matrices. -/
theorem eq_iff_matrix_eq {U V : UnitaryOperator 𝕜 I} :
    U = V ↔ (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜) := by
  constructor
  · rintro rfl
    rfl
  · exact ext_matrix

/-- Bundle a matrix together with a supplied unitary certificate. -/
def ofMatrix (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) : UnitaryOperator 𝕜 I where
  matrix := U
  mem_unitary := hU

/-- The matrix of `ofMatrix` is the supplied matrix. -/
@[simp]
theorem ofMatrix_coe (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) :
    ((ofMatrix U hU : UnitaryOperator 𝕜 I) : Matrix I I 𝕜) = U :=
  rfl

/-- The identity unitary operator. -/
def identity : UnitaryOperator 𝕜 I :=
  ofMatrix 1 (unitary (Matrix I I 𝕜)).one_mem

/-- The matrix of the identity bundled operator is the identity matrix. -/
@[simp]
theorem identity_coe :
    ((identity : UnitaryOperator 𝕜 I) : Matrix I I 𝕜) = 1 :=
  rfl

/--
Chronological composition of unitary operators.

`U.followedBy V` applies `U` first and `V` second, and therefore stores `V * U`.
-/
def followedBy (U V : UnitaryOperator 𝕜 I) : UnitaryOperator 𝕜 I :=
  ofMatrix (V.matrix * U.matrix)
    ((unitary (Matrix I I 𝕜)).mul_mem V.mem_unitary U.mem_unitary)

/-- Chronological composition stores the later matrix on the left. -/
@[simp]
theorem followedBy_coe (U V : UnitaryOperator 𝕜 I) :
    ((U.followedBy V : UnitaryOperator 𝕜 I) : Matrix I I 𝕜) =
      (V : Matrix I I 𝕜) * (U : Matrix I I 𝕜) :=
  rfl

/-- Chronological composition is associative. -/
@[simp]
theorem followedBy_assoc (U V W : UnitaryOperator 𝕜 I) :
    (U.followedBy V).followedBy W = U.followedBy (V.followedBy W) := by
  apply ext_matrix
  simp only [followedBy_coe, Matrix.mul_assoc]

/-- Applying the identity first does not change a unitary operator. -/
@[simp]
theorem identity_followedBy (U : UnitaryOperator 𝕜 I) :
    identity.followedBy U = U := by
  apply ext_matrix
  simp

/-- Applying the identity last does not change a unitary operator. -/
@[simp]
theorem followedBy_identity (U : UnitaryOperator 𝕜 I) :
    U.followedBy identity = U := by
  apply ext_matrix
  simp

/-! ## Density evolution -/

/-- Evolve a density matrix by the bundled operator's unitary conjugation. -/
def evolve (U : UnitaryOperator 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    DensityMatrix 𝕜 I :=
  DensityMatrix.unitaryConjugate U.matrix U.mem_unitary rho

/-- Bundled unitary evolution computes as `U * rho * Uᴴ`. -/
@[simp]
theorem evolve_coe (U : UnitaryOperator 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    ((U.evolve rho : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
      (U : Matrix I I 𝕜) * (rho : Matrix I I 𝕜) *
        (U : Matrix I I 𝕜)ᴴ :=
  rfl

/-- The identity bundled operator fixes every density matrix. -/
@[simp]
theorem identity_evolve (rho : DensityMatrix 𝕜 I) :
    (identity : UnitaryOperator 𝕜 I).evolve rho = rho := by
  apply DensityMatrix.ext_matrix
  simp [evolve]

/-- Chronological composition evolves first by `U` and then by `V`. -/
theorem followedBy_evolve (U V : UnitaryOperator 𝕜 I)
    (rho : DensityMatrix 𝕜 I) :
    (U.followedBy V).evolve rho = V.evolve (U.evolve rho) := by
  apply DensityMatrix.ext_matrix
  simp only [evolve_coe, followedBy_coe, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

end UnitaryOperator

/-! ## Channel and all-physical-measurement equality -/

/--
Two unitary operators induce the same channel when they produce the same
complete density matrix on every density input.
-/
def ChannelEq {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (U V : UnitaryOperator 𝕜 I) : Prop :=
  ∀ rho : DensityMatrix 𝕜 I, U.evolve rho = V.evolve rho

/--
Two unitary operators agree on all physical measurements when every genuine
effect has the same Born value after either operator acts on every density
input.
-/
def AllMeasurementEq {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (U V : UnitaryOperator 𝕜 I) : Prop :=
  ∀ (rho : DensityMatrix 𝕜 I) (E : Effect 𝕜 I),
    Effect.bornValue E (U.evolve rho) =
      Effect.bornValue E (V.evolve rho)

namespace ChannelEq

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]
variable {U V W : UnitaryOperator 𝕜 I}

@[refl]
theorem refl (U : UnitaryOperator 𝕜 I) : ChannelEq U U :=
  fun _ ↦ rfl

@[symm]
theorem symm (h : ChannelEq U V) : ChannelEq V U :=
  fun rho ↦ (h rho).symm

@[trans]
theorem trans (hUV : ChannelEq U V) (hVW : ChannelEq V W) :
    ChannelEq U W :=
  fun rho ↦ (hUV rho).trans (hVW rho)

/-- Unitary-channel equality is an equivalence relation. -/
theorem equivalence :
    Equivalence (@ChannelEq 𝕜 I _ _ _) :=
  ⟨refl, symm, trans⟩

/-- Channel equality exposes equality on each supplied density input. -/
theorem evolve_eq (h : ChannelEq U V) (rho : DensityMatrix 𝕜 I) :
    U.evolve rho = V.evolve rho :=
  h rho

/-- Equality of bundled unitary operators implies channel equality. -/
theorem of_eq (h : U = V) : ChannelEq U V := by
  subst V
  exact refl U

/-- Equality of underlying matrices implies channel equality. -/
theorem of_matrix_eq
    (h : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜)) : ChannelEq U V :=
  of_eq (UnitaryOperator.ext_matrix h)

/-- Channel equality implies agreement for every genuine physical effect. -/
theorem allMeasurementEq (h : ChannelEq U V) : AllMeasurementEq U V := by
  intro rho E
  rw [h rho]

/--
Chronological composition is congruent for channel equality: related early
and later operators compose to related complete channels.
-/
theorem followedBy {A B : UnitaryOperator 𝕜 I}
    (hUV : ChannelEq U V) (hAB : ChannelEq A B) :
    ChannelEq (U.followedBy A) (V.followedBy B) := by
  intro rho
  rw [UnitaryOperator.followedBy_evolve, UnitaryOperator.followedBy_evolve]
  calc
    A.evolve (U.evolve rho) = A.evolve (V.evolve rho) :=
      congrArg A.evolve (hUV rho)
    _ = B.evolve (V.evolve rho) := hAB (V.evolve rho)

end ChannelEq

namespace AllMeasurementEq

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]
variable {U V W : UnitaryOperator 𝕜 I}

@[refl]
theorem refl (U : UnitaryOperator 𝕜 I) : AllMeasurementEq U U :=
  fun _ _ ↦ rfl

@[symm]
theorem symm (h : AllMeasurementEq U V) : AllMeasurementEq V U :=
  fun rho E ↦ (h rho E).symm

@[trans]
theorem trans (hUV : AllMeasurementEq U V)
    (hVW : AllMeasurementEq V W) : AllMeasurementEq U W :=
  fun rho E ↦ (hUV rho E).trans (hVW rho E)

/-- All-physical-measurement equality is an equivalence relation. -/
theorem equivalence :
    Equivalence (@AllMeasurementEq 𝕜 I _ _ _) :=
  ⟨refl, symm, trans⟩

/-- All-measurement equality exposes the equality for one input and effect. -/
theorem bornValue_eq (h : AllMeasurementEq U V)
    (rho : DensityMatrix 𝕜 I) (E : Effect 𝕜 I) :
    Effect.bornValue E (U.evolve rho) =
      Effect.bornValue E (V.evolve rho) :=
  h rho E

/-- Equality of bundled unitary operators implies all-measurement equality. -/
theorem of_eq (h : U = V) : AllMeasurementEq U V := by
  subst V
  exact refl U

/-- Equality of underlying matrices implies all-measurement equality. -/
theorem of_matrix_eq
    (h : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜)) :
    AllMeasurementEq U V :=
  of_eq (UnitaryOperator.ext_matrix h)

/--
Agreement for every genuine physical effect recovers equality of the complete
evolved density matrices.
-/
theorem channelEq (h : AllMeasurementEq U V) : ChannelEq U V := by
  intro rho
  apply DensityMatrix.eq_of_forall_effect_bornValue_eq
  intro E
  exact h rho E

/-- Chronological composition is congruent for all-measurement equality. -/
theorem followedBy {A B : UnitaryOperator 𝕜 I}
    (hUV : AllMeasurementEq U V) (hAB : AllMeasurementEq A B) :
    AllMeasurementEq (U.followedBy A) (V.followedBy B) :=
  (hUV.channelEq.followedBy hAB.channelEq).allMeasurementEq

end AllMeasurementEq

/--
Equality of unitary channels is equivalent to agreement of all genuine
physical-effect Born values on every density input.
-/
theorem channelEq_iff_allMeasurementEq
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (U V : UnitaryOperator 𝕜 I) :
    ChannelEq U V ↔ AllMeasurementEq U V :=
  ⟨ChannelEq.allMeasurementEq, AllMeasurementEq.channelEq⟩

end QuaternionicComputing.Semantics
