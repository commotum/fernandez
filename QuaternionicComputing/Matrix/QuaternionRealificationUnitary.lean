module

public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.Matrix.QuaternionRealification

/-!
# Unitary image of direct quaternionic realification

This leaf packages direct quaternionic realification as a star-monoid
homomorphism and proves that quaternionic unitary matrices map into the
special orthogonal group in four times the real dimension.

The paper describes Equation 63 as inducing an isomorphism from the
quaternionic unitary group to `SO(4N)`.  The correct statement is an injective
homomorphism into `SO(4N)`, and hence an isomorphism only onto its image.  The
definitions below expose both the embedding and its image without asserting
surjectivity onto the full special orthogonal group.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Quaternion

/--
Direct realification as a star-preserving monoid homomorphism on square
matrices.
-/
def directRealifyStarMonoidHom (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℍ[ℝ] →⋆* Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ where
  toFun := directRealify
  map_one' := directRealify_one
  map_mul' := directRealify_mul
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      directRealify_conjTranspose A

@[simp]
theorem directRealifyStarMonoidHom_apply
    (n : Type*) [Fintype n] [DecidableEq n]
    (A : Matrix n n ℍ[ℝ]) :
    directRealifyStarMonoidHom n A = directRealify A :=
  rfl

/-- The bundled star-monoid direct realification is injective. -/
theorem directRealifyStarMonoidHom_injective
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (directRealifyStarMonoidHom n) :=
  directRealify_injective

/-- The induced injective homomorphism on unitary matrices. -/
def directRealifyUnitary (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (Matrix n n ℍ[ℝ]) →⋆*
      unitary (Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ) :=
  Unitary.map (directRealifyStarMonoidHom n)

@[simp]
theorem directRealifyUnitary_apply
    (n : Type*) [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℍ[ℝ])) :
    (directRealifyUnitary n U :
      Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ) =
        directRealify U.1 :=
  rfl

/-- Direct realification remains injective on quaternionic unitaries. -/
theorem directRealifyUnitary_injective
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (directRealifyUnitary n) :=
  Unitary.map_injective (directRealifyStarMonoidHom_injective n)

/-- A quaternionic unitary directly realifies to a real orthogonal matrix. -/
theorem directRealify_mem_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) :
    directRealify U ∈ Matrix.orthogonalGroup (DirectRealIndex n) ℝ :=
  Unitary.map_mem (directRealifyStarMonoidHom n) hU

/-- Simultaneous Equation 63 reindexing does not change the determinant. -/
theorem directRealify_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℍ[ℝ]) :
    (directRealify A).det =
      (QuaternionicComputing.Matrix.realify (complexify A)).det := by
  unfold directRealify
  exact Matrix.det_reindex_self (eq63PaperToComposed n).symm _

/-- A quaternionic unitary has determinant one after direct realification. -/
theorem directRealify_det_eq_one_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) :
    (directRealify U).det = 1 := by
  rw [directRealify_det]
  exact QuaternionicComputing.Matrix.realify_det_eq_one_of_mem_unitary
    (complexify_mem_unitary hU)

/--
The corrected Equation 63 group statement: quaternionic unitaries embed into
the special orthogonal group in four times the real dimension.
-/
theorem directRealify_mem_specialOrthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) :
    directRealify U ∈
      Matrix.specialOrthogonalGroup (DirectRealIndex n) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨directRealify_mem_orthogonal hU,
    directRealify_det_eq_one_of_mem_unitary hU⟩

/--
The direct realification homomorphism with its codomain restricted to the
special orthogonal group.
-/
def directRealifySpecialOrthogonal
    (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (Matrix n n ℍ[ℝ]) →*
      Matrix.specialOrthogonalGroup (DirectRealIndex n) ℝ where
  toFun U :=
    ⟨directRealify U.1,
      directRealify_mem_specialOrthogonal U.property⟩
  map_one' := by
    apply Subtype.ext
    exact directRealify_one
  map_mul' U V := by
    apply Subtype.ext
    exact directRealify_mul
      U.1 V.1

@[simp]
theorem directRealifySpecialOrthogonal_apply
    (n : Type*) [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℍ[ℝ])) :
    (directRealifySpecialOrthogonal n U :
      Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ) =
        directRealify U.1 :=
  rfl

/-- The special-orthogonal-valued direct realification is injective. -/
theorem directRealifySpecialOrthogonal_injective
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (directRealifySpecialOrthogonal n) := by
  intro U V h
  apply Subtype.ext
  apply directRealify_injective
  exact congrArg
    (fun X : Matrix.specialOrthogonalGroup (DirectRealIndex n) ℝ ↦
      (X : Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ)) h

/-- The subgroup of `SO(4N)` obtained by direct quaternionic realification. -/
def directRealifySpecialOrthogonalImage
    (n : Type*) [Fintype n] [DecidableEq n] :
    Subgroup (Matrix.specialOrthogonalGroup (DirectRealIndex n) ℝ) :=
  (directRealifySpecialOrthogonal n).range

/--
Quaternionic unitaries are `MulEquiv`-isomorphic to their direct-realification
range, rather than to the whole special orthogonal group.
-/
noncomputable def directRealifyUnitaryEquivImage
    (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (Matrix n n ℍ[ℝ]) ≃*
      directRealifySpecialOrthogonalImage n :=
  MonoidHom.ofInjective (directRealifySpecialOrthogonal_injective n)

end QuaternionicComputing.Quaternion
