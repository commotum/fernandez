module

public import QuaternionicComputing.Matrix.Realification
public import QuaternionicComputing.Matrix.Complexification
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Unitary images of realification and complexification

This module packages the algebraic matrix embeddings as star-monoid
homomorphisms.  Mathlib's generic `Unitary.map` construction then gives
injective group homomorphisms on unitary matrices without any determinant
assumption.

For realification, a unitary complex matrix becomes an orthogonal real matrix.
For complexification, a unitary quaternionic matrix becomes both a unitary
complex matrix and a member of the complex symplectic group.  Determinant-one
refinements are deliberately kept in the separate determinant leaf.
-/

@[expose] public noncomputable section

open scoped Quaternion Matrix

namespace QuaternionicComputing.Matrix

/-- Realification as a star-preserving monoid homomorphism on square matrices. -/
def realifyStarMonoidHom (n : Type*) [Fintype n] [DecidableEq n] :
    _root_.Matrix n n ℂ →⋆* _root_.Matrix (n ⊕ n) (n ⊕ n) ℝ where
  toFun := realify
  map_one' := realify_one
  map_mul' := realify_mul
  map_star' A := by
    simpa only [_root_.Matrix.star_eq_conjTranspose,
      _root_.Matrix.conjTranspose_eq_transpose_of_trivial] using realify_conjTranspose A

@[simp]
theorem realifyStarMonoidHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℂ) :
    realifyStarMonoidHom n A = realify A :=
  rfl

/-- The bundled star-monoid realification is injective. -/
theorem realifyStarMonoidHom_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (realifyStarMonoidHom n) :=
  realify_injective

/-- The injective group homomorphism induced by realification on unitary matrices. -/
def realifyUnitary (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (_root_.Matrix n n ℂ) →⋆*
      unitary (_root_.Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  Unitary.map (realifyStarMonoidHom n)

@[simp]
theorem realifyUnitary_apply (n : Type*) [Fintype n] [DecidableEq n]
    (U : unitary (_root_.Matrix n n ℂ)) :
    (realifyUnitary n U : _root_.Matrix (n ⊕ n) (n ⊕ n) ℝ) = realify U :=
  rfl

/-- Realification remains injective after restricting to unitary matrices. -/
theorem realifyUnitary_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (realifyUnitary n) :=
  Unitary.map_injective (realifyStarMonoidHom_injective n)

/-- The realification of a complex unitary matrix is orthogonal. -/
theorem realify_mem_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℂ} (hU : U ∈ unitary (_root_.Matrix n n ℂ)) :
    realify U ∈ _root_.Matrix.orthogonalGroup (n ⊕ n) ℝ :=
  Unitary.map_mem (realifyStarMonoidHom n) hU

/-- The subgroup of real orthogonal matrices obtained by realifying complex unitaries. -/
def realifyUnitaryImage (n : Type*) [Fintype n] [DecidableEq n] :
    Subgroup (unitary (_root_.Matrix (n ⊕ n) (n ⊕ n) ℝ)) :=
  (realifyUnitary n).toMonoidHom.range

/-- Complex unitaries are `MulEquiv`-isomorphic to their realification range. -/
noncomputable def realifyUnitaryEquivImage (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (_root_.Matrix n n ℂ) ≃* realifyUnitaryImage n :=
  MonoidHom.ofInjective (realifyUnitary_injective n)

end QuaternionicComputing.Matrix

namespace QuaternionicComputing.Quaternion

/-- Complexification as a star-preserving monoid homomorphism on square matrices. -/
def complexifyStarMonoidHom (n : Type*) [Fintype n] [DecidableEq n] :
    _root_.Matrix n n ℍ[ℝ] →⋆* _root_.Matrix (n ⊕ n) (n ⊕ n) ℂ where
  toFun := complexify
  map_one' := complexify_one
  map_mul' := complexify_mul
  map_star' A := by
    simpa only [_root_.Matrix.star_eq_conjTranspose] using complexify_conjTranspose A

@[simp]
theorem complexifyStarMonoidHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℍ[ℝ]) :
    complexifyStarMonoidHom n A = complexify A :=
  rfl

/-- The bundled star-monoid complexification is injective. -/
theorem complexifyStarMonoidHom_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (complexifyStarMonoidHom n) :=
  complexify_injective

/-- The injective group homomorphism induced by complexification on quaternionic unitaries. -/
def complexifyUnitary (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (_root_.Matrix n n ℍ[ℝ]) →⋆*
      unitary (_root_.Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  Unitary.map (complexifyStarMonoidHom n)

@[simp]
theorem complexifyUnitary_apply (n : Type*) [Fintype n] [DecidableEq n]
    (U : unitary (_root_.Matrix n n ℍ[ℝ])) :
    (complexifyUnitary n U : _root_.Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      complexify U.1 :=
  rfl

/-- Complexification remains injective after restricting to unitary matrices. -/
theorem complexifyUnitary_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (complexifyUnitary n) :=
  Unitary.map_injective (complexifyStarMonoidHom_injective n)

/-- The complexification of a quaternionic unitary matrix is complex unitary. -/
theorem complexify_mem_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (_root_.Matrix n n ℍ[ℝ])) :
    complexify U ∈ _root_.Matrix.unitaryGroup (n ⊕ n) ℂ :=
  Unitary.map_mem (complexifyStarMonoidHom n) hU

/--
The conjugate of a complexified quaternionic unitary is a left inverse of its
transpose.  This is the unitary identity in the form used by the symplectic
calculation.
-/
theorem complexify_map_star_mul_transpose_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (_root_.Matrix n n ℍ[ℝ])) :
    (complexify U).map star * (complexify U)ᵀ = 1 := by
  have h := (complexify_mem_unitary hU).2
  ext i j
  have hij := congrFun (congrFun h j) i
  simpa [_root_.Matrix.mul_apply, _root_.Matrix.one_apply, mul_comm, eq_comm] using hij

/-- A quaternionic unitary complexifies to a complex symplectic matrix. -/
theorem complexify_mem_symplectic {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (_root_.Matrix n n ℍ[ℝ])) :
    complexify U ∈ _root_.Matrix.symplecticGroup n ℂ := by
  rw [SymplecticGroup.mem_iff]
  change complexify U * complexificationJ n * (complexify U)ᵀ = complexificationJ n
  rw [complexify_mul_complexificationJ, _root_.Matrix.mul_assoc,
    complexify_map_star_mul_transpose_eq_one hU, _root_.Matrix.mul_one]

/-- The subgroup of complex unitaries obtained by complexifying quaternionic unitaries. -/
def complexifyUnitaryImage (n : Type*) [Fintype n] [DecidableEq n] :
    Subgroup (unitary (_root_.Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
  (complexifyUnitary n).toMonoidHom.range

/-- Quaternionic unitaries are `MulEquiv`-isomorphic to their complexification range. -/
noncomputable def complexifyUnitaryEquivImage (n : Type*) [Fintype n] [DecidableEq n] :
    unitary (_root_.Matrix n n ℍ[ℝ]) ≃* complexifyUnitaryImage n :=
  MonoidHom.ofInjective (complexifyUnitary_injective n)

end QuaternionicComputing.Quaternion
