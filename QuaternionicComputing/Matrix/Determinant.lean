module

public import QuaternionicComputing.Matrix.Unitary
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Determinants of the matrix embeddings

This proof leaf isolates the commutative determinant arguments from the basic
realification and complexification APIs.

For realification, the determinant is the complex field norm:

`det (realify A) = Complex.normSq (det A)`.

Consequently every complex unitary realifies to a special orthogonal matrix,
including in dimension zero.

For quaternionic complexification, the block symmetry forces the complex
determinant to be real.  Combined with unitarity this proves that the
determinant is `1` or `-1`.  Excluding the negative branch requires a genuine
determinant-one theorem for complex symplectic matrices (or equivalent
Pfaffian, connectedness, or Study-determinant infrastructure), none of which
is currently supplied by mathlib.  We therefore do not claim special-unitary
membership here.  The unitary simulation results do not depend on this missing
sign refinement.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Matrix

private def realificationSignUnit (i : Fin 2) : ℝˣ :=
  if i = 0 then 1 else -1

/-- The scalar basis `1, -I` whose coordinates realize the paper's block signs. -/
private noncomputable def basisOneNegI : Module.Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.unitsSMul realificationSignUnit

private theorem leftMulMatrix_basisOneNegI (z : ℂ) :
    Algebra.leftMulMatrix basisOneNegI z =
      !![z.re, z.im; -z.im, z.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases i <;> fin_cases j <;>
    simp [basisOneNegI, realificationSignUnit,
      Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply]

/-- Reorder the scalar coordinate inside each entry into the two block sectors. -/
private def prodFinTwoEquivSum (n : Type*) : n × Fin 2 ≃ n ⊕ n where
  toFun
    | (i, 0) => Sum.inl i
    | (i, 1) => Sum.inr i
  invFun
    | Sum.inl i => (i, 0)
    | Sum.inr i => (i, 1)
  left_inv x := by
    obtain ⟨i, k⟩ := x
    fin_cases k <;> rfl
  right_inv x := by cases x <;> rfl

/--
In the basis `1, -I`, restricting the complex matrix endomorphism to real
scalars produces exactly `realify`, up to the block-sector reindexing.
-/
private theorem restrictScalars_toMatrix_reindex_eq_realify
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℂ) :
    _root_.Matrix.reindex (prodFinTwoEquivSum n) (prodFinTwoEquivSum n)
      (((_root_.Matrix.toLin' A).restrictScalars ℝ).toMatrix
        (basisOneNegI.smulTower' (Pi.basisFun ℂ n))
        (basisOneNegI.smulTower' (Pi.basisFun ℂ n))) = realify A := by
  rw [LinearMap.restrictScalars_toMatrix]
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [prodFinTwoEquivSum, leftMulMatrix_basisOneNegI]
      | inr j => simp [prodFinTwoEquivSum, leftMulMatrix_basisOneNegI]
  | inr i =>
      cases j with
      | inl j => simp [prodFinTwoEquivSum, leftMulMatrix_basisOneNegI]
      | inr j => simp [prodFinTwoEquivSum, leftMulMatrix_basisOneNegI]

/--
The real determinant of a complex matrix's realification is the squared
complex norm of the original determinant.

This statement also covers the empty index type: both sides are then `1`.
-/
theorem realify_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℂ) :
    (realify A).det = Complex.normSq A.det := by
  let b := basisOneNegI.smulTower' (Pi.basisFun ℂ n)
  have hmatrix :
      _root_.Matrix.reindex (prodFinTwoEquivSum n) (prodFinTwoEquivSum n)
        (((_root_.Matrix.toLin' A).restrictScalars ℝ).toMatrix b b) =
          realify A := by
    simpa [b] using restrictScalars_toMatrix_reindex_eq_realify A
  rw [← hmatrix, _root_.Matrix.det_reindex_self, LinearMap.det_toMatrix b]
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Algebra.norm_complex_apply]

/-- A complex unitary has determinant norm square one after realification. -/
theorem realify_det_eq_one_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℂ}
    (hU : U ∈ unitary (_root_.Matrix n n ℂ)) :
    (realify U).det = 1 := by
  rw [realify_det]
  have hdet := _root_.Matrix.det_of_mem_unitary hU
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  exact hdet.1

/--
The corrected determinant refinement of the paper's realification theorem:
the full complex unitary group embeds into the special orthogonal group in
twice the dimension.
-/
theorem realify_mem_specialOrthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℂ}
    (hU : U ∈ unitary (_root_.Matrix n n ℂ)) :
    realify U ∈ _root_.Matrix.specialOrthogonalGroup (n ⊕ n) ℝ := by
  rw [_root_.Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨realify_mem_orthogonal hU, realify_det_eq_one_of_mem_unitary hU⟩

end QuaternionicComputing.Matrix

namespace QuaternionicComputing.Quaternion

/--
The determinant of a quaternionic complexification equals the determinant of
its entrywise complex conjugate.
-/
theorem complexify_det_eq_map_star_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℍ[ℝ]) :
    (complexify A).det = ((complexify A).map star).det := by
  have hdet := congrArg _root_.Matrix.det (complexify_mul_complexificationJ A)
  simp only [_root_.Matrix.det_mul] at hdet
  have hJ : IsUnit (complexificationJ n).det := by
    change IsUnit (_root_.Matrix.J n ℂ).det
    exact _root_.Matrix.isUnit_det_J n ℂ
  apply mul_right_cancel₀ hJ.ne_zero
  calc
    (complexify A).det * (complexificationJ n).det =
        (complexificationJ n).det * ((complexify A).map star).det := hdet
    _ = ((complexify A).map star).det * (complexificationJ n).det := by
      rw [mul_comm]

/-- The complex determinant of every quaternionic complexification is fixed by conjugation. -/
theorem complexify_det_star_fixed
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℍ[ℝ]) :
    star (complexify A).det = (complexify A).det := by
  calc
    star (complexify A).det = ((complexify A).map star).det := by
      simpa using RingHom.map_det (starRingEnd ℂ) (complexify A)
    _ = (complexify A).det := (complexify_det_eq_map_star_det A).symm

/-- The complex determinant of a quaternionic complexification has zero imaginary part. -/
theorem complexify_det_im_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℍ[ℝ]) :
    (complexify A).det.im = 0 := by
  have h := congrArg Complex.im (complexify_det_star_fixed A)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- The determinant is the complex coercion of its real part. -/
theorem complexify_det_eq_ofReal_re
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : _root_.Matrix n n ℍ[ℝ]) :
    (complexify A).det = ((complexify A).det.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [complexify_det_im_eq_zero]

/--
A quaternionic unitary's complexified determinant squares to one.

This is strictly weaker than determinant one: the symplectic and unitary laws
alone leave a sign that must be resolved by additional mathematics.
-/
theorem complexify_det_sq_eq_one_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (_root_.Matrix n n ℍ[ℝ])) :
    (complexify U).det ^ 2 = 1 := by
  have hdet := _root_.Matrix.det_of_mem_unitary (complexify_mem_unitary hU)
  simpa [pow_two, complexify_det_star_fixed] using hdet.1

/--
The strongest determinant conclusion obtained here for quaternionic
unitaries: the complexified determinant is `1` or `-1`.

The second disjunct records an unresolved proof branch; this theorem does not
assert that a negative-determinant image actually exists.
-/
theorem complexify_det_eq_one_or_neg_one_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : _root_.Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (_root_.Matrix n n ℍ[ℝ])) :
    (complexify U).det = 1 ∨ (complexify U).det = -1 :=
  sq_eq_one_iff.mp (complexify_det_sq_eq_one_of_mem_unitary hU)

end QuaternionicComputing.Quaternion
