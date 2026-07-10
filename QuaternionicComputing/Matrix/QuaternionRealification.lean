module

public import QuaternionicComputing.Matrix.Complexification
public import QuaternionicComputing.Matrix.Realification
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Direct realification of quaternionic matrices

This module realizes a quaternionic matrix directly as a real matrix with four
coordinate sectors.  It formalizes the matrix displayed in Equation 63 of the
paper, while deriving all algebraic laws from the already verified
quaternion-to-complex and complex-to-real embeddings.

For `q = a + b*i + c*j + d*k`, the paper orders the real sectors as
`Re, ImI, ImK, ImJ` and displays

```text
[[ a,  b, -d, -c],
 [-b,  a, -c,  d],
 [ d,  c,  a,  b],
 [ c, -d, -b,  a]].
```

The literal composition `Matrix.realify (complexify A)` uses a different
nested-sum order.  Equation 63 is obtained from that composition by applying
the same pure sector permutation `[3, 1, 0, 2]` to rows and columns.  No sign
change occurs in the basis permutation.

The construction below is rectangular.  Multiplicativity and the identity
specialize only as required by matrix multiplication.  Group-theoretic image
results are kept in `QuaternionRealificationUnitary`; in particular, this
module does not repeat the paper's imprecise suggestion that the embedding is
surjective onto the whole special orthogonal group.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Quaternion

/-- The four-sector real index used by direct quaternionic realification. -/
abbrev DirectRealIndex (n : Type*) := (n ⊕ n) ⊕ (n ⊕ n)

/-- Direct realification has four real coordinate sectors per source index. -/
@[simp]
theorem card_directRealIndex (n : Type*) [Fintype n] :
    Fintype.card (DirectRealIndex n) = 4 * Fintype.card n := by
  simp [DirectRealIndex]
  omega

/-- The real-coordinate sector in the Equation 63 order. -/
def directRealRe {n : Type*} (i : n) : DirectRealIndex n :=
  Sum.inl (Sum.inl i)

/-- The `i`-coordinate sector in the Equation 63 order. -/
def directRealImI {n : Type*} (i : n) : DirectRealIndex n :=
  Sum.inl (Sum.inr i)

/-- The `k`-coordinate sector in the Equation 63 order. -/
def directRealImK {n : Type*} (i : n) : DirectRealIndex n :=
  Sum.inr (Sum.inl i)

/-- The `j`-coordinate sector in the Equation 63 order. -/
def directRealImJ {n : Type*} (i : n) : DirectRealIndex n :=
  Sum.inr (Sum.inr i)

/--
Convert an Equation 63 sector index to the nested sector order used by
`Matrix.realify (complexify A)`.

On the four sectors this is the permutation `[3, 1, 0, 2]`.
-/
def eq63PaperToComposed (n : Type*) : DirectRealIndex n ≃ DirectRealIndex n where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inr i)
    | Sum.inl (Sum.inr i) => Sum.inl (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inl i)
  invFun
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inl (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inl i)
  left_inv x := by rcases x with ((i | i) | (i | i)) <;> rfl
  right_inv x := by rcases x with ((i | i) | (i | i)) <;> rfl

@[simp]
theorem eq63PaperToComposed_re {n : Type*} (i : n) :
    eq63PaperToComposed n (directRealRe i) = Sum.inr (Sum.inr i) :=
  rfl

@[simp]
theorem eq63PaperToComposed_imI {n : Type*} (i : n) :
    eq63PaperToComposed n (directRealImI i) = Sum.inl (Sum.inr i) :=
  rfl

@[simp]
theorem eq63PaperToComposed_imK {n : Type*} (i : n) :
    eq63PaperToComposed n (directRealImK i) = Sum.inl (Sum.inl i) :=
  rfl

@[simp]
theorem eq63PaperToComposed_imJ {n : Type*} (i : n) :
    eq63PaperToComposed n (directRealImJ i) = Sum.inr (Sum.inl i) :=
  rfl

/--
Direct realification of a rectangular quaternionic matrix in the sector order
of Equation 63.
-/
def directRealify {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    Matrix (DirectRealIndex m) (DirectRealIndex n) ℝ :=
  Matrix.reindex (eq63PaperToComposed m).symm
    (eq63PaperToComposed n).symm
    (QuaternionicComputing.Matrix.realify (complexify A))

/-- Direct realification is the composed embedding in the Equation 63 basis. -/
theorem directRealify_eq_reindex {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    directRealify A =
      Matrix.reindex (eq63PaperToComposed m).symm
        (eq63PaperToComposed n).symm
        (QuaternionicComputing.Matrix.realify (complexify A)) :=
  rfl

/-! ## Entry formulas -/

@[simp]
theorem directRealify_re_re {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealRe i) (directRealRe j) = (A i j).re :=
  rfl

@[simp]
theorem directRealify_re_imI {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealRe i) (directRealImI j) = (A i j).imI := by
  simp [directRealify, directRealRe, directRealImI, eq63PaperToComposed]

@[simp]
theorem directRealify_re_imK {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealRe i) (directRealImK j) = -(A i j).imK := by
  simp [directRealify, directRealRe, directRealImK, eq63PaperToComposed]

@[simp]
theorem directRealify_re_imJ {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealRe i) (directRealImJ j) = -(A i j).imJ :=
  rfl

@[simp]
theorem directRealify_imI_re {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImI i) (directRealRe j) = -(A i j).imI :=
  rfl

@[simp]
theorem directRealify_imI_imI {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImI i) (directRealImI j) = (A i j).re :=
  rfl

@[simp]
theorem directRealify_imI_imK {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImI i) (directRealImK j) = -(A i j).imJ :=
  rfl

@[simp]
theorem directRealify_imI_imJ {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImI i) (directRealImJ j) = (A i j).imK := by
  simp [directRealify, directRealImI, directRealImJ, eq63PaperToComposed]

@[simp]
theorem directRealify_imK_re {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImK i) (directRealRe j) = (A i j).imK :=
  rfl

@[simp]
theorem directRealify_imK_imI {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImK i) (directRealImI j) = (A i j).imJ :=
  rfl

@[simp]
theorem directRealify_imK_imK {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImK i) (directRealImK j) = (A i j).re :=
  rfl

@[simp]
theorem directRealify_imK_imJ {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImK i) (directRealImJ j) = (A i j).imI :=
  rfl

@[simp]
theorem directRealify_imJ_re {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImJ i) (directRealRe j) = (A i j).imJ :=
  rfl

@[simp]
theorem directRealify_imJ_imI {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImJ i) (directRealImI j) = -(A i j).imK :=
  rfl

@[simp]
theorem directRealify_imJ_imK {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImJ i) (directRealImK j) = -(A i j).imI :=
  rfl

@[simp]
theorem directRealify_imJ_imJ {m n : Type*} (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) :
    directRealify A (directRealImJ i) (directRealImJ j) = (A i j).re :=
  rfl

/-! ## Algebraic laws -/

@[simp]
theorem directRealify_zero {m n : Type*} :
    directRealify (0 : Matrix m n ℍ[ℝ]) = 0 := by
  simp [directRealify]

@[simp]
theorem directRealify_add {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    directRealify (A + B) = directRealify A + directRealify B := by
  unfold directRealify
  rw [complexify_add, QuaternionicComputing.Matrix.realify_add]
  exact (Matrix.reindexAddEquiv ℝ _ _).map_add _ _

@[simp]
theorem directRealify_neg {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    directRealify (-A) = -directRealify A := by
  unfold directRealify
  rw [complexify_neg, QuaternionicComputing.Matrix.realify_neg]
  exact (Matrix.reindexAddEquiv ℝ _ _).map_neg _

@[simp]
theorem directRealify_sub {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    directRealify (A - B) = directRealify A - directRealify B := by
  unfold directRealify
  rw [complexify_sub, QuaternionicComputing.Matrix.realify_sub]
  exact (Matrix.reindexAddEquiv ℝ _ _).map_sub _ _

/-- Direct realification preserves every compatible rectangular product. -/
@[simp]
theorem directRealify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n p ℍ[ℝ]) :
    directRealify (A * B) = directRealify A * directRealify B := by
  unfold directRealify
  rw [complexify_mul, QuaternionicComputing.Matrix.realify_mul]
  exact (Matrix.reindexLinearEquiv_mul
    (R := ℝ) (A := ℝ)
    (eq63PaperToComposed m).symm
    (eq63PaperToComposed n).symm
    (eq63PaperToComposed p).symm _ _).symm

/-- Direct realification sends the quaternionic identity to the real identity. -/
@[simp]
theorem directRealify_one {n : Type*} [DecidableEq n] :
    directRealify (1 : Matrix n n ℍ[ℝ]) = 1 := by
  unfold directRealify
  rw [complexify_one, QuaternionicComputing.Matrix.realify_one]
  simpa only [Matrix.coe_reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv_one (R := ℝ) (A := ℝ)
      (eq63PaperToComposed n).symm)

/-- Quaternionic adjoint becomes real transpose under direct realification. -/
@[simp]
theorem directRealify_conjTranspose {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    directRealify Aᴴ = (directRealify A)ᵀ := by
  unfold directRealify
  rw [complexify_conjTranspose,
    QuaternionicComputing.Matrix.realify_conjTranspose,
    Matrix.transpose_reindex]

/-- Direct realification loses no quaternionic matrix entries. -/
theorem directRealify_injective {m n : Type*} :
    Function.Injective (@directRealify m n) := by
  intro A B h
  apply complexify_injective
  apply QuaternionicComputing.Matrix.realify_injective
  exact (Matrix.reindex _ _).injective h

@[simp]
theorem directRealify_eq_iff {m n : Type*} {A B : Matrix m n ℍ[ℝ]} :
    directRealify A = directRealify B ↔ A = B :=
  directRealify_injective.eq_iff

/-- Direct realification as an injective ring homomorphism on square matrices. -/
def directRealifyRingHom (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℍ[ℝ] →+* Matrix (DirectRealIndex n) (DirectRealIndex n) ℝ where
  toFun := directRealify
  map_one' := directRealify_one
  map_mul' := directRealify_mul
  map_zero' := directRealify_zero
  map_add' := directRealify_add

@[simp]
theorem directRealifyRingHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : Matrix n n ℍ[ℝ]) :
    directRealifyRingHom n A = directRealify A :=
  rfl

/-- The bundled square-matrix direct realification is injective. -/
theorem directRealifyRingHom_injective
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (directRealifyRingHom n) :=
  directRealify_injective

end QuaternionicComputing.Quaternion
