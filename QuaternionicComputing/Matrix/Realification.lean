module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Realification of complex matrices

This module implements the paper's sign convention

`z = a + b * I ↦ [[a, b], [-b, a]]`

entrywise on matrices.  An `m × n` complex matrix is sent to a real matrix
whose row and column types are respectively `m ⊕ m` and `n ⊕ n`.
The construction is rectangular when possible; only multiplication and the
identity matrix require the usual finite/square hypotheses.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Matrix

variable {m n p : Type*}

/-- The entrywise real part of a complex matrix. -/
def realPart (A : _root_.Matrix m n ℂ) : _root_.Matrix m n ℝ :=
  A.map Complex.re

/-- The entrywise imaginary part of a complex matrix. -/
def imagPart (A : _root_.Matrix m n ℂ) : _root_.Matrix m n ℝ :=
  A.map Complex.im

@[simp]
theorem realPart_apply (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    realPart A i j = (A i j).re :=
  rfl

@[simp]
theorem imagPart_apply (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    imagPart A i j = (A i j).im :=
  rfl

@[simp]
theorem realPart_zero : realPart (0 : _root_.Matrix m n ℂ) = 0 :=
  rfl

@[simp]
theorem imagPart_zero : imagPart (0 : _root_.Matrix m n ℂ) = 0 :=
  rfl

@[simp]
theorem realPart_add (A B : _root_.Matrix m n ℂ) :
    realPart (A + B) = realPart A + realPart B := by
  ext i j
  simp

@[simp]
theorem imagPart_add (A B : _root_.Matrix m n ℂ) :
    imagPart (A + B) = imagPart A + imagPart B := by
  ext i j
  simp

@[simp]
theorem realPart_neg (A : _root_.Matrix m n ℂ) :
    realPart (-A) = -realPart A := by
  ext i j
  simp

@[simp]
theorem imagPart_neg (A : _root_.Matrix m n ℂ) :
    imagPart (-A) = -imagPart A := by
  ext i j
  simp

@[simp]
theorem realPart_sub (A B : _root_.Matrix m n ℂ) :
    realPart (A - B) = realPart A - realPart B := by
  ext i j
  simp

@[simp]
theorem imagPart_sub (A B : _root_.Matrix m n ℂ) :
    imagPart (A - B) = imagPart A - imagPart B := by
  ext i j
  simp

@[simp]
theorem realPart_real_smul (r : ℝ) (A : _root_.Matrix m n ℂ) :
    realPart (r • A) = r • realPart A := by
  ext i j
  simp

@[simp]
theorem imagPart_real_smul (r : ℝ) (A : _root_.Matrix m n ℂ) :
    imagPart (r • A) = r • imagPart A := by
  ext i j
  simp

/--
Realification of a rectangular complex matrix, with the paper's block signs.
-/
def realify (A : _root_.Matrix m n ℂ) : _root_.Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  _root_.Matrix.fromBlocks (realPart A) (imagPart A) (-imagPart A) (realPart A)

@[simp]
theorem realify_apply_inl_inl (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inl i) (Sum.inl j) = (A i j).re :=
  rfl

@[simp]
theorem realify_apply_inl_inr (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inl i) (Sum.inr j) = (A i j).im :=
  rfl

@[simp]
theorem realify_apply_inr_inl (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inr i) (Sum.inl j) = -(A i j).im :=
  rfl

@[simp]
theorem realify_apply_inr_inr (A : _root_.Matrix m n ℂ) (i : m) (j : n) :
    realify A (Sum.inr i) (Sum.inr j) = (A i j).re :=
  rfl

@[simp]
theorem realify_zero :
    realify (0 : _root_.Matrix m n ℂ) = 0 := by
  simp [realify]

@[simp]
theorem realify_add (A B : _root_.Matrix m n ℂ) :
    realify (A + B) = realify A + realify B := by
  ext (i | i) (j | j)
  all_goals simp
  all_goals ring

@[simp]
theorem realify_neg (A : _root_.Matrix m n ℂ) :
    realify (-A) = -realify A := by
  ext (i | i) (j | j) <;> simp

@[simp]
theorem realify_sub (A B : _root_.Matrix m n ℂ) :
    realify (A - B) = realify A - realify B := by
  ext (i | i) (j | j)
  all_goals simp
  all_goals ring

@[simp]
theorem realify_real_smul (r : ℝ) (A : _root_.Matrix m n ℂ) :
    realify (r • A) = r • realify A := by
  ext (i | i) (j | j) <;> simp

/-- Equality of complex matrices is detected by their real and imaginary parts. -/
theorem eq_iff_realPart_eq_and_imagPart_eq {A B : _root_.Matrix m n ℂ} :
    A = B ↔ realPart A = realPart B ∧ imagPart A = imagPart B := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hre, him⟩
    ext i j
    apply Complex.ext
    · exact congrFun (congrFun hre i) j
    · exact congrFun (congrFun him i) j

/-- Realification loses no matrix entries. -/
theorem realify_injective :
    Function.Injective (realify : _root_.Matrix m n ℂ →
      _root_.Matrix (m ⊕ m) (n ⊕ n) ℝ) := by
  intro A B h
  apply eq_iff_realPart_eq_and_imagPart_eq.mpr
  constructor
  · exact congrArg _root_.Matrix.toBlocks₁₁ h
  · exact congrArg _root_.Matrix.toBlocks₁₂ h

@[simp]
theorem realify_inj {A B : _root_.Matrix m n ℂ} :
    realify A = realify B ↔ A = B :=
  realify_injective.eq_iff

/-- Real part of a compatible matrix product. -/
theorem realPart_mul [Fintype n] (A : _root_.Matrix m n ℂ)
    (B : _root_.Matrix n p ℂ) :
    realPart (A * B) = realPart A * realPart B - imagPart A * imagPart B := by
  ext i j
  simp [realPart, imagPart, _root_.Matrix.mul_apply, Complex.mul_re,
    Finset.sum_sub_distrib]

/-- Imaginary part of a compatible matrix product. -/
theorem imagPart_mul [Fintype n] (A : _root_.Matrix m n ℂ)
    (B : _root_.Matrix n p ℂ) :
    imagPart (A * B) = realPart A * imagPart B + imagPart A * realPart B := by
  ext i j
  simp [realPart, imagPart, _root_.Matrix.mul_apply, Complex.mul_im,
    Finset.sum_add_distrib]

/-- Realification preserves every compatible rectangular matrix product. -/
@[simp]
theorem realify_mul [Fintype n] (A : _root_.Matrix m n ℂ)
    (B : _root_.Matrix n p ℂ) :
    realify (A * B) = realify A * realify B := by
  rw [realify, realify, realify, _root_.Matrix.fromBlocks_multiply]
  simp only [realPart_mul, imagPart_mul]
  congr
  all_goals simp [_root_.Matrix.neg_mul, _root_.Matrix.mul_neg, sub_eq_add_neg]
  all_goals abel

@[simp]
theorem realPart_one [DecidableEq n] :
    realPart (1 : _root_.Matrix n n ℂ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realPart, _root_.Matrix.one_apply, h]

@[simp]
theorem imagPart_one [DecidableEq n] :
    imagPart (1 : _root_.Matrix n n ℂ) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [imagPart, h]

/-- Realification sends the complex identity matrix to the doubled real identity. -/
@[simp]
theorem realify_one [DecidableEq n] :
    realify (1 : _root_.Matrix n n ℂ) = 1 := by
  simp [realify, _root_.Matrix.fromBlocks_one]

/-- Real parts of a conjugate transpose become an ordinary transpose. -/
@[simp]
theorem realPart_conjTranspose (A : _root_.Matrix m n ℂ) :
    realPart (Aᴴ) = (realPart A)ᵀ := by
  ext i j
  simp

/-- Imaginary parts of a conjugate transpose are negated and transposed. -/
@[simp]
theorem imagPart_conjTranspose (A : _root_.Matrix m n ℂ) :
    imagPart (Aᴴ) = -(imagPart A)ᵀ := by
  ext i j
  simp

/-- Realification intertwines complex adjoint with real transpose. -/
@[simp]
theorem realify_conjTranspose (A : _root_.Matrix m n ℂ) :
    realify (Aᴴ) = (realify A)ᵀ := by
  rw [realify, realify, _root_.Matrix.fromBlocks_transpose]
  simp only [realPart_conjTranspose, imagPart_conjTranspose,
    _root_.Matrix.transpose_neg]
  congr
  all_goals abel

/--
The vector convention compatible with the paper's matrix signs: a complex
column `x + y*I` is represented by the real column `(x, -y)`.
-/
def realifyVec (v : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i ↦ (v i).re) (fun i ↦ -(v i).im)

@[simp]
theorem realifyVec_inl (v : n → ℂ) (i : n) :
    realifyVec v (Sum.inl i) = (v i).re :=
  rfl

@[simp]
theorem realifyVec_inr (v : n → ℂ) (i : n) :
    realifyVec v (Sum.inr i) = -(v i).im :=
  rfl

/-- Realification commutes with matrix action on the compatible vector encoding. -/
theorem realify_mulVec [Fintype n] (A : _root_.Matrix m n ℂ) (v : n → ℂ) :
    (realify A) *ᵥ realifyVec v = realifyVec (A *ᵥ v) := by
  ext (i | i)
  · simp [realify, realifyVec, _root_.Matrix.mulVec, dotProduct,
      Complex.mul_re, Finset.sum_sub_distrib]
    abel
  · simp [realify, realifyVec, _root_.Matrix.mulVec, dotProduct,
      Complex.mul_im, Finset.sum_add_distrib]

/--
A real matrix, regarded as complex, realifies to two identical diagonal
blocks.  Thus an already-real gate does not couple the two added sectors.
-/
theorem realify_map_ofReal (A : _root_.Matrix m n ℝ) :
    realify (A.map (algebraMap ℝ ℂ)) =
      _root_.Matrix.fromBlocks A 0 0 A := by
  ext (i | i) (j | j) <;> simp

/-! Exact scalar-matrix checks fixing the signs and sector order. -/

/-- The scalar `I`, viewed as a `1 × 1` matrix, has the advertised real block form. -/
theorem realify_I_scalar :
    realify (fun _ _ : Fin 1 ↦ Complex.I) =
      _root_.Matrix.fromBlocks
        (0 : _root_.Matrix (Fin 1) (Fin 1) ℝ)
        (1 : _root_.Matrix (Fin 1) (Fin 1) ℝ)
        (-1 : _root_.Matrix (Fin 1) (Fin 1) ℝ)
        (0 : _root_.Matrix (Fin 1) (Fin 1) ℝ) := by
  ext (i | i) (j | j) <;> simp [Fin.eq_zero]

example :
    realify (fun _ _ : Fin 1 ↦ Complex.I) (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp

example :
    realify (fun _ _ : Fin 1 ↦ Complex.I) (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp

end QuaternionicComputing.Matrix
