module

public import QuaternionicComputing.Scalar.Quaternion
public import Mathlib.Data.Matrix.Block

/-!
# Complexification of quaternionic matrices

This module realizes a quaternionic matrix as a complex block matrix.  For the
scalar decomposition

`q = complexPart q + jPart q * j`,

the block convention is

`[[complexPart A, jPart A], [-conj (jPart A), conj (complexPart A)]]`.

The conjugations in the lower blocks are entrywise.  They are deliberately
written with `Matrix.map star`, rather than matrix `star`, because the latter
also transposes a square matrix.  The construction is rectangular, while the
multiplication and bundled ring-homomorphism APIs specialize dimensions only
as required by matrix multiplication.
-/

@[expose] public noncomputable section

open scoped Quaternion Matrix

namespace QuaternionicComputing.Quaternion

/-- Apply `complexPart` entrywise to a quaternionic matrix. -/
def complexPartMatrix {m n : Type*} (A : Matrix m n ℍ[ℝ]) : Matrix m n ℂ :=
  A.map complexPart

/-- Apply `jPart` entrywise to a quaternionic matrix. -/
def jPartMatrix {m n : Type*} (A : Matrix m n ℍ[ℝ]) : Matrix m n ℂ :=
  A.map jPart

@[simp]
theorem complexPartMatrix_apply {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    complexPartMatrix A i j = complexPart (A i j) :=
  rfl

@[simp]
theorem jPartMatrix_apply {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    jPartMatrix A i j = jPart (A i j) :=
  rfl

@[simp]
theorem complexPartMatrix_zero {m n : Type*} :
    complexPartMatrix (0 : Matrix m n ℍ[ℝ]) = 0 := by
  ext i j
  simp

@[simp]
theorem jPartMatrix_zero {m n : Type*} :
    jPartMatrix (0 : Matrix m n ℍ[ℝ]) = 0 := by
  ext i j
  simp

@[simp]
theorem complexPartMatrix_add {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    complexPartMatrix (A + B) = complexPartMatrix A + complexPartMatrix B := by
  ext i j
  simp

@[simp]
theorem jPartMatrix_add {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    jPartMatrix (A + B) = jPartMatrix A + jPartMatrix B := by
  ext i j
  simp

@[simp]
theorem complexPartMatrix_neg {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    complexPartMatrix (-A) = -complexPartMatrix A := by
  ext i j
  simp

@[simp]
theorem jPartMatrix_neg {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    jPartMatrix (-A) = -jPartMatrix A := by
  ext i j
  simp

@[simp]
theorem complexPartMatrix_sub {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    complexPartMatrix (A - B) = complexPartMatrix A - complexPartMatrix B := by
  ext i j
  simp

@[simp]
theorem jPartMatrix_sub {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    jPartMatrix (A - B) = jPartMatrix A - jPartMatrix B := by
  ext i j
  simp

@[simp]
theorem complexPartMatrix_one {n : Type*} [DecidableEq n] :
    complexPartMatrix (1 : Matrix n n ℍ[ℝ]) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext <;> simp [complexPart]
  · simp [hij]

@[simp]
theorem jPartMatrix_one {n : Type*} [DecidableEq n] :
    jPartMatrix (1 : Matrix n n ℍ[ℝ]) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext <;> simp [jPart]
  · simp [hij]

/-!
The next two identities lift the scalar multiplication formulas through the
finite sum defining matrix multiplication.
-/

theorem complexPartMatrix_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n p ℍ[ℝ]) :
    complexPartMatrix (A * B) =
      complexPartMatrix A * complexPartMatrix B -
        jPartMatrix A * (jPartMatrix B).map star := by
  ext i k
  change complexPart (∑ j, A i j * B j k) = _
  rw [map_sum]
  simp_rw [complexPart_mul]
  simp [complexPartMatrix, jPartMatrix, Matrix.mul_apply, Finset.sum_sub_distrib]

theorem jPartMatrix_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n p ℍ[ℝ]) :
    jPartMatrix (A * B) =
      complexPartMatrix A * jPartMatrix B +
        jPartMatrix A * (complexPartMatrix B).map star := by
  ext i k
  change jPart (∑ j, A i j * B j k) = _
  rw [map_sum]
  simp_rw [jPart_mul]
  simp [complexPartMatrix, jPartMatrix, Matrix.mul_apply, Finset.sum_add_distrib]

@[simp]
theorem complexPartMatrix_conjTranspose {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    complexPartMatrix Aᴴ = (complexPartMatrix A)ᴴ := by
  ext i j
  simp

@[simp]
theorem jPartMatrix_conjTranspose {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    jPartMatrix Aᴴ = -(jPartMatrix A)ᵀ := by
  ext i j
  simp

/--
The canonical complex block realization of a quaternionic matrix.

The row and column types are sums so the result has exactly twice each finite
dimension, without choosing enumerations of either index type.
-/
def complexify {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    Matrix (m ⊕ m) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    (complexPartMatrix A)
    (jPartMatrix A)
    (-((jPartMatrix A).map star))
    ((complexPartMatrix A).map star)

@[simp]
theorem complexify_apply_inl_inl {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    complexify A (Sum.inl i) (Sum.inl j) = complexPart (A i j) :=
  rfl

@[simp]
theorem complexify_apply_inl_inr {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    complexify A (Sum.inl i) (Sum.inr j) = jPart (A i j) :=
  rfl

@[simp]
theorem complexify_apply_inr_inl {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    complexify A (Sum.inr i) (Sum.inl j) = -star (jPart (A i j)) :=
  rfl

@[simp]
theorem complexify_apply_inr_inr {m n : Type*} (A : Matrix m n ℍ[ℝ]) (i : m) (j : n) :
    complexify A (Sum.inr i) (Sum.inr j) = star (complexPart (A i j)) :=
  rfl

/-- Equality of complexifications is detected by their two independent upper blocks. -/
theorem complexify_eq_iff_parts {m n : Type*} {A B : Matrix m n ℍ[ℝ]} :
    complexify A = complexify B ↔
      complexPartMatrix A = complexPartMatrix B ∧ jPartMatrix A = jPartMatrix B := by
  constructor
  · intro h
    have hblocks := Matrix.fromBlocks_inj.mp h
    exact ⟨hblocks.1, hblocks.2.1⟩
  · rintro ⟨hcomplex, hj⟩
    simp only [complexify, hcomplex, hj]

/-- The quaternion-to-complex matrix realization loses no entries. -/
theorem complexify_injective {m n : Type*} :
    Function.Injective (@complexify m n) := by
  intro A B h
  rw [complexify_eq_iff_parts] at h
  apply Matrix.ext
  intro i j
  exact ext_parts (congrFun (congrFun h.1 i) j) (congrFun (congrFun h.2 i) j)

@[simp]
theorem complexify_eq_iff {m n : Type*} {A B : Matrix m n ℍ[ℝ]} :
    complexify A = complexify B ↔ A = B :=
  complexify_injective.eq_iff

@[simp]
theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℍ[ℝ]) = 0 := by
  simp [complexify]

@[simp]
theorem complexify_add {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [add_comm]

@[simp]
theorem complexify_neg {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    complexify (-A) = -complexify A := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

@[simp]
theorem complexify_sub {m n : Type*} (A B : Matrix m n ℍ[ℝ]) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [sub_eq_add_neg, add_comm]

@[simp]
theorem complexify_one {n : Type*} [DecidableEq n] :
    complexify (1 : Matrix n n ℍ[ℝ]) = 1 := by
  simp [complexify]

/-- Complexification preserves compatible-shape matrix multiplication. -/
theorem complexify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n p ℍ[ℝ]) :
    complexify (A * B) = complexify A * complexify B := by
  rw [complexify, complexify, complexify, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using complexPartMatrix_mul A B
  · exact jPartMatrix_mul A B
  · ext i k
    change -star (jPart (∑ j, A i j * B j k)) = _
    rw [map_sum]
    simp_rw [jPart_mul]
    simp [complexPartMatrix, jPartMatrix, Matrix.mul_apply, Finset.sum_add_distrib]
  · ext i k
    change star (complexPart (∑ j, A i j * B j k)) = _
    rw [map_sum]
    simp_rw [complexPart_mul]
    simp [complexPartMatrix, jPartMatrix, Matrix.mul_apply, Finset.sum_sub_distrib]
    ring

/-- Complexification commutes with the matrix adjoint. -/
@[simp]
theorem complexify_conjTranspose {m n : Type*} (A : Matrix m n ℍ[ℝ]) :
    complexify Aᴴ = (complexify A)ᴴ := by
  rw [complexify, complexify, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> simp

/-- The block-vector action corresponding to `complexify`. -/
theorem complexify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (x : n ⊕ n → ℂ) :
    complexify A *ᵥ x =
      Sum.elim
        (complexPartMatrix A *ᵥ (x ∘ Sum.inl) + jPartMatrix A *ᵥ (x ∘ Sum.inr))
        (-((jPartMatrix A).map star) *ᵥ (x ∘ Sum.inl) +
          (complexPartMatrix A).map star *ᵥ (x ∘ Sum.inr)) := by
  exact Matrix.fromBlocks_mulVec _ _ _ _ x

/-- Complexification as an injective ring homomorphism on square finite matrices. -/
def complexifyRingHom (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℍ[ℝ] →+* Matrix (n ⊕ n) (n ⊕ n) ℂ where
  toFun := complexify
  map_one' := complexify_one
  map_mul' := complexify_mul
  map_zero' := complexify_zero
  map_add' := complexify_add

@[simp]
theorem complexifyRingHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : Matrix n n ℍ[ℝ]) :
    complexifyRingHom n A = complexify A :=
  rfl

/-- The bundled square-matrix complexification is injective. -/
theorem complexifyRingHom_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (complexifyRingHom n) :=
  complexify_injective

/-! A one-entry sanity check fixes the signs of the `j` image. -/

theorem complexify_j_scalar :
    complexify (fun _ _ : Unit ↦ j) =
      Matrix.fromBlocks
        (0 : Matrix Unit Unit ℂ) 1 (-1) (0 : Matrix Unit Unit ℂ) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> simp

end QuaternionicComputing.Quaternion
