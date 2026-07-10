module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import QuaternionicComputing.Scalar.Quaternion

/-!
# Kronecker interchange with noncommutative coefficients

For compatible rectangular matrices, expanding

`(A ⊗ₖ B) * (C ⊗ₖ D)`

shows that each entry of `B` must cross an entry of `C`.  The usual
interchange identity therefore remains valid over a noncommutative semiring
when those two middle matrices commute entrywise.  No commutativity is needed
between any other pair of entries.

The final quaternionic examples make both sides of the correction explicit:
zero–one matrices are sufficient but not necessary, while middle entries `i`
and `j` make the interchange identity fail.
-/

@[expose] public noncomputable section

open scoped Matrix Kronecker Quaternion

namespace QuaternionicComputing.Matrix

/-- Every entry of `B` commutes with every entry of `C`, in that order. -/
def EntrywiseCommute {R m n p q : Type*} [Mul R]
    (B : _root_.Matrix m n R) (C : _root_.Matrix p q R) : Prop :=
  ∀ i j k l, Commute (B i j) (C k l)

/-- Entrywise commutation is symmetric after swapping the two matrices. -/
theorem EntrywiseCommute.symm
    {R m n p q : Type*} [Mul R]
    {B : _root_.Matrix m n R} {C : _root_.Matrix p q R}
    (h : EntrywiseCommute B C) : EntrywiseCommute C B := by
  intro k l i j
  exact (h i j k l).symm

/--
Corrected Kronecker interchange over a possibly noncommutative semiring.

The shapes are `A : l × m`, `B : n × p`, `C : m × q`, and
`D : p × r`.  Thus the only entries whose order changes are those of `B`
and `C`, exactly as recorded by `EntrywiseCommute B C`.
-/
theorem kronecker_mul_kronecker_of_entrywiseCommute
    {R l m n p q r : Type*} [Semiring R] [Fintype m] [Fintype p]
    (A : _root_.Matrix l m R) (B : _root_.Matrix n p R)
    (C : _root_.Matrix m q R) (D : _root_.Matrix p r R)
    (h : EntrywiseCommute B C) :
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by
  ext ⟨i, i'⟩ ⟨k, k'⟩
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.kronecker_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j' _
  exact (h i' j' j k).mul_mul_mul_comm (A i j) (D j' k')

/-- The familiar interchange identity follows when the coefficient semiring is commutative. -/
theorem kronecker_mul_kronecker_commutative
    {R l m n p q r : Type*} [CommSemiring R] [Fintype m] [Fintype p]
    (A : _root_.Matrix l m R) (B : _root_.Matrix n p R)
    (C : _root_.Matrix m q R) (D : _root_.Matrix p r R) :
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by
  apply kronecker_mul_kronecker_of_entrywiseCommute A B C D
  intro _ _ _ _
  exact Commute.all _ _

/-- Every entry of a zero–one matrix is either coefficient `0` or coefficient `1`. -/
def IsZeroOneMatrix {R m n : Type*} [Zero R] [One R]
    (A : _root_.Matrix m n R) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- A zero–one left middle factor commutes entrywise with every matrix. -/
theorem IsZeroOneMatrix.entrywiseCommute_left
    {R m n p q : Type*} [Semiring R]
    {B : _root_.Matrix m n R} (hB : IsZeroOneMatrix B)
    (C : _root_.Matrix p q R) : EntrywiseCommute B C := by
  intro i j k l
  rcases hB i j with hij | hij
  · rw [hij]
    exact Commute.zero_left _
  · rw [hij]
    exact Commute.one_left _

/-- A zero–one right middle factor commutes entrywise with every matrix. -/
theorem IsZeroOneMatrix.entrywiseCommute_right
    {R m n p q : Type*} [Semiring R]
    (B : _root_.Matrix m n R) {C : _root_.Matrix p q R}
    (hC : IsZeroOneMatrix C) : EntrywiseCommute B C := by
  intro i j k l
  rcases hC k l with hkl | hkl
  · rw [hkl]
    exact Commute.zero_right _
  · rw [hkl]
    exact Commute.one_right _

/-! ## Quaternionic one-by-one checks -/

namespace QuaternionExamples

open QuaternionicComputing.Quaternion

/-- Regard a quaternion as a `1 × 1` matrix. -/
def oneByOne (q : ℍ[ℝ]) : _root_.Matrix (Fin 1) (Fin 1) ℍ[ℝ] :=
  fun _ _ ↦ q

@[simp]
theorem oneByOne_apply (q : ℍ[ℝ]) (a b : Fin 1) : oneByOne q a b = q :=
  rfl

theorem i_ne_zero : i ≠ (0 : ℍ[ℝ]) := by
  intro h
  have hi := congrArg (fun q : ℍ[ℝ] ↦ q.imI) h
  norm_num at hi

theorem i_ne_one : i ≠ (1 : ℍ[ℝ]) := by
  intro h
  have hi := congrArg (fun q : ℍ[ℝ] ↦ q.imI) h
  norm_num at hi

theorem j_ne_zero : j ≠ (0 : ℍ[ℝ]) := by
  intro h
  have hj := congrArg (fun q : ℍ[ℝ] ↦ q.imJ) h
  norm_num at hj

theorem j_ne_one : j ≠ (1 : ℍ[ℝ]) := by
  intro h
  have hj := congrArg (fun q : ℍ[ℝ] ↦ q.imJ) h
  norm_num at hj

/-- The `1 × 1` matrix `[i]` is not a zero–one matrix. -/
theorem oneByOne_i_not_zeroOne : ¬ IsZeroOneMatrix (oneByOne i) := by
  intro h
  rcases h 0 0 with hi | hi
  · exact i_ne_zero hi
  · exact i_ne_one hi

/-- The `1 × 1` matrix `[j]` is not a zero–one matrix. -/
theorem oneByOne_j_not_zeroOne : ¬ IsZeroOneMatrix (oneByOne j) := by
  intro h
  rcases h 0 0 with hj | hj
  · exact j_ne_zero hj
  · exact j_ne_one hj

/--
Interchange can hold although the right-hand factors `C = [i]` and `D = [j]`
are neither zero–one matrices: the relevant middle entries are both `i`.
-/
theorem oneByOne_interchange_eq :
    (oneByOne j ⊗ₖ oneByOne i) * (oneByOne i ⊗ₖ oneByOne j) =
      (oneByOne j * oneByOne i) ⊗ₖ (oneByOne i * oneByOne j) := by
  apply kronecker_mul_kronecker_of_entrywiseCommute
  intro _ _ _ _
  exact Commute.refl i

/-- A bundled counterexample to the paper's claimed zero–one necessity. -/
theorem oneByOne_interchange_without_zeroOne :
    ¬ IsZeroOneMatrix (oneByOne i) ∧
      ¬ IsZeroOneMatrix (oneByOne j) ∧
      (oneByOne j ⊗ₖ oneByOne i) * (oneByOne i ⊗ₖ oneByOne j) =
        (oneByOne j * oneByOne i) ⊗ₖ (oneByOne i * oneByOne j) :=
  ⟨oneByOne_i_not_zeroOne, oneByOne_j_not_zeroOne,
    oneByOne_interchange_eq⟩

/--
Interchange fails when the middle `1 × 1` entries are `i` and `j`: the two
sides reduce respectively to `k` and `-k`.
-/
theorem oneByOne_interchange_i_j_failure :
    ¬ ((oneByOne 1 ⊗ₖ oneByOne i) * (oneByOne j ⊗ₖ oneByOne 1) =
      (oneByOne 1 * oneByOne j) ⊗ₖ (oneByOne i * oneByOne 1)) := by
  intro h
  have hentry := congrFun (congrFun h (0, 0)) (0, 0)
  simp only [Fin.isValue, _root_.Matrix.mul_apply,
    _root_.Matrix.kroneckerMap_apply, oneByOne, one_mul, mul_one, i_mul_j,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_unique, one_smul, Finset.univ_unique, Fin.default_eq_zero,
    Finset.card_singleton, j_mul_i] at hentry
  have himK := congrArg (fun q : ℍ[ℝ] ↦ q.imK) hentry
  norm_num at himK

end QuaternionExamples

end QuaternionicComputing.Matrix
