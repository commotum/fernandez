module

public import QuaternionicComputing.State.Basic
public import QuaternionicComputing.Matrix.Complexification

/-!
# Quaternionic state complexification

This module implements the two complex columns associated with the quaternion
matrix representation.  For a quaternionic column `ψ`, they are

`complexColumn0 ψ = (complexPart ψ, -conj (jPart ψ))`

and

`complexColumn1 ψ = (jPart ψ, conj (complexPart ψ))`.

Both maps are real-linear, injective, preserve every bottom-basis weight after
the two added sectors are summed, and intertwine quaternionic matrix action
with the public `complexify` matrix embedding.  These are dimension-correct
versions of the two state columns used in Equations (52)--(57) of the paper.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.State

open QuaternionicComputing.Quaternion

variable {m n : Type*}

/-- The first quaternion-to-complex state column `(Co ψ, -conj (W ψ))`. -/
def complexColumn0 (psi : n → ℍ[ℝ]) : n ⊕ n → ℂ :=
  Sum.elim (fun i ↦ complexPart (psi i)) (fun i ↦ -star (jPart (psi i)))

/-- The second quaternion-to-complex state column `(W ψ, conj (Co ψ))`. -/
def complexColumn1 (psi : n → ℍ[ℝ]) : n ⊕ n → ℂ :=
  Sum.elim (fun i ↦ jPart (psi i)) (fun i ↦ star (complexPart (psi i)))

@[simp]
theorem complexColumn0_inl (psi : n → ℍ[ℝ]) (i : n) :
    complexColumn0 psi (Sum.inl i) = complexPart (psi i) :=
  rfl

@[simp]
theorem complexColumn0_inr (psi : n → ℍ[ℝ]) (i : n) :
    complexColumn0 psi (Sum.inr i) = -star (jPart (psi i)) :=
  rfl

@[simp]
theorem complexColumn1_inl (psi : n → ℍ[ℝ]) (i : n) :
    complexColumn1 psi (Sum.inl i) = jPart (psi i) :=
  rfl

@[simp]
theorem complexColumn1_inr (psi : n → ℍ[ℝ]) (i : n) :
    complexColumn1 psi (Sum.inr i) = star (complexPart (psi i)) :=
  rfl

/-- The first state column bundled with its exact real scalar convention. -/
def complexColumn0Linear (n : Type*) : (n → ℍ[ℝ]) →ₗ[ℝ] (n ⊕ n → ℂ) where
  toFun := complexColumn0
  map_add' psi phi := by
    ext (i | i) <;> simp
  map_smul' r psi := by
    ext (i | i) <;> simp

/-- The second state column bundled with its exact real scalar convention. -/
def complexColumn1Linear (n : Type*) : (n → ℍ[ℝ]) →ₗ[ℝ] (n ⊕ n → ℂ) where
  toFun := complexColumn1
  map_add' psi phi := by
    ext (i | i) <;> simp
  map_smul' r psi := by
    ext (i | i) <;> simp

@[simp]
theorem complexColumn0Linear_apply (psi : n → ℍ[ℝ]) :
    complexColumn0Linear n psi = complexColumn0 psi :=
  rfl

@[simp]
theorem complexColumn1Linear_apply (psi : n → ℍ[ℝ]) :
    complexColumn1Linear n psi = complexColumn1 psi :=
  rfl

@[simp]
theorem complexColumn0_add (psi phi : n → ℍ[ℝ]) :
    complexColumn0 (psi + phi) = complexColumn0 psi + complexColumn0 phi :=
  (complexColumn0Linear n).map_add psi phi

@[simp]
theorem complexColumn1_add (psi phi : n → ℍ[ℝ]) :
    complexColumn1 (psi + phi) = complexColumn1 psi + complexColumn1 phi :=
  (complexColumn1Linear n).map_add psi phi

@[simp]
theorem complexColumn0_real_smul (r : ℝ) (psi : n → ℍ[ℝ]) :
    complexColumn0 (r • psi) = r • complexColumn0 psi :=
  (complexColumn0Linear n).map_smul r psi

@[simp]
theorem complexColumn1_real_smul (r : ℝ) (psi : n → ℍ[ℝ]) :
    complexColumn1 (r • psi) = r • complexColumn1 psi :=
  (complexColumn1Linear n).map_smul r psi

/-! ## Reconstruction and injectivity -/

/-- Reconstruct a quaternionic column from a target column in the first convention. -/
def quaternionOfComplexColumn0 (x : n ⊕ n → ℂ) : n → ℍ[ℝ] :=
  fun i ↦ (x (Sum.inl i) : ℍ[ℝ]) +
    ((-star (x (Sum.inr i)) : ℂ) : ℍ[ℝ]) * j

/-- Reconstruct a quaternionic column from a target column in the second convention. -/
def quaternionOfComplexColumn1 (x : n ⊕ n → ℂ) : n → ℍ[ℝ] :=
  fun i ↦ (star (x (Sum.inr i)) : ℂ) + (x (Sum.inl i) : ℍ[ℝ]) * j

@[simp]
theorem quaternionOfComplexColumn0_leftInverse (psi : n → ℍ[ℝ]) :
    quaternionOfComplexColumn0 (complexColumn0 psi) = psi := by
  funext i
  simpa [quaternionOfComplexColumn0] using
    (eq_complexPart_add_jPart_mul_j (psi i)).symm

@[simp]
theorem quaternionOfComplexColumn1_leftInverse (psi : n → ℍ[ℝ]) :
    quaternionOfComplexColumn1 (complexColumn1 psi) = psi := by
  funext i
  simpa [quaternionOfComplexColumn1] using
    (eq_complexPart_add_jPart_mul_j (psi i)).symm

/-- The first complex state column loses no quaternionic information. -/
theorem complexColumn0_injective : Function.Injective (@complexColumn0 n) :=
  Function.LeftInverse.injective quaternionOfComplexColumn0_leftInverse

/-- The second complex state column loses no quaternionic information. -/
theorem complexColumn1_injective : Function.Injective (@complexColumn1 n) :=
  Function.LeftInverse.injective quaternionOfComplexColumn1_leftInverse

/-! ## Compatible matrix action -/

/-- The first state column intertwines quaternionic action with complexification. -/
theorem complexify_mulVec_complexColumn0 [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (psi : n → ℍ[ℝ]) :
    complexify A *ᵥ complexColumn0 psi = complexColumn0 (A *ᵥ psi) := by
  ext (i | i)
  · change
      (∑ k, complexPart (A i k) * complexPart (psi k)) +
          ∑ k, jPart (A i k) * -star (jPart (psi k)) =
        complexPart (∑ k, A i k * psi k)
    rw [map_sum]
    simp_rw [complexPart_mul]
    simp [Finset.sum_sub_distrib]
  · change
      (∑ k, -star (jPart (A i k)) * complexPart (psi k)) +
          ∑ k, star (complexPart (A i k)) * -star (jPart (psi k)) =
        -star (jPart (∑ k, A i k * psi k))
    rw [map_sum]
    simp_rw [jPart_mul]
    simp [Finset.sum_add_distrib]
    ring

/-- The second state column intertwines quaternionic action with complexification. -/
theorem complexify_mulVec_complexColumn1 [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (psi : n → ℍ[ℝ]) :
    complexify A *ᵥ complexColumn1 psi = complexColumn1 (A *ᵥ psi) := by
  ext (i | i)
  · change
      (∑ k, complexPart (A i k) * jPart (psi k)) +
          ∑ k, jPart (A i k) * star (complexPart (psi k)) =
        jPart (∑ k, A i k * psi k)
    rw [map_sum]
    simp_rw [jPart_mul]
    simp [Finset.sum_add_distrib]
  · change
      (∑ k, -star (jPart (A i k)) * jPart (psi k)) +
          ∑ k, star (complexPart (A i k)) * star (complexPart (psi k)) =
        star (complexPart (∑ k, A i k * psi k))
    rw [map_sum]
    simp_rw [complexPart_mul]
    simp [Finset.sum_sub_distrib]
    ring

/-! ## Basis weights and total weights -/

/-- Sum the target weights over the two added sectors above one bottom basis index. -/
def bottomComplexWeight (phi : n ⊕ n → ℂ) (i : n) : ℝ :=
  complexBasisWeight phi (Sum.inl i) + complexBasisWeight phi (Sum.inr i)

/-- The first canonical column preserves each quaternionic basis weight. -/
@[simp]
theorem complexColumn0_bottomWeight (psi : n → ℍ[ℝ]) (i : n) :
    bottomComplexWeight (complexColumn0 psi) i = quaternionBasisWeight psi i := by
  simp [bottomComplexWeight, complexBasisWeight, basisWeight, complexWeight,
    quaternionBasisWeight, quaternionWeight, normSq_eq_complexPart_add_jPart]

/-- The second canonical column preserves each quaternionic basis weight. -/
@[simp]
theorem complexColumn1_bottomWeight (psi : n → ℍ[ℝ]) (i : n) :
    bottomComplexWeight (complexColumn1 psi) i = quaternionBasisWeight psi i := by
  simp [bottomComplexWeight, complexBasisWeight, basisWeight, complexWeight,
    quaternionBasisWeight, quaternionWeight, normSq_eq_complexPart_add_jPart, add_comm]

theorem complexTotalWeight_eq_sum_bottomComplexWeight [Fintype n]
    (phi : n ⊕ n → ℂ) :
    complexTotalWeight phi = ∑ i, bottomComplexWeight phi i := by
  simp [complexTotalWeight, totalWeight, bottomComplexWeight, complexBasisWeight,
    Fintype.sum_sum_type, Finset.sum_add_distrib]

/-- The first column preserves total state weight. -/
@[simp]
theorem complexColumn0_totalWeight [Fintype n] (psi : n → ℍ[ℝ]) :
    complexTotalWeight (complexColumn0 psi) = quaternionTotalWeight psi := by
  rw [complexTotalWeight_eq_sum_bottomComplexWeight]
  simp [quaternionTotalWeight, totalWeight]

/-- The second column preserves total state weight. -/
@[simp]
theorem complexColumn1_totalWeight [Fintype n] (psi : n → ℍ[ℝ]) :
    complexTotalWeight (complexColumn1 psi) = quaternionTotalWeight psi := by
  rw [complexTotalWeight_eq_sum_bottomComplexWeight]
  simp [quaternionTotalWeight, totalWeight]

/-! ## Orthogonality of the two columns -/

/-- The two target columns of any quaternionic state are complex-orthogonal. -/
theorem complexColumns_orthogonal [Fintype n] (psi : n → ℍ[ℝ]) :
    star (complexColumn0 psi) ⬝ᵥ complexColumn1 psi = 0 := by
  simp only [dotProduct, Fintype.sum_sum_type, complexColumn0_inl,
    complexColumn0_inr, complexColumn1_inl, complexColumn1_inr, Pi.star_apply,
    star_neg, star_star]
  rw [Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- Both representation columns have the same total squared norm. -/
theorem complexColumns_equal_norm [Fintype n] (psi : n → ℍ[ℝ]) :
    complexTotalWeight (complexColumn0 psi) =
      complexTotalWeight (complexColumn1 psi) := by
  simp

/-! ## Arbitrary top-qubit values -/

/-- Combine the two representation columns using arbitrary top-qubit amplitudes. -/
def complexTopCombination (a b : ℂ) (psi : n → ℍ[ℝ]) : n ⊕ n → ℂ :=
  a • complexColumn0 psi + b • complexColumn1 psi

@[simp]
theorem complexTopCombination_inl (a b : ℂ) (psi : n → ℍ[ℝ]) (i : n) :
    complexTopCombination a b psi (Sum.inl i) =
      a * complexPart (psi i) + b * jPart (psi i) := by
  simp [complexTopCombination]

@[simp]
theorem complexTopCombination_inr (a b : ℂ) (psi : n → ℍ[ℝ]) (i : n) :
    complexTopCombination a b psi (Sum.inr i) =
      a * -star (jPart (psi i)) + b * star (complexPart (psi i)) := by
  simp [complexTopCombination]

/-- Before top-state normalization, bottom weight scales by the top squared norm. -/
theorem complexTopCombination_bottomWeight (a b : ℂ) (psi : n → ℍ[ℝ]) (i : n) :
    bottomComplexWeight (complexTopCombination a b psi) i =
      (Complex.normSq a + Complex.normSq b) * quaternionBasisWeight psi i := by
  simp [bottomComplexWeight, complexBasisWeight, basisWeight, complexWeight,
    quaternionBasisWeight, quaternionWeight, Complex.normSq_apply,
    _root_.Quaternion.normSq_def']
  ring

/-- Every normalized top-qubit value preserves the bottom outcome weight. -/
theorem complexTopCombination_bottomWeight_of_normalized
    {a b : ℂ} (hab : Complex.normSq a + Complex.normSq b = 1)
    (psi : n → ℍ[ℝ]) (i : n) :
    bottomComplexWeight (complexTopCombination a b psi) i =
      quaternionBasisWeight psi i := by
  rw [complexTopCombination_bottomWeight, hab, one_mul]

theorem complexTopCombination_totalWeight [Fintype n]
    (a b : ℂ) (psi : n → ℍ[ℝ]) :
    complexTotalWeight (complexTopCombination a b psi) =
      (Complex.normSq a + Complex.normSq b) * quaternionTotalWeight psi := by
  rw [complexTotalWeight_eq_sum_bottomComplexWeight]
  simp_rw [complexTopCombination_bottomWeight]
  simp [quaternionTotalWeight, totalWeight, Finset.mul_sum]

/-! ## Normalized-state constructors -/

/-- The first state column sends normalized quaternionic states to normalized complex states. -/
def complexColumn0State [Fintype n] (psi : QuaternionState n) : ComplexState (n ⊕ n) :=
  ⟨complexColumn0 psi, by simpa using psi.totalWeight_eq_one⟩

/-- The second state column sends normalized quaternionic states to normalized complex states. -/
def complexColumn1State [Fintype n] (psi : QuaternionState n) : ComplexState (n ⊕ n) :=
  ⟨complexColumn1 psi, by simpa using psi.totalWeight_eq_one⟩

/-- A normalized top qubit and normalized quaternionic state give a normalized target state. -/
def complexTopCombinationState [Fintype n]
    (a b : ℂ) (hab : Complex.normSq a + Complex.normSq b = 1)
    (psi : QuaternionState n) : ComplexState (n ⊕ n) :=
  ⟨complexTopCombination a b psi, by
    rw [complexTopCombination_totalWeight, hab, psi.totalWeight_eq_one, one_mul]⟩

/-! ## Canonical basis and quaternionic sign checks -/

/-- The first column sends a quaternionic basis vector to the first complex sector. -/
theorem complexColumn0_basis [DecidableEq n] (i : n) :
    complexColumn0 (Pi.single i (1 : ℍ[ℝ])) =
      Pi.single (Sum.inl i) (1 : ℂ) := by
  ext (k | k) <;> simp [Pi.single_apply, eq_comm]

/-- The second column sends a quaternionic basis vector to the second complex sector. -/
theorem complexColumn1_basis [DecidableEq n] (i : n) :
    complexColumn1 (Pi.single i (1 : ℍ[ℝ])) =
      Pi.single (Sum.inr i) (1 : ℂ) := by
  ext (k | k) <;> simp [Pi.single_apply, eq_comm]

/-- A one-coordinate state with amplitude `j`, used to guard genuinely quaternionic signs. -/
def quaternionicJExample : Unit → ℍ[ℝ] :=
  fun _ ↦ j

@[simp]
theorem complexColumn0_quaternionicJExample_inl :
    complexColumn0 quaternionicJExample (Sum.inl ()) = 0 := by
  simp [quaternionicJExample]

@[simp]
theorem complexColumn0_quaternionicJExample_inr :
    complexColumn0 quaternionicJExample (Sum.inr ()) = -1 := by
  simp [quaternionicJExample]

@[simp]
theorem complexColumn1_quaternionicJExample_inl :
    complexColumn1 quaternionicJExample (Sum.inl ()) = 1 := by
  simp [quaternionicJExample]

@[simp]
theorem complexColumn1_quaternionicJExample_inr :
    complexColumn1 quaternionicJExample (Sum.inr ()) = 0 := by
  simp [quaternionicJExample]

theorem quaternionicJExample_bottomWeight :
    bottomComplexWeight (complexColumn0 quaternionicJExample) () = 1 := by
  simp [quaternionicBasisWeight, basisWeight, quaternionWeight,
    quaternionicJExample, _root_.Quaternion.normSq_def']

end QuaternionicComputing.State
