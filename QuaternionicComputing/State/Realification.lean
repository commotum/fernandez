module

public import QuaternionicComputing.State.Basic
public import QuaternionicComputing.Matrix.Realification

/-!
# Complex states as pairs of real state columns

For the realification convention

`a + b * I ↦ [[a, b], [-b, a]]`,

a complex column `ψ` has two canonical real representatives

* `realColumn0 ψ = (re ψ, -im ψ)`, and
* `realColumn1 ψ = (im ψ, re ψ)`.

Both columns intertwine arbitrary compatible complex matrix actions with
matrix realification.  They have equal total weight, are orthogonal, and give
the same bottom-system computational-basis weights.  More generally, every
normalized real combination of the two columns has the same bottom weights.

The reduced outer product near the end of the file is the explicit finite
matrix needed for the paper's density-matrix calculation.  It deliberately
does not introduce a partial-trace hierarchy.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.State

variable {m n : Type*}

/-- The first canonical real column `(re ψ, -im ψ)`. -/
def realColumn0 (v : n → ℂ) : n ⊕ n → ℝ :=
  QuaternionicComputing.Matrix.realifyVec v

/-- The second canonical real column `(im ψ, re ψ)`. -/
def realColumn1 (v : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i ↦ (v i).im) (fun i ↦ (v i).re)

@[simp]
theorem realColumn0_inl (v : n → ℂ) (i : n) :
    realColumn0 v (Sum.inl i) = (v i).re :=
  rfl

@[simp]
theorem realColumn0_inr (v : n → ℂ) (i : n) :
    realColumn0 v (Sum.inr i) = -(v i).im :=
  rfl

@[simp]
theorem realColumn1_inl (v : n → ℂ) (i : n) :
    realColumn1 v (Sum.inl i) = (v i).im :=
  rfl

@[simp]
theorem realColumn1_inr (v : n → ℂ) (i : n) :
    realColumn1 v (Sum.inr i) = (v i).re :=
  rfl

/-- The first real column, bundled as a real-linear map. -/
def realColumn0Linear : (n → ℂ) →ₗ[ℝ] (n ⊕ n → ℝ) where
  toFun := realColumn0
  map_add' v w := by
    ext (i | i) <;> simp [realColumn0]
  map_smul' r v := by
    ext (i | i) <;> simp [realColumn0]

/-- The second real column, bundled as a real-linear map. -/
def realColumn1Linear : (n → ℂ) →ₗ[ℝ] (n ⊕ n → ℝ) where
  toFun := realColumn1
  map_add' v w := by
    ext (i | i) <;> simp [realColumn1]
  map_smul' r v := by
    ext (i | i) <;> simp [realColumn1]

@[simp]
theorem realColumn0Linear_apply (v : n → ℂ) :
    realColumn0Linear v = realColumn0 v :=
  rfl

@[simp]
theorem realColumn1Linear_apply (v : n → ℂ) :
    realColumn1Linear v = realColumn1 v :=
  rfl

/-- Reconstruct a complex vector from a candidate first real column. -/
def complexOfRealColumn0 (w : n ⊕ n → ℝ) : n → ℂ :=
  fun i ↦ ⟨w (Sum.inl i), -w (Sum.inr i)⟩

/-- Reconstruct a complex vector from a candidate second real column. -/
def complexOfRealColumn1 (w : n ⊕ n → ℝ) : n → ℂ :=
  fun i ↦ ⟨w (Sum.inr i), w (Sum.inl i)⟩

@[simp]
theorem complexOfRealColumn0_realColumn0 (v : n → ℂ) :
    complexOfRealColumn0 (realColumn0 v) = v := by
  ext i <;> simp [complexOfRealColumn0]

@[simp]
theorem complexOfRealColumn1_realColumn1 (v : n → ℂ) :
    complexOfRealColumn1 (realColumn1 v) = v := by
  ext i <;> simp [complexOfRealColumn1]

/-- The first state-column encoding loses no complex amplitudes. -/
theorem realColumn0_injective :
    Function.Injective (realColumn0 : (n → ℂ) → (n ⊕ n → ℝ)) :=
  Function.LeftInverse.injective (complexOfRealColumn0_realColumn0 (n := n))

/-- The second state-column encoding loses no complex amplitudes. -/
theorem realColumn1_injective :
    Function.Injective (realColumn1 : (n → ℂ) → (n ⊕ n → ℝ)) :=
  Function.LeftInverse.injective (complexOfRealColumn1_realColumn1 (n := n))

/-! ## Basis vectors -/

/-- Paper Equation (20): the first column sends a complex basis vector to the
first real sector. -/
theorem realColumn0_single [DecidableEq n] (i : n) :
    realColumn0 (Pi.single i (1 : ℂ)) = Pi.single (Sum.inl i) (1 : ℝ) := by
  ext (j | j) <;> by_cases h : j = i <;> simp [realColumn0, h]

/-- Paper Equation (21): the second column sends a complex basis vector to the
second real sector. -/
theorem realColumn1_single [DecidableEq n] (i : n) :
    realColumn1 (Pi.single i (1 : ℂ)) = Pi.single (Sum.inr i) (1 : ℝ) := by
  ext (j | j) <;> by_cases h : j = i <;> simp [realColumn1, h]

/-! ## Compatible rectangular matrix actions -/

/-- Correctly typed first-column version of the paper's state-intertwining
identity.  The source matrix may be rectangular. -/
theorem realify_mulVec_realColumn0 [Fintype n]
    (A : _root_.Matrix m n ℂ) (v : n → ℂ) :
    QuaternionicComputing.Matrix.realify A *ᵥ realColumn0 v =
      realColumn0 (A *ᵥ v) :=
  QuaternionicComputing.Matrix.realify_mulVec A v

/-- Correctly typed second-column version of the paper's state-intertwining
identity.  The source matrix may be rectangular. -/
theorem realify_mulVec_realColumn1 [Fintype n]
    (A : _root_.Matrix m n ℂ) (v : n → ℂ) :
    QuaternionicComputing.Matrix.realify A *ᵥ realColumn1 v =
      realColumn1 (A *ᵥ v) := by
  ext (i | i)
  · simp [QuaternionicComputing.Matrix.realify, realColumn1,
      _root_.Matrix.mulVec, dotProduct, Complex.mul_im,
      Finset.sum_add_distrib]
  · simp [QuaternionicComputing.Matrix.realify, realColumn1,
      _root_.Matrix.mulVec, dotProduct, Complex.mul_re,
      Finset.sum_sub_distrib]

/-! ## Norms and orthogonality -/

/-- The first column has the same squared norm as the complex source vector. -/
theorem realColumn0_dot_self [Fintype n] (v : n → ℂ) :
    realColumn0 v ⬝ᵥ realColumn0 v = ∑ i, Complex.normSq (v i) := by
  simp [dotProduct, realColumn0, Complex.normSq_apply,
    Finset.sum_add_distrib]

/-- The second column has the same squared norm as the complex source vector. -/
theorem realColumn1_dot_self [Fintype n] (v : n → ℂ) :
    realColumn1 v ⬝ᵥ realColumn1 v = ∑ i, Complex.normSq (v i) := by
  simp [dotProduct, realColumn1, Complex.normSq_apply,
    Finset.sum_add_distrib, add_comm]

/-- The two canonical real columns are orthogonal. -/
theorem realColumns_orthogonal [Fintype n] (v : n → ℂ) :
    realColumn0 v ⬝ᵥ realColumn1 v = 0 := by
  simp [dotProduct, realColumn0, realColumn1, Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, mul_comm]

/-- The two canonical real columns have equal squared norm. -/
theorem realColumns_equal_norm [Fintype n] (v : n → ℂ) :
    realColumn0 v ⬝ᵥ realColumn0 v =
      realColumn1 v ⬝ᵥ realColumn1 v := by
  rw [realColumn0_dot_self, realColumn1_dot_self]

/-! ## Computational-basis weights -/

/-- Sum the two real sector weights over a fixed bottom-system index. -/
def bottomRealWeight (w : n ⊕ n → ℝ) (i : n) : ℝ :=
  realBasisWeight w (Sum.inl i) + realBasisWeight w (Sum.inr i)

@[simp]
theorem bottomRealWeight_apply (w : n ⊕ n → ℝ) (i : n) :
    bottomRealWeight w i =
      realWeight (w (Sum.inl i)) + realWeight (w (Sum.inr i)) :=
  rfl

/-- The first canonical column preserves each bottom computational-basis
outcome weight. -/
@[simp]
theorem realColumn0_bottomWeight (v : n → ℂ) (i : n) :
    bottomRealWeight (realColumn0 v) i = complexBasisWeight v i := by
  simp [bottomRealWeight, realBasisWeight, complexBasisWeight, basisWeight,
    realWeight, complexWeight, Complex.normSq_apply]

/-- The second canonical column preserves each bottom computational-basis
outcome weight. -/
@[simp]
theorem realColumn1_bottomWeight (v : n → ℂ) (i : n) :
    bottomRealWeight (realColumn1 v) i = complexBasisWeight v i := by
  simp [bottomRealWeight, realBasisWeight, complexBasisWeight, basisWeight,
    realWeight, complexWeight, Complex.normSq_apply, add_comm]

/-- A real top-state combination of the two canonical columns. -/
def realTopCombination (a b : ℝ) (v : n → ℂ) : n ⊕ n → ℝ :=
  a • realColumn0 v + b • realColumn1 v

@[simp]
theorem realTopCombination_inl (a b : ℝ) (v : n → ℂ) (i : n) :
    realTopCombination a b v (Sum.inl i) =
      a * (v i).re + b * (v i).im := by
  simp [realTopCombination]

@[simp]
theorem realTopCombination_inr (a b : ℝ) (v : n → ℂ) (i : n) :
    realTopCombination a b v (Sum.inr i) =
      -a * (v i).im + b * (v i).re := by
  simp [realTopCombination]
  ring

/-- Before normalizing the top amplitudes, every bottom weight is scaled by
their total real weight. -/
theorem realTopCombination_bottomWeight (a b : ℝ) (v : n → ℂ) (i : n) :
    bottomRealWeight (realTopCombination a b v) i =
      (realWeight a + realWeight b) * complexBasisWeight v i := by
  simp [bottomRealWeight, realBasisWeight, complexBasisWeight, basisWeight,
    realWeight, complexWeight, Complex.normSq_apply]
  ring

/-- A normalized real top state leaves every bottom computational-basis
weight unchanged. -/
theorem realTopCombination_bottomWeight_of_normalized
    {a b : ℝ} (h : realWeight a + realWeight b = 1)
    (v : n → ℂ) (i : n) :
    bottomRealWeight (realTopCombination a b v) i = complexBasisWeight v i := by
  rw [realTopCombination_bottomWeight, h, one_mul]

/-! ## Total weights and normalized states -/

@[simp]
theorem realTotalWeight_realColumn0 [Fintype n] (v : n → ℂ) :
    realTotalWeight (realColumn0 v) = complexTotalWeight v := by
  simp [realTotalWeight, complexTotalWeight, totalWeight, realBasisWeight,
    complexBasisWeight, basisWeight, realWeight, complexWeight,
    Complex.normSq_apply, Finset.sum_add_distrib]

@[simp]
theorem realTotalWeight_realColumn1 [Fintype n] (v : n → ℂ) :
    realTotalWeight (realColumn1 v) = complexTotalWeight v := by
  simp [realTotalWeight, complexTotalWeight, totalWeight, realBasisWeight,
    complexBasisWeight, basisWeight, realWeight, complexWeight,
    Complex.normSq_apply, Finset.sum_add_distrib, add_comm]

theorem realTotalWeight_realTopCombination [Fintype n]
    (a b : ℝ) (v : n → ℂ) :
    realTotalWeight (realTopCombination a b v) =
      (realWeight a + realWeight b) * complexTotalWeight v := by
  rw [show realTotalWeight (realTopCombination a b v) =
      ∑ i, bottomRealWeight (realTopCombination a b v) i by
    simp [realTotalWeight, totalWeight, bottomRealWeight, realBasisWeight,
      basisWeight, Fintype.sum_sum_type]]
  simp_rw [realTopCombination_bottomWeight]
  simp [complexTotalWeight, totalWeight, complexBasisWeight, basisWeight,
    Finset.mul_sum]

/-- The first column maps normalized complex states to normalized real states. -/
def realColumn0State [Fintype n] (v : ComplexState n) : RealState (n ⊕ n) :=
  ⟨realColumn0 v, by
    rw [realTotalWeight_realColumn0]
    exact v.property⟩

/-- The second column maps normalized complex states to normalized real states. -/
def realColumn1State [Fintype n] (v : ComplexState n) : RealState (n ⊕ n) :=
  ⟨realColumn1 v, by
    rw [realTotalWeight_realColumn1]
    exact v.property⟩

/-- Every normalized real top combination maps a normalized complex state to
a normalized real state. -/
def realTopCombinationState [Fintype n]
    (a b : ℝ) (h : realWeight a + realWeight b = 1)
    (v : ComplexState n) : RealState (n ⊕ n) :=
  ⟨realTopCombination a b v, by
    rw [realTotalWeight_realTopCombination, h, one_mul]
    exact v.property⟩

/-! ## Explicit reduced outer product -/

/-- Trace out the added two-sector coordinate in a real rank-one outer
product, written directly as the finite matrix used by the paper. -/
def reducedRealOuter (w : n ⊕ n → ℝ) : _root_.Matrix n n ℝ :=
  fun i j ↦
    w (Sum.inl i) * w (Sum.inl j) +
      w (Sum.inr i) * w (Sum.inr j)

@[simp]
theorem reducedRealOuter_apply (w : n ⊕ n → ℝ) (i j : n) :
    reducedRealOuter w i j =
      w (Sum.inl i) * w (Sum.inl j) +
        w (Sum.inr i) * w (Sum.inr j) :=
  rfl

/-- Both canonical real columns give exactly the same reduced outer product,
the corrected direct form of the paper's Lemma 5 calculation. -/
theorem reducedRealOuter_realColumns (v : n → ℂ) :
    reducedRealOuter (realColumn0 v) =
      reducedRealOuter (realColumn1 v) := by
  ext i j
  simp [reducedRealOuter]
  ring

/-- The common reduced outer product is the real part of the complex rank-one
outer product. -/
theorem reducedRealOuter_realColumn0 (v : n → ℂ) (i j : n) :
    reducedRealOuter (realColumn0 v) i j =
      (v i * star (v j)).re := by
  simp [reducedRealOuter, Complex.mul_re]
  ring

/-- The diagonal of the reduced outer product is exactly the bottom outcome
weight. -/
@[simp]
theorem reducedRealOuter_diagonal (w : n ⊕ n → ℝ) (i : n) :
    reducedRealOuter w i i = bottomRealWeight w i := by
  simp [reducedRealOuter, bottomRealWeight, realBasisWeight, basisWeight,
    realWeight]

/-! ## Sign sanity check -/

/-- A genuinely non-real amplitude fixes both the sign and sector order: the
first encoding sends `I` to `-1` in the second sector, while the second sends
it to `1` in the first sector. -/
theorem realColumns_I_sanity :
    realColumn0 (fun _ : Fin 1 ↦ Complex.I) (Sum.inr 0) = -1 ∧
      realColumn1 (fun _ : Fin 1 ↦ Complex.I) (Sum.inl 0) = 1 := by
  simp

end QuaternionicComputing.State
