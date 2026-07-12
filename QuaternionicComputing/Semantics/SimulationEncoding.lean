module

public import QuaternionicComputing.Semantics.Simulation
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification

/-!
# Exact representative encodings used by cross-model simulations

This leaf certifies the two canonical complex-to-doubled-real state columns
and the two canonical quaternion-to-doubled-complex state columns as exact,
total-weight-preserving encodings.  Each raw coordinate map is a real-linear
equivalence with the displayed decoder, and each restriction to normalized
states is an equivalence as well.

These are bijective changes of scalar and sum-index coordinates.  Their
`LinearEquiv` and `Equiv` values record representative-level coordinate
bijections, not same-space equality, ray equivalence, or circuit behavioral
equivalence.  Nothing here asserts a top-sector marginal, a mixed-state
encoding, channel equality, or all-measurement agreement.  Orthogonality of
the paired columns remains in the underlying state modules and is not
duplicated here.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.Semantics

universe u

/-! ## Complex columns represented over the reals -/

/-- The first doubled-real column reconstructs its complex source exactly. -/
theorem realColumn0_exactStateEncoding {I : Type u} :
    ExactStateEncoding
      (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
      State.complexOfRealColumn0 :=
  State.complexOfRealColumn0_realColumn0

/-- The second doubled-real column reconstructs its complex source exactly. -/
theorem realColumn1_exactStateEncoding {I : Type u} :
    ExactStateEncoding
      (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
      State.complexOfRealColumn1 :=
  State.complexOfRealColumn1_realColumn1

/-- The displayed decoder is also a right inverse to the first real column. -/
theorem realColumn0_rightInverse {I : Type u} :
    Function.RightInverse
      (State.complexOfRealColumn0 : (I ⊕ I → ℝ) → (I → ℂ))
      State.realColumn0 := by
  intro target
  funext i
  rcases i with i | i
  · simp [State.realColumn0, State.complexOfRealColumn0]
  · simp [State.realColumn0, State.complexOfRealColumn0]

/-- The displayed decoder is also a right inverse to the second real column. -/
theorem realColumn1_rightInverse {I : Type u} :
    Function.RightInverse
      (State.complexOfRealColumn1 : (I ⊕ I → ℝ) → (I → ℂ))
      State.realColumn1 := by
  intro target
  funext i
  rcases i with i | i
  · simp [State.realColumn1, State.complexOfRealColumn1]
  · simp [State.realColumn1, State.complexOfRealColumn1]

/-- The first doubled-real representative is exact and preserves total weight. -/
theorem realColumn0_losslessStateEncoding {I : Type u} [Fintype I] :
    LosslessStateEncoding
      (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
      State.complexOfRealColumn0 State.complexTotalWeight
      State.realTotalWeight :=
  ⟨realColumn0_exactStateEncoding, State.realTotalWeight_realColumn0⟩

/-- The second doubled-real representative is exact and preserves total weight. -/
theorem realColumn1_losslessStateEncoding {I : Type u} [Fintype I] :
    LosslessStateEncoding
      (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
      State.complexOfRealColumn1 State.complexTotalWeight
      State.realTotalWeight :=
  ⟨realColumn1_exactStateEncoding, State.realTotalWeight_realColumn1⟩

/--
The first raw doubled-real coordinate convention is a real-linear
equivalence, with `complexOfRealColumn0` as its explicit inverse.
-/
def realColumn0LinearEquiv (I : Type u) :
    (I → ℂ) ≃ₗ[ℝ] (I ⊕ I → ℝ) where
  toFun := State.realColumn0
  invFun := State.complexOfRealColumn0
  left_inv := State.complexOfRealColumn0_realColumn0
  right_inv := realColumn0_rightInverse
  map_add' := State.realColumn0Linear.map_add
  map_smul' := State.realColumn0Linear.map_smul

/--
The second raw doubled-real coordinate convention is a real-linear
equivalence, with `complexOfRealColumn1` as its explicit inverse.
-/
def realColumn1LinearEquiv (I : Type u) :
    (I → ℂ) ≃ₗ[ℝ] (I ⊕ I → ℝ) where
  toFun := State.realColumn1
  invFun := State.complexOfRealColumn1
  left_inv := State.complexOfRealColumn1_realColumn1
  right_inv := realColumn1_rightInverse
  map_add' := State.realColumn1Linear.map_add
  map_smul' := State.realColumn1Linear.map_smul

/--
The first column is a bijection between normalized source and target
representatives.  This is not an equivalence of their ordinary ray spaces.
-/
def realColumn0StateEquiv (I : Type u) [Fintype I] :
    State.ComplexState I ≃ State.RealState (I ⊕ I) where
  toFun := State.realColumn0State
  invFun target :=
    ⟨State.complexOfRealColumn0 target.1, by
      have h := State.realTotalWeight_realColumn0
        (State.complexOfRealColumn0 target.1)
      rw [realColumn0_rightInverse target.1] at h
      change State.complexTotalWeight
        (State.complexOfRealColumn0 target.1) = 1
      rw [← h]
      exact target.property⟩
  left_inv source := by
    apply Subtype.ext
    exact State.complexOfRealColumn0_realColumn0 source.1
  right_inv target := by
    apply Subtype.ext
    exact realColumn0_rightInverse target.1

/--
The second column is a bijection between normalized source and target
representatives.  This is not an equivalence of their ordinary ray spaces.
-/
def realColumn1StateEquiv (I : Type u) [Fintype I] :
    State.ComplexState I ≃ State.RealState (I ⊕ I) where
  toFun := State.realColumn1State
  invFun target :=
    ⟨State.complexOfRealColumn1 target.1, by
      have h := State.realTotalWeight_realColumn1
        (State.complexOfRealColumn1 target.1)
      rw [realColumn1_rightInverse target.1] at h
      change State.complexTotalWeight
        (State.complexOfRealColumn1 target.1) = 1
      rw [← h]
      exact target.property⟩
  left_inv source := by
    apply Subtype.ext
    exact State.complexOfRealColumn1_realColumn1 source.1
  right_inv target := by
    apply Subtype.ext
    exact realColumn1_rightInverse target.1

/-! ## Quaternionic columns represented over the complexes -/

/-- The first doubled-complex column reconstructs its quaternionic source exactly. -/
theorem complexColumn0_exactStateEncoding {I : Type u} :
    ExactStateEncoding
      (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
      State.quaternionOfComplexColumn0 :=
  State.quaternionOfComplexColumn0_leftInverse

/-- The second doubled-complex column reconstructs its quaternionic source exactly. -/
theorem complexColumn1_exactStateEncoding {I : Type u} :
    ExactStateEncoding
      (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
      State.quaternionOfComplexColumn1 :=
  State.quaternionOfComplexColumn1_leftInverse

/-- The displayed decoder is also a right inverse to the first complex column. -/
theorem complexColumn0_rightInverse {I : Type u} :
    Function.RightInverse
      (State.quaternionOfComplexColumn0 :
        (I ⊕ I → ℂ) → (I → ℍ[ℝ]))
      State.complexColumn0 := by
  intro target
  funext i
  rcases i with i | i
  · simp [State.complexColumn0, State.quaternionOfComplexColumn0]
  · simp [State.complexColumn0, State.quaternionOfComplexColumn0]

/-- The displayed decoder is also a right inverse to the second complex column. -/
theorem complexColumn1_rightInverse {I : Type u} :
    Function.RightInverse
      (State.quaternionOfComplexColumn1 :
        (I ⊕ I → ℂ) → (I → ℍ[ℝ]))
      State.complexColumn1 := by
  intro target
  funext i
  rcases i with i | i
  · simp [State.complexColumn1, State.quaternionOfComplexColumn1]
  · simp [State.complexColumn1, State.quaternionOfComplexColumn1]

/-- The first doubled-complex representative is exact and preserves total weight. -/
theorem complexColumn0_losslessStateEncoding {I : Type u} [Fintype I] :
    LosslessStateEncoding
      (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
      State.quaternionOfComplexColumn0 State.quaternionTotalWeight
      State.complexTotalWeight :=
  ⟨complexColumn0_exactStateEncoding,
    State.complexTotalWeight_complexColumn0⟩

/-- The second doubled-complex representative is exact and preserves total weight. -/
theorem complexColumn1_losslessStateEncoding {I : Type u} [Fintype I] :
    LosslessStateEncoding
      (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
      State.quaternionOfComplexColumn1 State.quaternionTotalWeight
      State.complexTotalWeight :=
  ⟨complexColumn1_exactStateEncoding,
    State.complexTotalWeight_complexColumn1⟩

/--
The first raw doubled-complex coordinate convention is a real-linear
equivalence, with `quaternionOfComplexColumn0` as its explicit inverse.
-/
def complexColumn0LinearEquiv (I : Type u) :
    (I → ℍ[ℝ]) ≃ₗ[ℝ] (I ⊕ I → ℂ) where
  toFun := State.complexColumn0
  invFun := State.quaternionOfComplexColumn0
  left_inv := State.quaternionOfComplexColumn0_leftInverse
  right_inv := complexColumn0_rightInverse
  map_add' := State.complexColumn0Linear.map_add
  map_smul' := State.complexColumn0Linear.map_smul

/--
The second raw doubled-complex coordinate convention is a real-linear
equivalence, with `quaternionOfComplexColumn1` as its explicit inverse.
-/
def complexColumn1LinearEquiv (I : Type u) :
    (I → ℍ[ℝ]) ≃ₗ[ℝ] (I ⊕ I → ℂ) where
  toFun := State.complexColumn1
  invFun := State.quaternionOfComplexColumn1
  left_inv := State.quaternionOfComplexColumn1_leftInverse
  right_inv := complexColumn1_rightInverse
  map_add' := State.complexColumn1Linear.map_add
  map_smul' := State.complexColumn1Linear.map_smul

/--
The first column is a bijection between normalized source and target
representatives.  This is not an equivalence of their ordinary ray spaces.
-/
def complexColumn0StateEquiv (I : Type u) [Fintype I] :
    State.QuaternionState I ≃ State.ComplexState (I ⊕ I) where
  toFun := State.complexColumn0State
  invFun target :=
    ⟨State.quaternionOfComplexColumn0 target.1, by
      have h := State.complexTotalWeight_complexColumn0
        (State.quaternionOfComplexColumn0 target.1)
      rw [complexColumn0_rightInverse target.1] at h
      change State.quaternionTotalWeight
        (State.quaternionOfComplexColumn0 target.1) = 1
      rw [← h]
      exact target.property⟩
  left_inv source := by
    apply Subtype.ext
    exact State.quaternionOfComplexColumn0_leftInverse source.1
  right_inv target := by
    apply Subtype.ext
    exact complexColumn0_rightInverse target.1

/--
The second column is a bijection between normalized source and target
representatives.  This is not an equivalence of their ordinary ray spaces.
-/
def complexColumn1StateEquiv (I : Type u) [Fintype I] :
    State.QuaternionState I ≃ State.ComplexState (I ⊕ I) where
  toFun := State.complexColumn1State
  invFun target :=
    ⟨State.quaternionOfComplexColumn1 target.1, by
      have h := State.complexTotalWeight_complexColumn1
        (State.quaternionOfComplexColumn1 target.1)
      rw [complexColumn1_rightInverse target.1] at h
      change State.quaternionTotalWeight
        (State.quaternionOfComplexColumn1 target.1) = 1
      rw [← h]
      exact target.property⟩
  left_inv source := by
    apply Subtype.ext
    exact State.quaternionOfComplexColumn1_leftInverse source.1
  right_inv target := by
    apply Subtype.ext
    exact complexColumn1_rightInverse target.1

end QuaternionicComputing.Semantics
