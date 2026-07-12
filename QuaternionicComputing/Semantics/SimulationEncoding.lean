module

public import QuaternionicComputing.Semantics.Simulation
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification

/-!
# Exact representative encodings used by cross-model simulations

This leaf certifies the two canonical complex-to-doubled-real state columns
and the two canonical quaternion-to-doubled-complex state columns as exact,
total-weight-preserving directional encodings.  It also packages their
normalized-state maps as `Function.Embedding` values.

These maps change both scalar and index type.  They are injective
representative embeddings, not surjections onto the target state spaces and
not same-space state equalities.  Nothing here asserts descent to ordinary
target rays, a top-sector marginal, a mixed-state encoding, channel equality,
or all-measurement agreement.  Orthogonality of the paired columns remains in
the underlying state modules and is not duplicated here.
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
The first normalized doubled-real representative is an injective function.
This value records no surjectivity or ordinary-real-ray claim.
-/
def realColumn0StateEmbedding (I : Type u) [Fintype I] :
    State.ComplexState I ↪ State.RealState (I ⊕ I) where
  toFun := State.realColumn0State
  inj' a b h := by
    apply Subtype.ext
    apply State.realColumn0_injective
    exact congrArg Subtype.val h

/--
The second normalized doubled-real representative is an injective function.
This value records no surjectivity or ordinary-real-ray claim.
-/
def realColumn1StateEmbedding (I : Type u) [Fintype I] :
    State.ComplexState I ↪ State.RealState (I ⊕ I) where
  toFun := State.realColumn1State
  inj' a b h := by
    apply Subtype.ext
    apply State.realColumn1_injective
    exact congrArg Subtype.val h

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
The first normalized doubled-complex representative is an injective function.
This value records no surjectivity or complex-ray claim.
-/
def complexColumn0StateEmbedding (I : Type u) [Fintype I] :
    State.QuaternionState I ↪ State.ComplexState (I ⊕ I) where
  toFun := State.complexColumn0State
  inj' a b h := by
    apply Subtype.ext
    apply State.complexColumn0_injective
    exact congrArg Subtype.val h

/--
The second normalized doubled-complex representative is an injective function.
This value records no surjectivity or complex-ray claim.
-/
def complexColumn1StateEmbedding (I : Type u) [Fintype I] :
    State.QuaternionState I ↪ State.ComplexState (I ⊕ I) where
  toFun := State.complexColumn1State
  inj' a b h := by
    apply Subtype.ext
    apply State.complexColumn1_injective
    exact congrArg Subtype.val h

end QuaternionicComputing.Semantics
