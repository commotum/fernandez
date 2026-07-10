module

public import QuaternionicComputing.Semantics.Measurement
public import QuaternionicComputing.State.RealPhase
public import QuaternionicComputing.State.ComplexPhase
public import QuaternionicComputing.State.Unitary

/-!
# Exact and phase equality for normalized pure states

This leaf gives separate semantic names to literal equality of normalized
state representatives and to the physically relevant real, complex, and
quaternionic ray relations.  Real phase is a sign, complex phase is a unit
complex scalar on the right, and quaternionic phase is a unit quaternion
strictly on the right.

The phase relations preserve computational-basis weights and therefore the
finite measurement distributions of normalized states.  They are also
natural under arbitrary compatible raw matrix action and under the normalized
unitary evolutions from `State.Unitary`.  No relation in this file compares
operators or channels, and no quotient identification is made here.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Normalized-state relations -/

/-- Literal equality of two representatives of the same normalized-state type. -/
def ExactStateEq {R : Type u} {I : Type v} [Fintype I]
    {weight : R → ℝ} (a b : State.NormalizedState I R weight) : Prop :=
  a = b

/-- Real normalized states agree up to a unit sign on the right. -/
def RealStatePhaseEq {I : Type u} [Fintype I]
    (a b : State.RealState I) : Prop :=
  Real.SignEquivalent (a : I → ℝ) b

/-- Complex normalized states agree up to a unit complex phase on the right. -/
def ComplexStatePhaseEq {I : Type u} [Fintype I]
    (a b : State.ComplexState I) : Prop :=
  Complex.RightPhaseEquivalent (a : I → ℂ) b

/-- Quaternionic normalized states agree up to a unit quaternion on the right. -/
def QuaternionStatePhaseEq {I : Type u} [Fintype I]
    (a b : State.QuaternionState I) : Prop :=
  Quaternion.RightPhaseEquivalent (a : I → ℍ[ℝ]) b

/-! ## Exact normalized-state equality -/

namespace ExactStateEq

variable {R : Type u} {I : Type v} [Fintype I] {weight : R → ℝ}
variable {a b c : State.NormalizedState I R weight}

@[refl]
theorem refl (a : State.NormalizedState I R weight) : ExactStateEq a a :=
  rfl

@[symm]
theorem symm (h : ExactStateEq a b) : ExactStateEq b a :=
  Eq.symm h

@[trans]
theorem trans (hab : ExactStateEq a b) (hbc : ExactStateEq b c) :
    ExactStateEq a c :=
  Eq.trans hab hbc

/-- Literal normalized-state equality is an equivalence relation. -/
theorem equivalence :
    Equivalence
      (ExactStateEq : State.NormalizedState I R weight →
        State.NormalizedState I R weight → Prop) :=
  ⟨refl, symm, trans⟩

@[simp]
theorem iff_eq : ExactStateEq a b ↔ a = b :=
  Iff.rfl

theorem of_eq (h : a = b) : ExactStateEq a b :=
  h

theorem eq (h : ExactStateEq a b) : a = b :=
  h

/-- Exactly equal normalized states have identical basis weights. -/
theorem basisWeightEq (h : ExactStateEq a b) :
    BasisWeightEq weight a b := by
  subst b
  exact BasisWeightEq.refl a

/-- Exactly equal normalized states induce the same finite distribution. -/
theorem normalizedDistributionEq (hweight : ∀ z, 0 ≤ weight z)
    (h : ExactStateEq a b) :
    NormalizedDistributionEq weight hweight a b :=
  h.basisWeightEq.normalizedDistributionEq

end ExactStateEq

/-! ## Real sign equality -/

namespace RealStatePhaseEq

variable {I : Type u} [Fintype I]
variable {a b c : State.RealState I}

@[refl]
theorem refl (a : State.RealState I) : RealStatePhaseEq a a :=
  Real.signEquivalent_refl a

@[symm]
theorem symm (h : RealStatePhaseEq a b) : RealStatePhaseEq b a :=
  Real.signEquivalent_symm h

@[trans]
theorem trans (hab : RealStatePhaseEq a b) (hbc : RealStatePhaseEq b c) :
    RealStatePhaseEq a c :=
  Real.signEquivalent_trans hab hbc

/-- Real normalized-state phase equality is an equivalence relation. -/
theorem equivalence :
    Equivalence
      (RealStatePhaseEq : State.RealState I → State.RealState I → Prop) :=
  ⟨refl, symm, trans⟩

/-- Literal equality of normalized real representatives implies sign equality. -/
theorem of_exact (h : ExactStateEq a b) : RealStatePhaseEq a b := by
  subst b
  exact refl a

/-- Construct real state-phase equality from an explicit unit sign. -/
theorem of_sign (s : ℝ) (hs : s * s = 1)
    (h : (a : I → ℝ) = fun i ↦ b i * s) : RealStatePhaseEq a b :=
  ⟨s, hs, h⟩

/-- Applying an explicit unit sign to a normalized real state preserves its ray. -/
theorem rightSign (a : State.RealState I) (s : ℝ) (hs : s * s = 1) :
    RealStatePhaseEq (State.RealState.rightSign a s hs) a :=
  State.RealState.signEquivalent_rightSign a s hs

/-- Real sign equality preserves every computational-basis weight. -/
theorem basisWeightEq (h : RealStatePhaseEq a b) :
    BasisWeightEq State.realWeight a b :=
  fun i ↦ State.signEquivalent_realBasisWeight h i

/-- Real sign equality preserves the normalized finite distribution. -/
theorem normalizedDistributionEq (h : RealStatePhaseEq a b) :
    NormalizedDistributionEq State.realWeight State.realWeight_nonneg a b :=
  h.basisWeightEq.normalizedDistributionEq

/-- Arbitrary compatible real matrix action preserves the underlying sign ray. -/
theorem raw_mulVec {O : Type v} (A : Matrix O I ℝ)
    (h : RealStatePhaseEq a b) :
    Real.SignEquivalent
      (A *ᵥ (a : I → ℝ)) (A *ᵥ (b : I → ℝ)) :=
  State.signEquivalent_real_mulVec A h

/-- Real unitary evolution preserves normalized real state-phase equality. -/
theorem evolveUnitary [DecidableEq I] (U : Matrix I I ℝ)
    (hU : U ∈ unitary (Matrix I I ℝ)) (h : RealStatePhaseEq a b) :
    RealStatePhaseEq
      (State.RealState.evolveUnitary a U hU)
      (State.RealState.evolveUnitary b U hU) :=
  State.signEquivalent_real_mulVec U h

end RealStatePhaseEq

/-! ## Complex right-phase equality -/

namespace ComplexStatePhaseEq

variable {I : Type u} [Fintype I]
variable {a b c : State.ComplexState I}

@[refl]
theorem refl (a : State.ComplexState I) : ComplexStatePhaseEq a a :=
  Complex.rightPhaseEquivalent_refl a

@[symm]
theorem symm (h : ComplexStatePhaseEq a b) : ComplexStatePhaseEq b a :=
  Complex.rightPhaseEquivalent_symm h

@[trans]
theorem trans (hab : ComplexStatePhaseEq a b)
    (hbc : ComplexStatePhaseEq b c) : ComplexStatePhaseEq a c :=
  Complex.rightPhaseEquivalent_trans hab hbc

/-- Complex normalized-state phase equality is an equivalence relation. -/
theorem equivalence :
    Equivalence
      (ComplexStatePhaseEq :
        State.ComplexState I → State.ComplexState I → Prop) :=
  ⟨refl, symm, trans⟩

/-- Literal equality of normalized complex representatives implies phase equality. -/
theorem of_exact (h : ExactStateEq a b) : ComplexStatePhaseEq a b := by
  subst b
  exact refl a

/-- Construct complex state-phase equality from an explicit unit right phase. -/
theorem of_phase (eta : ℂ) (heta : _root_.Complex.normSq eta = 1)
    (h : (a : I → ℂ) = fun i ↦ b i * eta) : ComplexStatePhaseEq a b :=
  ⟨eta, heta, h⟩

/-- Applying an explicit unit complex phase preserves a normalized state's ray. -/
theorem rightPhase (a : State.ComplexState I) (eta : ℂ)
    (heta : _root_.Complex.normSq eta = 1) :
    ComplexStatePhaseEq (State.ComplexState.rightPhase a eta heta) a :=
  State.ComplexState.rightPhaseEquivalent_rightPhase a eta heta

/-- Complex phase equality preserves every computational-basis weight. -/
theorem basisWeightEq (h : ComplexStatePhaseEq a b) :
    BasisWeightEq State.complexWeight a b :=
  fun i ↦ State.rightPhaseEquivalent_complexBasisWeight h i

/-- Complex phase equality preserves the normalized finite distribution. -/
theorem normalizedDistributionEq (h : ComplexStatePhaseEq a b) :
    NormalizedDistributionEq State.complexWeight State.complexWeight_nonneg a b :=
  h.basisWeightEq.normalizedDistributionEq

/-- Arbitrary compatible complex matrix action preserves the underlying phase ray. -/
theorem raw_mulVec {O : Type v} (A : Matrix O I ℂ)
    (h : ComplexStatePhaseEq a b) :
    Complex.RightPhaseEquivalent
      (A *ᵥ (a : I → ℂ)) (A *ᵥ (b : I → ℂ)) :=
  State.rightPhaseEquivalent_complex_mulVec A h

/-- Complex unitary evolution preserves normalized complex state-phase equality. -/
theorem evolveUnitary [DecidableEq I] (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (h : ComplexStatePhaseEq a b) :
    ComplexStatePhaseEq
      (State.ComplexState.evolveUnitary a U hU)
      (State.ComplexState.evolveUnitary b U hU) :=
  State.rightPhaseEquivalent_complex_mulVec U h

end ComplexStatePhaseEq

/-! ## Quaternionic right-phase equality -/

namespace QuaternionStatePhaseEq

variable {I : Type u} [Fintype I]
variable {a b c : State.QuaternionState I}

@[refl]
theorem refl (a : State.QuaternionState I) : QuaternionStatePhaseEq a a :=
  Quaternion.rightPhaseEquivalent_refl a

@[symm]
theorem symm (h : QuaternionStatePhaseEq a b) :
    QuaternionStatePhaseEq b a :=
  Quaternion.rightPhaseEquivalent_symm h

@[trans]
theorem trans (hab : QuaternionStatePhaseEq a b)
    (hbc : QuaternionStatePhaseEq b c) : QuaternionStatePhaseEq a c :=
  Quaternion.rightPhaseEquivalent_trans hab hbc

/-- Quaternionic normalized-state right-phase equality is an equivalence relation. -/
theorem equivalence :
    Equivalence
      (QuaternionStatePhaseEq :
        State.QuaternionState I → State.QuaternionState I → Prop) :=
  ⟨refl, symm, trans⟩

/-- Literal equality of quaternionic representatives implies right-phase equality. -/
theorem of_exact (h : ExactStateEq a b) : QuaternionStatePhaseEq a b := by
  subst b
  exact refl a

/-- Construct quaternionic state-phase equality from an explicit unit right phase. -/
theorem of_phase (eta : ℍ[ℝ])
    (heta : _root_.Quaternion.normSq eta = 1)
    (h : (a : I → ℍ[ℝ]) = fun i ↦ b i * eta) :
    QuaternionStatePhaseEq a b :=
  ⟨eta, heta, h⟩

/-- Applying an explicit unit quaternion on the right preserves a normalized ray. -/
theorem rightPhase (a : State.QuaternionState I) (eta : ℍ[ℝ])
    (heta : _root_.Quaternion.normSq eta = 1) :
    QuaternionStatePhaseEq (State.QuaternionState.rightPhase a eta heta) a :=
  State.QuaternionState.rightPhaseEquivalent_rightPhase a eta heta

/-- Quaternionic right-phase equality preserves every basis weight. -/
theorem basisWeightEq (h : QuaternionStatePhaseEq a b) :
    BasisWeightEq State.quaternionWeight a b :=
  fun i ↦ State.rightPhaseEquivalent_quaternionBasisWeight h i

/-- Quaternionic right-phase equality preserves the normalized distribution. -/
theorem normalizedDistributionEq (h : QuaternionStatePhaseEq a b) :
    NormalizedDistributionEq State.quaternionWeight
      State.quaternionWeight_nonneg a b :=
  h.basisWeightEq.normalizedDistributionEq

/-- Arbitrary compatible quaternionic matrix action preserves the right phase. -/
theorem raw_mulVec {O : Type v} (A : Matrix O I ℍ[ℝ])
    (h : QuaternionStatePhaseEq a b) :
    Quaternion.RightPhaseEquivalent
      (A *ᵥ (a : I → ℍ[ℝ])) (A *ᵥ (b : I → ℍ[ℝ])) :=
  State.rightPhaseEquivalent_mulVec A h

/-- Quaternionic unitary evolution preserves normalized right-phase equality. -/
theorem evolveUnitary [DecidableEq I] (U : Matrix I I ℍ[ℝ])
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ]))
    (h : QuaternionStatePhaseEq a b) :
    QuaternionStatePhaseEq
      (State.QuaternionState.evolveUnitary a U hU)
      (State.QuaternionState.evolveUnitary b U hU) :=
  State.rightPhaseEquivalent_mulVec U h

end QuaternionStatePhaseEq

end QuaternionicComputing.Semantics
