module

public import QuaternionicComputing.Semantics.Core
public import QuaternionicComputing.State.Distribution

/-!
# Computational-basis semantic comparisons

This leaf separates comparison at one supplied input, all computational-basis
inputs, all normalized pure inputs, and packaged finite distributions. These
relations concern computational-basis weights only; they are not channel or
all-effect equality.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe u v w

/-- Two columns assign the same computational-basis weight at every output. -/
def BasisWeightEq {A : Type u} {O : Type v}
    (weight : A → ℝ) (a b : O → A) : Prop :=
  ∀ y, State.basisWeight weight a y = State.basisWeight weight b y

namespace BasisWeightEq

variable {A : Type u} {O : Type v} {weight : A → ℝ}
variable {a b c : O → A}

@[refl]
theorem refl (a : O → A) : BasisWeightEq weight a a :=
  fun _ ↦ rfl

@[symm]
theorem symm (h : BasisWeightEq weight a b) : BasisWeightEq weight b a :=
  fun y ↦ (h y).symm

@[trans]
theorem trans (hab : BasisWeightEq weight a b)
    (hbc : BasisWeightEq weight b c) :
    BasisWeightEq weight a c :=
  fun y ↦ (hab y).trans (hbc y)

theorem equivalence :
    Equivalence (BasisWeightEq weight : (O → A) → (O → A) → Prop) :=
  ⟨refl, symm, trans⟩

theorem of_eq (h : a = b) : BasisWeightEq weight a b := by
  subst b
  exact refl a

end BasisWeightEq

/-- Output-weight agreement for one explicitly supplied input column. -/
def OutputWeightEqAt {R : Type u} {O : Type v} {I : Type w}
    [Fintype I] [NonUnitalNonAssocSemiring R]
    (weight : R → ℝ) (U V : Matrix O I R) (input : I → R) : Prop :=
  BasisWeightEq weight (U *ᵥ input) (V *ᵥ input)

namespace OutputWeightEqAt

variable {R : Type u} {O : Type v} {I : Type w}
variable [Fintype I] [NonUnitalNonAssocSemiring R]
variable {weight : R → ℝ} {U V T : Matrix O I R} {input : I → R}

theorem refl (U : Matrix O I R) : OutputWeightEqAt weight U U input :=
  BasisWeightEq.refl _

@[symm]
theorem symm (h : OutputWeightEqAt weight U V input) :
    OutputWeightEqAt weight V U input :=
  BasisWeightEq.symm h

@[trans]
theorem trans (hUV : OutputWeightEqAt weight U V input)
    (hVT : OutputWeightEqAt weight V T input) :
    OutputWeightEqAt weight U T input :=
  BasisWeightEq.trans hUV hVT

theorem equivalence :
    Equivalence (fun U V : Matrix O I R ↦
      OutputWeightEqAt weight U V input) :=
  ⟨refl, symm, trans⟩

theorem of_exact (h : ExactOperatorEq U V) :
    OutputWeightEqAt weight U V input := by
  subst V
  exact refl U

end OutputWeightEqAt

/-- Agreement of all computational-basis transition weights. -/
def BasisMeasurementEq {R : Type u} {O : Type v} {I : Type w}
    (weight : R → ℝ) (U V : Matrix O I R) : Prop :=
  ∀ x y, weight (U y x) = weight (V y x)

namespace BasisMeasurementEq

variable {R : Type u} {O : Type v} {I : Type w}
variable {weight : R → ℝ} {U V T : Matrix O I R}

@[refl]
theorem refl (U : Matrix O I R) : BasisMeasurementEq weight U U :=
  fun _ _ ↦ rfl

@[symm]
theorem symm (h : BasisMeasurementEq weight U V) :
    BasisMeasurementEq weight V U :=
  fun x y ↦ (h x y).symm

@[trans]
theorem trans (hUV : BasisMeasurementEq weight U V)
    (hVT : BasisMeasurementEq weight V T) :
    BasisMeasurementEq weight U T :=
  fun x y ↦ (hUV x y).trans (hVT x y)

theorem equivalence :
    Equivalence
      (BasisMeasurementEq weight : Matrix O I R → Matrix O I R → Prop) :=
  ⟨refl, symm, trans⟩

theorem of_exact (h : ExactOperatorEq U V) :
    BasisMeasurementEq weight U V := by
  subst V
  exact refl U

end BasisMeasurementEq

/-- Basis measurement is exactly fixed-input output agreement on every basis ket. -/
theorem basisMeasurementEq_iff_outputWeightEqAt_basis
    {R : Type u} {O : Type v} {I : Type w}
    [Fintype I] [DecidableEq I] [NonAssocSemiring R]
    (weight : R → ℝ) (U V : Matrix O I R) :
    BasisMeasurementEq weight U V ↔
      ∀ x, OutputWeightEqAt weight U V (Pi.single x 1) := by
  simp only [BasisMeasurementEq, OutputWeightEqAt, BasisWeightEq,
    State.basisWeight, Matrix.mulVec_single_one, Matrix.col_apply]

/-- Fixed-input agreement on one basis ket is equality of the corresponding column weights. -/
theorem outputWeightEqAt_basis_iff_column_weight
    {R : Type u} {O : Type v} {I : Type w}
    [Fintype I] [DecidableEq I] [NonAssocSemiring R]
    (weight : R → ℝ) (U V : Matrix O I R) (x : I) :
    OutputWeightEqAt weight U V (Pi.single x 1) ↔
      ∀ y, weight (U y x) = weight (V y x) := by
  simp [OutputWeightEqAt, BasisWeightEq, State.basisWeight]

/-- Agreement of basis-output weights for every normalized pure input state. -/
def PureInputBasisMeasurementEq {R : Type u} {O : Type v} {I : Type w}
    [Fintype I] [NonUnitalNonAssocSemiring R]
    (weight : R → ℝ) (U V : Matrix O I R) : Prop :=
  ∀ input : State.NormalizedState I R weight,
    OutputWeightEqAt weight U V input

namespace PureInputBasisMeasurementEq

variable {R : Type u} {O : Type v} {I : Type w}
variable [Fintype I] [NonUnitalNonAssocSemiring R]
variable {weight : R → ℝ} {U V T : Matrix O I R}

@[refl]
theorem refl (U : Matrix O I R) :
    PureInputBasisMeasurementEq weight U U :=
  fun _ ↦ OutputWeightEqAt.refl U

@[symm]
theorem symm (h : PureInputBasisMeasurementEq weight U V) :
    PureInputBasisMeasurementEq weight V U :=
  fun input ↦ (h input).symm

@[trans]
theorem trans (hUV : PureInputBasisMeasurementEq weight U V)
    (hVT : PureInputBasisMeasurementEq weight V T) :
    PureInputBasisMeasurementEq weight U T :=
  fun input ↦ (hUV input).trans (hVT input)

theorem equivalence :
    Equivalence
      (PureInputBasisMeasurementEq weight :
        Matrix O I R → Matrix O I R → Prop) :=
  ⟨refl, symm, trans⟩

theorem of_exact (h : ExactOperatorEq U V) :
    PureInputBasisMeasurementEq weight U V :=
  fun _ ↦ OutputWeightEqAt.of_exact h

end PureInputBasisMeasurementEq

/--
All-normalized-pure-input agreement implies all-basis-input agreement when
every basis ket is normalized for the explicitly supplied weight.
-/
theorem PureInputBasisMeasurementEq.basisMeasurementEq
    {R : Type u} {O : Type v} {I : Type w}
    [Fintype I] [DecidableEq I] [NonAssocSemiring R]
    {weight : R → ℝ} {U V : Matrix O I R}
    (h : PureInputBasisMeasurementEq weight U V)
    (hbasis : ∀ x : I, State.totalWeight weight (Pi.single x 1) = 1) :
    BasisMeasurementEq weight U V := by
  rw [basisMeasurementEq_iff_outputWeightEqAt_basis]
  intro x
  simpa using h ⟨Pi.single x 1, hbasis x⟩

/-- Equality of the finite distributions induced by two normalized states. -/
def NormalizedDistributionEq {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) : Prop :=
  State.FiniteDistribution.ofNormalizedState weight hweight a =
    State.FiniteDistribution.ofNormalizedState weight hweight b

namespace NormalizedDistributionEq

variable {R : Type u} {I : Type v} [Fintype I]
variable {weight : R → ℝ} {hweight : ∀ z, 0 ≤ weight z}
variable {a b c : State.NormalizedState I R weight}

@[refl]
theorem refl (a : State.NormalizedState I R weight) :
    NormalizedDistributionEq weight hweight a a :=
  rfl

@[symm]
theorem symm (h : NormalizedDistributionEq weight hweight a b) :
    NormalizedDistributionEq weight hweight b a :=
  Eq.symm h

@[trans]
theorem trans (hab : NormalizedDistributionEq weight hweight a b)
    (hbc : NormalizedDistributionEq weight hweight b c) :
    NormalizedDistributionEq weight hweight a c :=
  Eq.trans hab hbc

theorem equivalence :
    Equivalence
      (NormalizedDistributionEq weight hweight :
        State.NormalizedState I R weight →
          State.NormalizedState I R weight → Prop) :=
  ⟨refl, symm, trans⟩

theorem eventWeight_eq (h : NormalizedDistributionEq weight hweight a b)
    (event : Finset I) :
    (State.FiniteDistribution.ofNormalizedState weight hweight a).eventWeight
        event =
      (State.FiniteDistribution.ofNormalizedState weight hweight b).eventWeight
        event := by
  rw [h]

theorem pushforward_eq {J : Type w} [Fintype J]
    (h : NormalizedDistributionEq weight hweight a b) (f : I → J) :
    (State.FiniteDistribution.ofNormalizedState weight hweight a).pushforward f =
      (State.FiniteDistribution.ofNormalizedState weight hweight b).pushforward f := by
  rw [h]

end NormalizedDistributionEq

/-- Pointwise normalized-state weights agree iff their packaged distributions agree. -/
theorem basisWeightEq_iff_normalizedDistributionEq
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    BasisWeightEq weight a b ↔ NormalizedDistributionEq weight hweight a b := by
  constructor
  · intro h
    apply State.FiniteDistribution.ext
    exact h
  · intro h y
    exact congrArg (fun μ : State.FiniteDistribution I ↦ μ.weight y) h

namespace BasisWeightEq

variable {R : Type u} {I : Type v} [Fintype I]
variable {weight : R → ℝ} {hweight : ∀ z, 0 ≤ weight z}
variable {a b : State.NormalizedState I R weight}

theorem normalizedDistributionEq (h : BasisWeightEq weight a b) :
    NormalizedDistributionEq weight hweight a b :=
  (basisWeightEq_iff_normalizedDistributionEq weight hweight a b).mp h

theorem eventWeight_eq (h : BasisWeightEq weight a b) (event : Finset I) :
    (State.FiniteDistribution.ofNormalizedState weight hweight a).eventWeight
        event =
      (State.FiniteDistribution.ofNormalizedState weight hweight b).eventWeight
        event := by
  apply State.FiniteDistribution.eventWeight_eq_of_weight_eq
  exact h

theorem pushforward_eq {J : Type w} [Fintype J]
    (h : BasisWeightEq weight a b) (f : I → J) :
    (State.FiniteDistribution.ofNormalizedState weight hweight a).pushforward f =
      (State.FiniteDistribution.ofNormalizedState weight hweight b).pushforward f := by
  apply State.FiniteDistribution.pushforward_eq_of_weight_eq
  exact h

theorem pushforward_weight_eq {J : Type w} [Fintype J]
    (h : BasisWeightEq weight a b) (f : I → J) (y : J) :
    ((State.FiniteDistribution.ofNormalizedState weight hweight a).pushforward f).weight y =
      ((State.FiniteDistribution.ofNormalizedState weight hweight b).pushforward f).weight y := by
  exact congrArg (fun μ : State.FiniteDistribution J ↦ μ.weight y)
    (pushforward_eq h f)

end BasisWeightEq

namespace ExactCircuitEq

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]
variable {weight : R → ℝ} {C D : Circuit.OrderedCircuit R W}

theorem outputWeightEqAt (h : ExactCircuitEq C D)
    (input : Circuit.BitBasis W → R) :
    OutputWeightEqAt weight (Circuit.OrderedCircuit.eval C)
      (Circuit.OrderedCircuit.eval D) input :=
  OutputWeightEqAt.of_exact h

theorem basisMeasurementEq (h : ExactCircuitEq C D) :
    BasisMeasurementEq weight (Circuit.OrderedCircuit.eval C)
      (Circuit.OrderedCircuit.eval D) :=
  BasisMeasurementEq.of_exact h

theorem pureInputBasisMeasurementEq (h : ExactCircuitEq C D) :
    PureInputBasisMeasurementEq weight (Circuit.OrderedCircuit.eval C)
      (Circuit.OrderedCircuit.eval D) :=
  PureInputBasisMeasurementEq.of_exact h

end ExactCircuitEq

end QuaternionicComputing.Semantics
