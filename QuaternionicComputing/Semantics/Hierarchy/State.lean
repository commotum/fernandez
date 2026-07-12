module

import QuaternionicComputing.State.DistributionLaws
public import QuaternionicComputing.Semantics.Ray

/-!
# State and finite-outcome semantic hierarchy

This leaf packages the missing converse arrows in the finite-outcome state
hierarchy.  Equality of finite distributions is characterized both by all
finite-event weights and by all deterministic pushforwards whose finite target
type lives in the same universe as the source.  The event converse uses
singleton events; the pushforward converse uses the identity map.

The universe restriction in the all-pushforward theorem is only what makes the
identity target available inside one Lean statement.  Forward preservation by
a particular deterministic map remains universe-polymorphic in
`FiniteDistribution.pushforward_eq_of_eq`.

None of the results requires a `Nonempty` hypothesis.  Thus their signatures
cover empty and singleton finite types uniformly (although no probability
distribution, and no normalized state, can inhabit an empty outcome type).
The state wrappers reuse `BasisWeightEq`, `NormalizedDistributionEq`, and the
existing scalar-correct ray quotients; no new comparison relation is defined.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.State.FiniteDistribution

universe u

variable {α : Type u} [Fintype α]
variable {μ ν : FiniteDistribution α}

/--
Two finite distributions are equal exactly when all singleton-event weights
agree.  This statement has no nonemptiness premise, so it also gives the
correct vacuous boundary on an empty outcome type.
-/
theorem eq_iff_singletonEventWeight_eq :
    μ = ν ↔ ∀ x : α, μ.eventWeight {x} = ν.eventWeight {x} := by
  classical
  constructor
  · intro h x
    subst ν
    rfl
  · intro h
    apply ext
    intro x
    simpa [eventWeight] using h x

/--
Two finite distributions are equal exactly when every finite event has the
same weight.  Singleton events prove the converse; the empty event alone, of
course, carries no distinguishing information.
-/
theorem eq_iff_eventWeight_eq :
    μ = ν ↔ ∀ event : Finset α, μ.eventWeight event = ν.eventWeight event := by
  classical
  constructor
  · intro h event
    subst ν
    rfl
  · intro h
    rw [eq_iff_singletonEventWeight_eq]
    exact fun x ↦ h {x}

/--
Two finite distributions are equal exactly when all of their deterministic
pushforwards to finite target types in the source universe are equal.  The
identity map supplies the converse.  In particular, this theorem does not say
that pushforwards to one fixed smaller codomain suffice.
-/
theorem eq_iff_allPushforward_eq_sameUniverse :
    μ = ν ↔
      ∀ (β : Type u) (_ : Fintype β) (f : α → β),
        @pushforward α β _ _ μ f = @pushforward α β _ _ ν f := by
  constructor
  · intro h β inst f
    subst ν
    rfl
  · intro h
    have hid := h α (inferInstance : Fintype α) id
    simpa using hid

end QuaternionicComputing.State.FiniteDistribution

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Normalized-state measurement characterizations -/

/--
Packaged normalized-state distributions agree exactly when all finite-event
weights agree.
-/
theorem normalizedDistributionEq_iff_eventWeight_eq
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    NormalizedDistributionEq weight hweight a b ↔
      ∀ event : Finset I,
        (State.FiniteDistribution.ofNormalizedState weight hweight a).eventWeight
            event =
          (State.FiniteDistribution.ofNormalizedState weight hweight b).eventWeight
            event :=
  State.FiniteDistribution.eq_iff_eventWeight_eq

/--
Packaged normalized-state distributions agree exactly when all deterministic
pushforwards to finite target types in the outcome universe agree.  The
converse specializes to the identity postprocessing on `I`.
-/
theorem normalizedDistributionEq_iff_allPushforward_eq_sameUniverse
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    NormalizedDistributionEq weight hweight a b ↔
      ∀ (J : Type v) (_ : Fintype J) (f : I → J),
        @State.FiniteDistribution.pushforward I J _ _
            (State.FiniteDistribution.ofNormalizedState weight hweight a) f =
          @State.FiniteDistribution.pushforward I J _ _
            (State.FiniteDistribution.ofNormalizedState weight hweight b) f :=
  State.FiniteDistribution.eq_iff_allPushforward_eq_sameUniverse

/--
Pointwise basis-weight agreement is equivalent to agreement on every finite
event of the induced normalized distributions.
-/
theorem basisWeightEq_iff_eventWeight_eq
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    BasisWeightEq weight a b ↔
      ∀ event : Finset I,
        (State.FiniteDistribution.ofNormalizedState weight hweight a).eventWeight
            event =
          (State.FiniteDistribution.ofNormalizedState weight hweight b).eventWeight
            event :=
  (basisWeightEq_iff_normalizedDistributionEq weight hweight a b).trans
    (normalizedDistributionEq_iff_eventWeight_eq weight hweight a b)

/--
Pointwise basis-weight agreement is equivalent to agreement of every
deterministic pushforward whose finite target lies in the outcome universe.
-/
theorem basisWeightEq_iff_allPushforward_eq_sameUniverse
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    BasisWeightEq weight a b ↔
      ∀ (J : Type v) (_ : Fintype J) (f : I → J),
        @State.FiniteDistribution.pushforward I J _ _
            (State.FiniteDistribution.ofNormalizedState weight hweight a) f =
          @State.FiniteDistribution.pushforward I J _ _
            (State.FiniteDistribution.ofNormalizedState weight hweight b) f :=
  (basisWeightEq_iff_normalizedDistributionEq weight hweight a b).trans
    (normalizedDistributionEq_iff_allPushforward_eq_sameUniverse
      weight hweight a b)

/-! ## Exact representatives, rays, and basis weights -/

namespace ExactStateEq

/-- Exact real-state representative equality implies equality of real rays. -/
theorem realRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.RealState I} (h : ExactStateEq a b) :
    State.RealRay.mk a = State.RealRay.mk b :=
  RealStatePhaseEq.iff_realRay_mk_eq.mp (RealStatePhaseEq.of_exact h)

/-- Exact complex-state representative equality implies equality of complex rays. -/
theorem complexRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.ComplexState I} (h : ExactStateEq a b) :
    State.ComplexRay.mk a = State.ComplexRay.mk b :=
  ComplexStatePhaseEq.iff_complexRay_mk_eq.mp (ComplexStatePhaseEq.of_exact h)

/--
Exact quaternionic-state representative equality implies equality of
right-phase quaternionic rays.
-/
theorem quaternionRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.QuaternionState I} (h : ExactStateEq a b) :
    State.QuaternionRay.mk a = State.QuaternionRay.mk b :=
  QuaternionStatePhaseEq.iff_quaternionRay_mk_eq.mp
    (QuaternionStatePhaseEq.of_exact h)

end ExactStateEq

namespace RealStatePhaseEq

/-- Equal real-ray constructors have identical computational-basis weights. -/
theorem basisWeightEq_of_realRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.RealState I} (h : State.RealRay.mk a = State.RealRay.mk b) :
    BasisWeightEq State.realWeight a b :=
  basisWeightEq (iff_realRay_mk_eq.mpr h)

end RealStatePhaseEq

namespace ComplexStatePhaseEq

/-- Equal complex-ray constructors have identical computational-basis weights. -/
theorem basisWeightEq_of_complexRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.ComplexState I}
    (h : State.ComplexRay.mk a = State.ComplexRay.mk b) :
    BasisWeightEq State.complexWeight a b :=
  basisWeightEq (iff_complexRay_mk_eq.mpr h)

end ComplexStatePhaseEq

namespace QuaternionStatePhaseEq

/--
Equal quaternionic-ray constructors have identical computational-basis
weights; the quotient relation used here is right phase.
-/
theorem basisWeightEq_of_quaternionRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.QuaternionState I}
    (h : State.QuaternionRay.mk a = State.QuaternionRay.mk b) :
    BasisWeightEq State.quaternionWeight a b :=
  basisWeightEq (iff_quaternionRay_mk_eq.mpr h)

end QuaternionStatePhaseEq

end QuaternionicComputing.Semantics
