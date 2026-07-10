module

public import QuaternionicComputing.State.Basic

/-!
# Finite probability distributions

This file packages nonnegative real weights of total mass one on a finite
type.  It is independent of the scalar field used by an amplitude state:
`ofNormalizedState` consumes only the generic computational-basis weights and
their nonnegativity proof.

`pushforward` implements deterministic finite classical postprocessing by
summing over fibers.  It carries no computability, runtime, randomized, or
finite-precision claim.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.State

universe u v w

/-- Nonnegative real weights of total mass one on a finite type. -/
structure FiniteDistribution (α : Type u) [Fintype α] where
  /-- Weight assigned to a single outcome. -/
  weight : α → ℝ
  /-- Every outcome weight is nonnegative. -/
  nonnegative : ∀ x, 0 ≤ weight x
  /-- The weights have total mass one. -/
  normalized : (∑ x, weight x) = 1

namespace FiniteDistribution

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [Fintype β]

/-- Two finite distributions are equal when all their outcome weights agree. -/
@[ext]
theorem ext {μ ν : FiniteDistribution α}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk μ hμ hμsum =>
    cases ν with
    | mk ν hν hνsum =>
      have hweight : μ = ν := funext h
      subst ν
      rfl

/-- The defining total-mass equation of a finite distribution. -/
@[simp]
theorem sum_weight (μ : FiniteDistribution α) :
    (∑ x, μ.weight x) = 1 :=
  μ.normalized

/--
Turn the computational-basis weights of a generic normalized state into a
finite distribution.
-/
def ofNormalizedState (scalarWeight : γ → ℝ)
    (hscalarWeight : ∀ z, 0 ≤ scalarWeight z)
    (ψ : NormalizedState α γ scalarWeight) : FiniteDistribution α where
  weight x := basisWeight scalarWeight ψ x
  nonnegative x := ψ.basisWeight_nonneg hscalarWeight x
  normalized := ψ.sum_basisWeight

@[simp]
theorem ofNormalizedState_weight (scalarWeight : γ → ℝ)
    (hscalarWeight : ∀ z, 0 ≤ scalarWeight z)
    (ψ : NormalizedState α γ scalarWeight) (x : α) :
    (ofNormalizedState scalarWeight hscalarWeight ψ).weight x =
      basisWeight scalarWeight ψ x :=
  rfl

/-- Total weight assigned to a finite event. -/
def eventWeight (μ : FiniteDistribution α) (event : Finset α) : ℝ :=
  ∑ x ∈ event, μ.weight x

/-- Every finite event has nonnegative weight. -/
theorem eventWeight_nonnegative (μ : FiniteDistribution α)
    (event : Finset α) :
    0 ≤ μ.eventWeight event := by
  exact Finset.sum_nonneg fun x _ ↦ μ.nonnegative x

@[simp]
theorem eventWeight_empty (μ : FiniteDistribution α) :
    μ.eventWeight ∅ = 0 := by
  simp [eventWeight]

@[simp]
theorem eventWeight_univ (μ : FiniteDistribution α) :
    μ.eventWeight Finset.univ = 1 := by
  simp [eventWeight]

/-- Pointwise-equal outcome weights give equal weights to every finite event. -/
theorem eventWeight_eq_of_weight_eq {μ ν : FiniteDistribution α}
    (h : ∀ x, μ.weight x = ν.weight x) (event : Finset α) :
    μ.eventWeight event = ν.eventWeight event := by
  apply Finset.sum_congr rfl
  intro x _
  exact h x

/--
Push a finite distribution through a deterministic map by summing the weights
of every source fiber.
-/
def pushforward (μ : FiniteDistribution α) (f : α → β) :
    FiniteDistribution β := by
  classical
  exact
    { weight := fun y ↦ ∑ x with f x = y, μ.weight x
      nonnegative := fun _ ↦ Finset.sum_nonneg fun x _ ↦ μ.nonnegative x
      normalized := by
        calc
          (∑ y, ∑ x with f x = y, μ.weight x) = ∑ x, μ.weight x :=
            Finset.sum_fiberwise Finset.univ f μ.weight
          _ = 1 := μ.sum_weight }

open scoped Classical in
@[simp]
theorem pushforward_weight (μ : FiniteDistribution α) (f : α → β) (y : β) :
    (μ.pushforward f).weight y = ∑ x with f x = y, μ.weight x := by
  rfl

/-- Every weight of a deterministic pushforward is nonnegative. -/
theorem pushforward_weight_nonnegative (μ : FiniteDistribution α)
    (f : α → β) (y : β) :
    0 ≤ (μ.pushforward f).weight y :=
  (μ.pushforward f).nonnegative y

/-- A deterministic pushforward still has total mass one. -/
@[simp]
theorem sum_pushforward_weight (μ : FiniteDistribution α) (f : α → β) :
    (∑ y, (μ.pushforward f).weight y) = 1 :=
  (μ.pushforward f).normalized

/-- Pointwise-equal source weights give equal weights after deterministic pushforward. -/
theorem pushforward_weight_eq_of_weight_eq {μ ν : FiniteDistribution α}
    (h : ∀ x, μ.weight x = ν.weight x) (f : α → β) (y : β) :
    (μ.pushforward f).weight y = (ν.pushforward f).weight y := by
  classical
  simp only [pushforward_weight]
  apply Finset.sum_congr rfl
  intro x _
  exact h x

/-- Pointwise-equal source weights give equal deterministic pushforwards. -/
theorem pushforward_eq_of_weight_eq {μ ν : FiniteDistribution α}
    (h : ∀ x, μ.weight x = ν.weight x) (f : α → β) :
    μ.pushforward f = ν.pushforward f := by
  apply ext
  exact pushforward_weight_eq_of_weight_eq h f

/-- Equal source distributions remain equal after every deterministic map. -/
theorem pushforward_eq_of_eq {μ ν : FiniteDistribution α}
    (h : μ = ν) (f : α → β) :
    μ.pushforward f = ν.pushforward f := by
  subst ν
  rfl

end FiniteDistribution

end QuaternionicComputing.State
