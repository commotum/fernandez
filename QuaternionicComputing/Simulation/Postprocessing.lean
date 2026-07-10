module

public import QuaternionicComputing.State.Distribution
public import QuaternionicComputing.Simulation.ComplexToReal
public import QuaternionicComputing.Simulation.QuaternionToComplex

/-!
# Finite events and deterministic postprocessing of simulated outcomes

The primary simulation theorems identify each normalized bottom
computational-basis weight.  This file packages those weights as finite
distributions and closes the result under arbitrary finite events and
deterministic classical maps.

This is the precise finite semantic content of the paper's claim that the same
classical postprocessing can be reused.  It carries no Turing-machine,
computability, runtime, randomized-postprocessing, or finite-precision claim.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe u v

/-! ## Generic bottom distribution of one normalized added-wire state -/

/--
Aggregate a normalized added-wire state's false/true top assignments into a
normalized distribution on bottom basis assignments.
-/
def addedWireBottomDistribution {R : Type u} {W : Type v} [Finite W]
    {weight : R → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    (v : NormalizedState (BitBasis (AddedWire W)) R weight) :
    FiniteDistribution (BitBasis W) where
  weight := addedWireBottomWeight weight v
  nonnegative := addedWireBottomWeight_normalized_nonneg hweight v
  normalized := sum_addedWireBottomWeight_normalized v

@[simp]
theorem addedWireBottomDistribution_weight
    {R : Type u} {W : Type v} [Finite W]
    {weight : R → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    (v : NormalizedState (BitBasis (AddedWire W)) R weight)
    (x : BitBasis W) :
    (addedWireBottomDistribution hweight v).weight x =
      addedWireBottomWeight weight v x :=
  rfl

/-! ## Complex-to-real output distributions -/

/-- Normalized source output distribution of a complex circuit. -/
def complexCircuitOutputDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (psi : ComplexState (BitBasis W)) : FiniteDistribution (BitBasis W) :=
  FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg
    (complexCircuitOutput c hc psi)

/-- Normalized bottom distribution of the realified circuit output. -/
def realifyCircuitBottomDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    FiniteDistribution (BitBasis W) :=
  addedWireBottomDistribution realWeight_nonneg
    (realifyCircuitOutput c hc top psi)

/-- The two normalized complex-to-real output distributions are exactly equal. -/
theorem realifyCircuitBottomDistribution_eq {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    realifyCircuitBottomDistribution c hc top psi =
      complexCircuitOutputDistribution c hc psi := by
  apply FiniteDistribution.ext
  intro x
  exact realifyCircuitOutput_bottomProbability c hc top psi x

/-- Every finite bottom event has the same probability after realification. -/
theorem realifyCircuitOutput_eventWeight {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (realifyCircuitBottomDistribution c hc top psi).eventWeight event =
      (complexCircuitOutputDistribution c hc psi).eventWeight event := by
  rw [realifyCircuitBottomDistribution_eq]

/-- Every deterministic finite postprocessing has the same output distribution. -/
theorem realifyCircuitOutput_pushforward_eq
    {W : Type v} [Fintype W] {β : Type u} [Fintype β]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W))
    (postprocess : BitBasis W → β) :
    (realifyCircuitBottomDistribution c hc top psi).pushforward postprocess =
      (complexCircuitOutputDistribution c hc psi).pushforward postprocess := by
  rw [realifyCircuitBottomDistribution_eq]

/-! ## Quaternion-to-complex output distributions -/

/-- Normalized source output distribution of a quaternionic circuit. -/
def quaternionCircuitOutputDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (psi : QuaternionState (BitBasis W)) : FiniteDistribution (BitBasis W) :=
  FiniteDistribution.ofNormalizedState quaternionWeight quaternionWeight_nonneg
    (quaternionCircuitOutput c hc psi)

/-- Normalized bottom distribution of the complexified circuit output. -/
def complexifyCircuitBottomDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    FiniteDistribution (BitBasis W) :=
  addedWireBottomDistribution complexWeight_nonneg
    (complexifyCircuitOutput c hc top psi)

/-- The two normalized quaternion-to-complex output distributions are exactly equal. -/
theorem complexifyCircuitBottomDistribution_eq {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    complexifyCircuitBottomDistribution c hc top psi =
      quaternionCircuitOutputDistribution c hc psi := by
  apply FiniteDistribution.ext
  intro x
  exact complexifyCircuitOutput_bottomProbability c hc top psi x

/-- Every finite bottom event has the same probability after complexification. -/
theorem complexifyCircuitOutput_eventWeight {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (complexifyCircuitBottomDistribution c hc top psi).eventWeight event =
      (quaternionCircuitOutputDistribution c hc psi).eventWeight event := by
  rw [complexifyCircuitBottomDistribution_eq]

/-- Every deterministic finite postprocessing has the same output distribution. -/
theorem complexifyCircuitOutput_pushforward_eq
    {W : Type v} [Fintype W] {β : Type u} [Fintype β]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W))
    (postprocess : BitBasis W → β) :
    (complexifyCircuitBottomDistribution c hc top psi).pushforward postprocess =
      (quaternionCircuitOutputDistribution c hc psi).pushforward postprocess := by
  rw [complexifyCircuitBottomDistribution_eq]

end QuaternionicComputing.Simulation
