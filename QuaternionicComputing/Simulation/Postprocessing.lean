module

public import QuaternionicComputing.Simulation.OutcomeDecoder
public import QuaternionicComputing.Simulation.QuaternionToReal

/-!
# Finite events and deterministic postprocessing of simulated outcomes

The primary and composed simulation theorems identify each normalized bottom
computational-basis weight. This file retains the full target outcome
distributions, decodes their added wires explicitly, and closes the resulting
equalities under arbitrary finite events and deterministic classical maps.

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

/--
Decoding the full basis distribution of a normalized added-wire state gives
the existing bottom distribution of that state.
-/
theorem addedWireDistributionDecoder_ofNormalizedState
    {R : Type u} {W : Type v} [Finite W]
    {weight : R → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    (v : NormalizedState (BitBasis (AddedWire W)) R weight) :
    addedWireDistributionDecoder
        (FiniteDistribution.ofNormalizedState weight hweight v) =
      addedWireBottomDistribution hweight v := by
  apply FiniteDistribution.ext
  intro x
  rfl

/-! ## Complex-to-real output distributions -/

/-- Normalized source output distribution of a complex circuit. -/
def complexCircuitOutputDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (psi : ComplexState (BitBasis W)) : FiniteDistribution (BitBasis W) :=
  FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg
    (complexCircuitOutput c hc psi)

/--
Normalized full target output distribution of the realified circuit, before
the added-wire outcome is decoded.
-/
def realifyCircuitFullOutputDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    FiniteDistribution (BitBasis (AddedWire W)) :=
  FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg
    (realifyCircuitOutput c hc top psi)

/-- Normalized bottom distribution of the realified circuit output. -/
def realifyCircuitBottomDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    FiniteDistribution (BitBasis W) :=
  addedWireDistributionDecoder
    (realifyCircuitFullOutputDistribution c hc top psi)

/-- The two normalized complex-to-real output distributions are exactly equal. -/
theorem realifyCircuitBottomDistribution_eq {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    realifyCircuitBottomDistribution c hc top psi =
      complexCircuitOutputDistribution c hc psi := by
  rw [realifyCircuitBottomDistribution,
    realifyCircuitFullOutputDistribution,
    addedWireDistributionDecoder_ofNormalizedState]
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

/--
Normalized full target output distribution of the complexified circuit,
before the added-wire outcome is decoded.
-/
def complexifyCircuitFullOutputDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    FiniteDistribution (BitBasis (AddedWire W)) :=
  FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg
    (complexifyCircuitOutput c hc top psi)

/-- Normalized bottom distribution of the complexified circuit output. -/
def complexifyCircuitBottomDistribution {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    FiniteDistribution (BitBasis W) :=
  addedWireDistributionDecoder
    (complexifyCircuitFullOutputDistribution c hc top psi)

/-- The two normalized quaternion-to-complex output distributions are exactly equal. -/
theorem complexifyCircuitBottomDistribution_eq {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    complexifyCircuitBottomDistribution c hc top psi =
      quaternionCircuitOutputDistribution c hc psi := by
  rw [complexifyCircuitBottomDistribution,
    complexifyCircuitFullOutputDistribution,
    addedWireDistributionDecoder_ofNormalizedState]
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

/-! ## Quaternion-to-real composed output distributions -/

/--
Normalized full real target distribution of the literally composed
quaternion-to-real simulation, before either added wire is decoded.
-/
def quaternionToRealCircuitFullOutputDistribution
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    FiniteDistribution (BitBasis (AddedWire (AddedWire W))) :=
  FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg
    (quaternionToRealCircuitOutput c hc complexTop realTop psi)

/--
Decode the outer realification wire and then the inner complexification wire
from the normalized composed target output.
-/
def quaternionToRealCircuitBottomDistribution
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    FiniteDistribution (BitBasis W) :=
  twoAddedWireDistributionDecoder
    (quaternionToRealCircuitFullOutputDistribution
      c hc complexTop realTop psi)

/--
The decoded composed real output distribution is exactly the quaternionic
source output distribution.
-/
theorem quaternionToRealCircuitBottomDistribution_eq
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    quaternionToRealCircuitBottomDistribution c hc complexTop realTop psi =
      quaternionCircuitOutputDistribution c hc psi := by
  apply FiniteDistribution.ext
  intro x
  exact quaternionToRealCircuitOutput_bottomProbability
    c hc complexTop realTop psi x

/-- Every finite event agrees after the two added wires are decoded. -/
theorem quaternionToRealCircuitOutput_eventWeight
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (quaternionToRealCircuitBottomDistribution
      c hc complexTop realTop psi).eventWeight event =
      (quaternionCircuitOutputDistribution c hc psi).eventWeight event := by
  rw [quaternionToRealCircuitBottomDistribution_eq]

/--
Every deterministic finite postprocessing agrees after the two added wires
are decoded.
-/
theorem quaternionToRealCircuitOutput_pushforward_eq
    {W : Type v} [Fintype W] {β : Type u} [Fintype β]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W))
    (postprocess : BitBasis W → β) :
    (quaternionToRealCircuitBottomDistribution
      c hc complexTop realTop psi).pushforward postprocess =
      (quaternionCircuitOutputDistribution c hc psi).pushforward
        postprocess := by
  rw [quaternionToRealCircuitBottomDistribution_eq]

end QuaternionicComputing.Simulation
