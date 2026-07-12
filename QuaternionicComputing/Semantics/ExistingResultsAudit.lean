module

public import QuaternionicComputing.Semantics.ExistingResults

/-!
# Audit of semantic classifications for existing exact results

This non-root leaf allocates the six stable declarations introduced by
`Semantics.ExistingResults` to three source-order aggregate consumers:

* three normalized-state and reduced-matrix boundary declarations;
* two schedule and order-distinction declarations;
* one conditional exact-compilation declaration.

The aggregates retain the concrete counterexample inputs and observations.
In particular, they do not promote one-input output agreement to an all-input
claim, and they do not turn a supplied exact compiler into a synthesis result.
The public root deliberately does not import this file.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.ExistingResultsAudit

universe u v w

open QuaternionicComputing.Circuit
open QuaternionicComputing.State
open QuaternionicComputing.Quaternion
open QuaternionicComputing.Semantics

/-! ## Exact allocation of the three state and reduced-matrix declarations -/

/--
Source-order consumer for the normalized left-phase rejection, canonical
reduced-outer agreement, and quaternionic distribution/ray separation.
-/
theorem stateResults_api (column : n → ℂ) :
    (∃ a b : QuaternionState Bool,
      LeftPhaseEquivalent (a : Bool → ℍ[ℝ]) b ∧
        quaternionTotalWeight (phaseWitnessGate a) = 1 ∧
        quaternionTotalWeight (phaseWitnessGate b) = 1 ∧
        ¬ LeftPhaseEquivalent (phaseWitnessGate a) (phaseWitnessGate b)) ∧
      (reducedRealOuter (realColumn0 column) =
          reducedRealOuter (realColumn1 column) ∧
        ∀ i, reducedRealOuter (realColumn0 column) i i =
          complexBasisWeight column i) ∧
      (NormalizedDistributionEq quaternionWeight quaternionWeight_nonneg
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
        ¬ QuaternionStatePhaseEq
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
        State.QuaternionRay.mk
            Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
          State.QuaternionRay.mk
            Circuit.ProductInputOrderingWitness.jThenIGroundOutput) :=
  ⟨normalizedQuaternionLeftPhase_rejection,
    realCanonicalColumns_reducedOuterAgreement column,
    quaternionGroundOutputs_distributionEq_not_rayEq⟩

/-! ## Exact allocation of the two schedule declarations -/

/--
Source-order consumer for commuting-schedule exact equality and the complete
fixed quaternionic order-witness boundary, including its exact translation.
-/
theorem scheduleResults_api
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {precedes : ι → ι → Prop}
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s t : LegalSchedule ι precedes) (gates : ι → PlacedGate R W)
    (hcomm : Pairwise fun i j : ι ⇒
      Commute (gates i).denote (gates j).denote) :
    ExactCircuitEq (s.scheduledCircuit gates) (t.scheduledCircuit gates) ∧
      (¬ ExactCircuitEq
          (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily) ∧
        OutputWeightEqAt quaternionWeight
          (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          Circuit.ProductInputOrderingWitness.groundColumn ∧
        ¬ PureInputBasisMeasurementEq quaternionWeight
          (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily) ∧
        ¬ ExactCircuitEq
          (Simulation.complexifyCircuit
            (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
              Circuit.OrderingWitness.gateFamily))
          (Simulation.complexifyCircuit
            (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
              Circuit.OrderingWitness.gateFamily)) ∧
        Simulation.wireComplexBottomWeight
            Simulation.OrderingWitness.iThenJComplexOutput
            Circuit.OrderingWitness.basis00 ≠
          Simulation.wireComplexBottomWeight
            Simulation.OrderingWitness.jThenIComplexOutput
            Circuit.OrderingWitness.basis00) :=
  ⟨scheduledCircuit_exactCircuitEq_of_pairwise_commute s t gates hcomm,
    quaternionOrderingWitness_scopeBoundary⟩

/-! ## Exact allocation of the conditional compiler declaration -/

/--
Source-order consumer for the exact circuit-equality wrapper supplied by an
existing certified compiler.  No compiler inhabitant is synthesized here.
-/
theorem compilerResult_api
    {R : Type u} {W : Type v} [Semiring R] [Fintype W]
    (compiler : ExactGateCompiler R W) (circuit : OrderedCircuit R W) :
    ExactCircuitEq (compiler.compileCircuit circuit) circuit :=
  compiler.compileCircuit_exactCircuitEq circuit

/-! ## Concrete boundary endpoint -/

/--
The fixed ordering example simultaneously exhibits equality of the complete
ground-input distribution, inequality of quaternionic rays, source-circuit
inequality, and inequality after exact complex translation.
-/
theorem concreteOrderingBoundaries_api :
    NormalizedDistributionEq quaternionWeight quaternionWeight_nonneg
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
        State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      ¬ ExactCircuitEq
        (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
          Circuit.OrderingWitness.gateFamily)
        (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
          Circuit.OrderingWitness.gateFamily) ∧
      ¬ ExactCircuitEq
        (Simulation.complexifyCircuit
          (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily))
        (Simulation.complexifyCircuit
          (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily)) := by
  rcases quaternionGroundOutputs_distributionEq_not_rayEq with
    ⟨hDistribution, -, hRay⟩
  rcases quaternionOrderingWitness_scopeBoundary with
    ⟨hSource, -, -, hTranslated, -⟩
  exact ⟨hDistribution, hRay, hSource, hTranslated⟩

#print axioms stateResults_api
#print axioms scheduleResults_api
#print axioms compilerResult_api
#print axioms concreteOrderingBoundaries_api

end QuaternionicComputing.Semantics.ExistingResultsAudit
