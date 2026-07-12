module

public import QuaternionicComputing.Semantics.Simulation
public import QuaternionicComputing.Simulation.Postprocessing
public import QuaternionicComputing.Simulation.Scheduled

/-!
# Proof-bearing decoded outcomes for cross-model simulations

This leaf packages the complex-to-real, quaternion-to-complex, scheduled, and
composed quaternion-to-real outcome theorems in the directional semantic
relations from `Semantics.Simulation`.

Point-weight wrappers quantify every raw source column and a normalized pure
top coefficient.  Their values need not be probabilities when the raw source
is unnormalized.  Distribution, event, and deterministic-pushforward wrappers
instead use normalized source states and locally unitary circuits.  Every
target distribution lives on the full added-wire outcome carrier until the
explicit one- or two-wire decoder is applied.

None of these declarations asserts same-space equality, ray equality, product
factorization, mixed-top behavior, partial trace, channel equality,
all-measurement equality, randomized postprocessing, or a resource bound.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

open QuaternionicComputing.Circuit
open QuaternionicComputing.State
open QuaternionicComputing.Simulation

universe u v

/-! ## Representative-level decoded weights -/

/--
Every normalized pure rebit coefficient preserves the decoded basis weights
of every raw complex source column.  Raw columns are not called states or
probability distributions here.
-/
theorem realTopCombination_allRebit_raw_decodedBasisWeightAgreement
    {I : Type u} :
    AllTopDecodedBasisWeightAgreement sumSectorWeightDecoder
      (fun input : I → ℂ => fun outcome => complexBasisWeight input outcome)
      (fun (top : Rebit) (input : I → ℂ) targetOutcome =>
        realBasisWeight
          (realTopCombination (top false) (top true) input) targetOutcome) := by
  intro top input
  funext outcome
  exact realTopCombination_bottomWeight_of_rebit top input outcome

/--
Every normalized pure qubit coefficient preserves the decoded basis weights
of every raw quaternionic source column.
-/
theorem complexTopCombination_allQubit_raw_decodedBasisWeightAgreement
    {I : Type u} :
    AllTopDecodedBasisWeightAgreement sumSectorWeightDecoder
      (fun input : I → ℍ[ℝ] => fun outcome => quaternionBasisWeight input outcome)
      (fun (top : Qubit) (input : I → ℍ[ℝ]) targetOutcome =>
        complexBasisWeight
          (complexTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  exact complexTopCombination_bottomWeight_of_qubit top input outcome

/-! ## Complex circuits represented by real circuits -/

/-- Decoded basis weights agree for every raw input and normalized rebit top. -/
theorem realifyCircuit_allRebit_raw_decodedBasisWeightAgreement
    {W : Type u} [Fintype W] (c : OrderedCircuit ℂ W) :
    AllTopDecodedBasisWeightAgreement
      (addedWireWeightDecoder (W := W))
      (fun input outcome =>
        complexBasisWeight (OrderedCircuit.eval c *ᵥ input) outcome)
      (fun (top : Rebit) input targetOutcome =>
        realBasisWeight
          (OrderedCircuit.eval (realifyCircuit c) *ᵥ
            wireRealTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  exact realifyCircuit_bottomWeight_of_rebit c top input outcome

/--
Every normalized complex input and rebit top gives the source output
distribution after the full real target distribution is explicitly decoded.
-/
theorem realifyCircuit_allRebit_decodedDistributionAgreement
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary) :
    AllTopDecodedDistributionAgreement
      (addedWireDistributionDecoder (W := W))
      (fun source => complexCircuitOutputDistribution c hc source)
      (fun top source => realifyCircuitFullOutputDistribution c hc top source) := by
  intro top source
  apply DecodedDistributionAgreement.of_eq
  exact realifyCircuitBottomDistribution_eq c hc top source

/-- Every finite decoded real-target event has the source event weight. -/
theorem realifyCircuit_decodedEventWeight_eq
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (source : ComplexState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (addedWireDistributionDecoder
      (realifyCircuitFullOutputDistribution c hc top source)).eventWeight event =
        (complexCircuitOutputDistribution c hc source).eventWeight event :=
  DecodedDistributionAgreement.eventWeight_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (realifyCircuit_allRebit_decodedDistributionAgreement c hc)
      top source)
    event

/-- Every deterministic finite postprocessing agrees after real-target decoding. -/
theorem realifyCircuit_decodedPushforward_eq
    {W : Type u} [Fintype W] {Output : Type v} [Fintype Output]
    (c : OrderedCircuit ℂ W) (hc : c.IsLocallyUnitary)
    (top : Rebit) (source : ComplexState (BitBasis W))
    (postprocess : BitBasis W → Output) :
    (addedWireDistributionDecoder
      (realifyCircuitFullOutputDistribution c hc top source)).pushforward
        postprocess =
      (complexCircuitOutputDistribution c hc source).pushforward postprocess :=
  DecodedDistributionAgreement.pushforward_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (realifyCircuit_allRebit_decodedDistributionAgreement c hc)
      top source)
    postprocess

/-! ## Quaternionic circuits represented by complex circuits -/

/-- Decoded basis weights agree for every raw input and normalized qubit top. -/
theorem complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement
    {W : Type u} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) :
    AllTopDecodedBasisWeightAgreement
      (addedWireWeightDecoder (W := W))
      (fun input outcome =>
        quaternionBasisWeight (OrderedCircuit.eval c *ᵥ input) outcome)
      (fun (top : Qubit) input targetOutcome =>
        complexBasisWeight
          (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
            wireComplexTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  exact complexifyCircuit_bottomWeight_of_qubit c top input outcome

/--
Every normalized quaternionic input and qubit top gives the source output
distribution after the full complex target distribution is decoded.
-/
theorem complexifyCircuit_allQubit_decodedDistributionAgreement
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary) :
    AllTopDecodedDistributionAgreement
      (addedWireDistributionDecoder (W := W))
      (fun source => quaternionCircuitOutputDistribution c hc source)
      (fun top source =>
        complexifyCircuitFullOutputDistribution c hc top source) := by
  intro top source
  apply DecodedDistributionAgreement.of_eq
  exact complexifyCircuitBottomDistribution_eq c hc top source

/-- Every finite decoded complex-target event has the source event weight. -/
theorem complexifyCircuit_decodedEventWeight_eq
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (source : QuaternionState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (addedWireDistributionDecoder
      (complexifyCircuitFullOutputDistribution c hc top source)).eventWeight event =
        (quaternionCircuitOutputDistribution c hc source).eventWeight event :=
  DecodedDistributionAgreement.eventWeight_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (complexifyCircuit_allQubit_decodedDistributionAgreement c hc)
      top source)
    event

/-- Every deterministic finite postprocessing agrees after complex-target decoding. -/
theorem complexifyCircuit_decodedPushforward_eq
    {W : Type u} [Fintype W] {Output : Type v} [Fintype Output]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (top : Qubit) (source : QuaternionState (BitBasis W))
    (postprocess : BitBasis W → Output) :
    (addedWireDistributionDecoder
      (complexifyCircuitFullOutputDistribution c hc top source)).pushforward
        postprocess =
      (quaternionCircuitOutputDistribution c hc source).pushforward
        postprocess :=
  DecodedDistributionAgreement.pushforward_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (complexifyCircuit_allQubit_decodedDistributionAgreement c hc)
      top source)
    postprocess

/-! ## One supplied legal schedule -/

/--
The exact circuit selected by one supplied schedule preserves every decoded
basis weight for raw inputs.  No unitarity, arity, choice, or independence
premise is needed at this algebraic point-weight level.
-/
theorem scheduledComplexifyCircuit_allQubit_raw_decodedBasisWeightAgreement
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type v} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    AllTopDecodedBasisWeightAgreement
      (addedWireWeightDecoder (W := W))
      (fun input outcome =>
        quaternionBasisWeight (schedule.scheduledEval gates *ᵥ input) outcome)
      (fun (top : Qubit) input targetOutcome =>
        complexBasisWeight
          (OrderedCircuit.eval
              (complexifyCircuit (schedule.scheduledCircuit gates)) *ᵥ
            wireComplexTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  rw [eval_complexify_scheduledCircuit]
  change wireComplexBottomWeight
      (wireComplexify (schedule.scheduledEval gates) *ᵥ
        wireComplexTopCombination (top false) (top true) input)
      outcome = _
  rw [wireComplexify_mulVec_wireComplexTopCombination]
  exact wireComplexTopCombination_bottomWeight_of_qubit top _ outcome

/--
For pointwise locally unitary gates, the scheduled full target distribution
decodes to the exact scheduled source distribution.
-/
theorem scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type v} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (hunitary : ∀ i, (gates i).IsLocallyUnitary) :
    AllTopDecodedDistributionAgreement
      (addedWireDistributionDecoder (W := W))
      (fun source =>
        quaternionCircuitOutputDistribution (schedule.scheduledCircuit gates)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            schedule gates hunitary)
          source)
      (fun top source =>
        complexifyCircuitFullOutputDistribution
          (schedule.scheduledCircuit gates)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            schedule gates hunitary)
          top source) :=
  complexifyCircuit_allQubit_decodedDistributionAgreement
    (schedule.scheduledCircuit gates)
    (LegalSchedule.scheduledCircuit_isLocallyUnitary
      schedule gates hunitary)

/-- Every finite event agrees for the exact supplied schedule after decoding. -/
theorem scheduledComplexifyCircuit_decodedEventWeight_eq
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type v} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (hunitary : ∀ i, (gates i).IsLocallyUnitary)
    (top : Qubit) (source : QuaternionState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (addedWireDistributionDecoder
      (complexifyCircuitFullOutputDistribution
        (schedule.scheduledCircuit gates)
        (LegalSchedule.scheduledCircuit_isLocallyUnitary
          schedule gates hunitary)
        top source)).eventWeight event =
      (quaternionCircuitOutputDistribution (schedule.scheduledCircuit gates)
        (LegalSchedule.scheduledCircuit_isLocallyUnitary
          schedule gates hunitary)
        source).eventWeight event :=
  DecodedDistributionAgreement.eventWeight_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement
        schedule gates hunitary)
      top source)
    event

/-- Deterministic postprocessing agrees for the supplied schedule after decoding. -/
theorem scheduledComplexifyCircuit_decodedPushforward_eq
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type v} [Fintype W] {precedes : ι → ι → Prop}
    {Output : Type*} [Fintype Output]
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (hunitary : ∀ i, (gates i).IsLocallyUnitary)
    (top : Qubit) (source : QuaternionState (BitBasis W))
    (postprocess : BitBasis W → Output) :
    (addedWireDistributionDecoder
      (complexifyCircuitFullOutputDistribution
        (schedule.scheduledCircuit gates)
        (LegalSchedule.scheduledCircuit_isLocallyUnitary
          schedule gates hunitary)
        top source)).pushforward postprocess =
      (quaternionCircuitOutputDistribution (schedule.scheduledCircuit gates)
        (LegalSchedule.scheduledCircuit_isLocallyUnitary
          schedule gates hunitary)
        source).pushforward postprocess :=
  DecodedDistributionAgreement.pushforward_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement
        schedule gates hunitary)
      top source)
    postprocess

/-! ## Composed quaternion-to-real outcomes -/

/--
Two normalized pure top coefficients preserve every decoded basis weight for
every raw quaternionic input.  The outer real wire is decoded before the inner
complex wire; the pair does not assert target-state factorization.
-/
theorem quaternionToRealCircuit_allPureTop_raw_decodedBasisWeightAgreement
    {W : Type u} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) :
    AllTopDecodedBasisWeightAgreement
      (twoAddedWireWeightDecoder (W := W))
      (fun input outcome =>
        quaternionBasisWeight (OrderedCircuit.eval c *ᵥ input) outcome)
      (fun (tops : Qubit × Rebit) input targetOutcome =>
        realBasisWeight
          (OrderedCircuit.eval (quaternionToRealCircuit c) *ᵥ
            wireRealTopCombination (tops.2 false) (tops.2 true)
              (wireComplexTopCombination
                (tops.1 false) (tops.1 true) input))
          targetOutcome) := by
  intro tops input
  funext outcome
  change wireQuaternionToRealBottomWeight
      (OrderedCircuit.eval (quaternionToRealCircuit c) *ᵥ
        wireRealTopCombination (tops.2 false) (tops.2 true)
          (wireComplexTopCombination
            (tops.1 false) (tops.1 true) input))
      outcome = _
  rw [quaternionToRealCircuit,
    eval_realifyCircuit_mulVec_wireRealTopCombination,
    eval_complexifyCircuit_mulVec_wireComplexTopCombination]
  unfold wireQuaternionToRealBottomWeight
  rw [wireRealTopCombination_bottomWeight_of_rebit,
    wireRealTopCombination_bottomWeight_of_rebit]
  exact wireComplexTopCombination_bottomWeight_of_qubit tops.1 _ outcome

/--
The full twice-translated real output distribution decodes to the original
quaternionic output distribution for every normalized top pair and source.
-/
theorem quaternionToRealCircuit_allPureTop_decodedDistributionAgreement
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary) :
    AllTopDecodedDistributionAgreement
      (twoAddedWireDistributionDecoder (W := W))
      (fun source => quaternionCircuitOutputDistribution c hc source)
      (fun (tops : Qubit × Rebit) source =>
        quaternionToRealCircuitFullOutputDistribution
          c hc tops.1 tops.2 source) := by
  intro tops source
  apply DecodedDistributionAgreement.of_eq
  exact quaternionToRealCircuitBottomDistribution_eq
    c hc tops.1 tops.2 source

/-- Every finite event agrees after both added wires are decoded. -/
theorem quaternionToRealCircuit_decodedEventWeight_eq
    {W : Type u} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (source : QuaternionState (BitBasis W))
    (event : Finset (BitBasis W)) :
    (twoAddedWireDistributionDecoder
      (quaternionToRealCircuitFullOutputDistribution
        c hc complexTop realTop source)).eventWeight event =
      (quaternionCircuitOutputDistribution c hc source).eventWeight event :=
  DecodedDistributionAgreement.eventWeight_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (quaternionToRealCircuit_allPureTop_decodedDistributionAgreement c hc)
      (complexTop, realTop) source)
    event

/-- Every deterministic postprocessing agrees after both wires are decoded. -/
theorem quaternionToRealCircuit_decodedPushforward_eq
    {W : Type u} [Fintype W] {Output : Type v} [Fintype Output]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (source : QuaternionState (BitBasis W))
    (postprocess : BitBasis W → Output) :
    (twoAddedWireDistributionDecoder
      (quaternionToRealCircuitFullOutputDistribution
        c hc complexTop realTop source)).pushforward postprocess =
      (quaternionCircuitOutputDistribution c hc source).pushforward
        postprocess :=
  DecodedDistributionAgreement.pushforward_eq
    (AllTopDecodedDistributionAgreement.forTopInput
      (quaternionToRealCircuit_allPureTop_decodedDistributionAgreement c hc)
      (complexTop, realTop) source)
    postprocess

end QuaternionicComputing.Semantics
