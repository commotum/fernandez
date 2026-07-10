# 2-CORE

## Current Facts

- Stage 1 froze 51 comparison families and 936 uniquely assigned public Goal 1
  declarations. `EQC-004-NORMALIZED-BASIS-DIST`,
  `EQC-005-EVENT-PUSHFORWARD-CONGRUENCE`, `EQC-006-UNITARY-EVOLUTION-NORM`,
  and `EQC-026-ORDERED-EVAL` are the primary Stage 2 cohort rows.
- `Circuit.OrderedCircuit.eval` is the only public chronological evaluator.
  `eval_congr` and `eval_append` supply exact gatewise and compositional lifts.
- `State.NormalizedState` packages a finite column with an explicit scalar-
  weight normalization proof. The weight function is not a typeclass.
- `State.FiniteDistribution.ext`, `eventWeight_eq_of_weight_eq`, and
  `pushforward_eq_of_weight_eq` already provide the distribution-level
  extensionality and finite classical consequences needed here.
- `Matrix.mulVec_single_one` identifies action on `Pi.single x 1` with matrix
  column `x`, but it requires finite decidable input indices and a
  `NonAssocSemiring`.
- For a generic scalar weight, a basis ket need not be normalized. Any theorem
  deriving all-basis behavior from all-normalized-pure-input behavior therefore
  needs an explicit basis-normalization premise.
- A complete combined draft compiles with warnings as errors in
  `/tmp/SemanticsCoreMeasurementDraft.lean`; it has not yet been accepted as
  repository evidence.

## Updated Assumptions

- `ExactOperatorEq` should support compatible rectangular matrices; exact
  circuit equality specializes it to the square `BitBasis W` evaluator.
- `ExactCircuitEq C D` must be definitionally only equality of
  `OrderedCircuit.eval C` and `OrderedCircuit.eval D`. Gate-list equality is
  sufficient but not required.
- `BasisWeightEq`, `OutputWeightEqAt`, `BasisMeasurementEq`, and
  `PureInputBasisMeasurementEq` are distinct predicates with different
  quantifier scopes.
- The generic measurement relations need no positivity premise: they compare
  supplied real-valued weights. Positivity and normalization enter only when
  packaging a genuine `FiniteDistribution`.
- This stage proves exact-to-observational implications and pointwise-
  distribution equivalence. Phase, certified classical behavior, channels,
  cross-model decoding, and approximation remain owned by later stages.

## Big Picture Objective

Introduce a low-dependency, reusable same-space vocabulary for exact operator
and circuit equality, fixed-input output weights, all-basis-input weights,
all-normalized-pure-input weights, and normalized finite distributions, with
the precise implications already justified by Goal 1 APIs.

## Detailed Implementation Plan

- Add `QuaternionicComputing/Semantics/Core.lean` importing only
  `Circuit.Basic`. Define `ExactOperatorEq` and `ExactCircuitEq`, their
  equivalence laws, multiplication congruence, gatewise circuit lift, and
  append lift.
- Add `QuaternionicComputing/Semantics/Measurement.lean` importing `Core` and
  `State.Distribution`. Define `BasisWeightEq`, `OutputWeightEqAt`,
  `BasisMeasurementEq`, `PureInputBasisMeasurementEq`, and
  `NormalizedDistributionEq`.
- Prove equivalence laws for every genuine same-domain relation, exact-to-
  weaker implications, basis-ket/column characterizations, and
  `BasisWeightEq ↔ NormalizedDistributionEq`.
- Prove finite-event, deterministic-pushforward, and pushforward-weight
  consequences through the existing public distribution API.
- State the pure-input-to-basis implication only under explicit normalization
  of every `Pi.single x 1` basis ket.
- Add `Semantics/CoreAudit.lean` as a non-root diagnostic consumer with empty
  and Boolean index examples, standard real/complex/quaternion basis-ket
  normalization checks, scope-separation examples, and axiom spot checks.
- Add every new stable semantic declaration to the separate Goal 2 API
  manifest after its owning leaf and consumer compile.

## Build Structure

- `Semantics/Core.lean`: low-dependency public API definitions and exact laws;
  imports no distribution, phase, simulation, density, or audit leaf.
- `Semantics/Measurement.lean`: public measurement/distribution vocabulary;
  depends only on `Core` and the existing finite-distribution leaf.
- `Semantics/CoreAudit.lean`: proof-side/diagnostic consumer and edge examples;
  it is not imported by either core leaf or the public root.
- `QuaternionicComputing.lean` remains untouched until the stage leaf and real
  consumer pass; if promoted in this stage, root and audit builds become
  mandatory.
- Focused commands:
  `lake build QuaternionicComputing.Semantics.Core`,
  `lake build QuaternionicComputing.Semantics.Measurement`, and
  `lake build QuaternionicComputing.Semantics.CoreAudit`.
- Adjacent consumers are the audit leaf and focused builds of
  `QuaternionicComputing.Circuit.Basic` and
  `QuaternionicComputing.State.Distribution`; public promotion additionally
  requires the root and explicit axiom audit.

## Boundary Checks

- Exact operator equality is same-domain matrix equality. It is not mapped
  embedding equality or equality up to phase.
- Exact circuit equality goes through the chronological evaluator and says
  nothing about gate-list identity, resource equality, or schedule legality.
- One fixed input, all basis inputs, and all normalized pure inputs remain
  separate in definitions and theorem signatures.
- Basis-measurement equality compares only computational-basis preparation and
  readout. It is not all-pure-input, channel, or all-effect equality.
- Distribution equality, finite-event equality, and deterministic
  postprocessing equality remain classical outcome relations.
- Empty index types are permitted for exact operator/circuit relations; no
  nonexistent normalized state is fabricated.

## No-Cheating Checks

- No relation is defined by referring to the theorem that it is intended to
  classify.
- `ExactCircuitEq` unfolds only to evaluator equality.
- The all-pure-to-all-basis implication carries a real basis-normalization
  premise; normalization is not inferred for an arbitrary weight function.
- Equivalence instances/theorems are supplied only for fixed-domain symmetric
  relations. No approximation or directional cross-model certificate is given
  an `Equivalence` instance.
- The distribution implications call the existing `FiniteDistribution` proofs
  rather than accepting arbitrary unnormalized functions as probabilities.
- Completed leaves must contain no `sorry`, `admit`, new axiom, opaque/unsafe
  shortcut, or impossible premise.

## Completion Requirements

- The five relation families have distinct public signatures and named
  reflexive/symmetric/transitive laws.
- `ExactCircuitEq` definitionally exposes only equality of evaluations and has
  compiling gatewise/append consumers.
- Basis-ket action is connected to matrix columns using the pinned
  `Matrix.mulVec_single_one` API.
- Pointwise normalized basis weights are equivalent to packaged finite-
  distribution equality and imply event/pushforward equality.
- Empty/Boolean index and standard scalar-weight examples compile in a separate
  consumer without collapsing input scopes.
- Focused leaves, adjacent consumer, warning-as-error checks, axiom spot audit,
  API-manifest validation, hole/shortcut/whitespace scans, and
  `git diff --check` pass.

## Stage Results

- Stage active. Repository implementation, consumer verification, API-manifest
  entries, and final evidence remain to be completed.
