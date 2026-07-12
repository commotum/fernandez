# 9C-OUTCOMES

## Current Facts

- Stage 9B is independently complete. The current tree has 88 Lean sources
  including the public root, 1,064 exact semantic-manifest entries, 133
  resolving consumers, 272 direct release-audit labels, 458 root axiom
  commands, and 16 local `SimulationAudit` commands. The wrapper/audit focused
  builds pass at `2369` and `2381`, the combined stable/audit/public-root/
  release-audit build passes at `2767/2767`, and the cached default build
  completes `2765` jobs. The parsed axiom union is exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Stage 9C has exactly seven inventory touchpoints: five Stage 9C-owned frozen
  families (`EQC-009`, `EQC-013`, `EQC-032`, `EQC-035`, and `EQC-038`) plus the
  outcome slices of the Stage 9B-owned scheduled and composed families
  (`EQC-036` and `EQC-037`). `EQC-005` is an already-closed finite-event/
  pushforward dependency and is not reopened. Raw state families `EQC-031` and
  `EQC-034` remain separate from their observable families `EQC-032` and
  `EQC-035`.

| Touchpoint | Strongest existing evidence | Exact remaining gap |
|---|---|---|
| `EQC-009-REAL-COLUMNS-MEASUREMENT` | `realTopCombination_bottomWeight_of_rebit`, subsuming both canonical columns | no stable all-`Rebit` decoded-basis wrapper; the current sector decoder is audit-local |
| `EQC-013-COMPLEX-COLUMNS-MEASUREMENT` | `complexTopCombination_bottomWeight_of_qubit`, subsuming both canonical columns | no stable all-`Qubit` decoded-basis wrapper; no reduced-density conclusion follows |
| `EQC-032-C2R-OBSERVABLE` | `realifyCircuitOutput_bottomProbability` for every locally unitary circuit, normalized source input, and `Rebit` | no all-top decoded-basis relation with the full added-wire outcome carrier visible |
| `EQC-035-Q2C-OBSERVABLE` | `complexifyCircuitOutput_bottomProbability` under the analogous quaternionic hypotheses | the same missing relation-valued wrapper and explicit decoder |
| `EQC-038-POSTPROCESSING-SIMULATION` | primary bottom-distribution, event, and deterministic-pushforward equalities | current target distributions are already marginalized; an `id` decoder would erase the target carrier and marginal policy |
| outcome slice of `EQC-036-SCHEDULED-Q2C` | outcome conjunct of `scheduledQuaternionToComplex_exactSimulation` | no separately named supplied-schedule outcome relation; the old conjunction carries an irrelevant arity premise |
| outcome slice of `EQC-037-Q2R-COMPOSED` | `quaternionToRealCircuitOutput_bottomProbability` | no explicit two-wire relation, full target distribution, event theorem, or postprocessing theorem |

- `DecodedBasisWeightAgreement`, `DecodedDistributionAgreement`, their
  composition and event/pushforward consequences, and both `AllTop...`
  quantifier policies already compile in `Semantics/Simulation.lean`.
- `Simulation/Postprocessing.lean` packages normalized source distributions and
  already-marginalized primary target distributions. It does not yet expose a
  decoder from a full `BitBasis (AddedWire W)` distribution, a full target
  distribution, or the composed quaternion-to-real distribution closure.
- `FiniteDistribution.pushforward` can express forgetting the added wire via
  `Circuit.tailBits`. Independently, the explicit false/true sector formula
  makes a direct decoder constructive and normalization-preserving. A second
  strict-compiling probe at `/private/tmp/Stage9CRelationsProbe.lean` proves
  that the direct decoder equals `pushforward tailBits`, so this desired
  identification has no remaining proof obstruction.
- The strict-compiling prototype
  `/private/tmp/Stage9CDecoderProbe.lean` constructs explicit one- and two-wire
  weight/distribution decoders, full target distributions, the missing composed
  distribution equality, and ten core relation wrappers. Its emitted wrapper
  axiom union is exactly the standard three items. The prototype is signature
  evidence only, not repository implementation or audit coverage.

## Updated Assumptions

- A decoded-distribution theorem must start from the full target distribution.
  Reusing an already-marginalized distribution with decoder `id` does not close
  Stage 9C because it hides the changed target outcome type and added-wire
  policy.
- The stable one-wire decoder will sum the explicit false/true sectors and
  expose compatibility between distribution weights and the corresponding
  weight decoder. It should also be identified with deterministic pushforward
  through `tailBits`; if direct proof engineering favors defining it as that
  pushforward, the same point-weight compatibility theorem remains mandatory.
- Two-wire decoding is composition in physical construction order: first
  remove the outer realification wire, then remove the inner complexification
  wire. The normalized top parameter is explicitly `Qubit × Rebit`, inner
  complex top first and outer real top second.
- `EQC-009` and `EQC-013` concern arbitrary raw source columns with normalized
  pure top coefficients. Their results are decoded weights, not probabilities
  unless the source column is normalized. Circuit distribution, event, and
  postprocessing wrappers quantify normalized source states and locally
  unitary circuits so their values are actual probabilities.
- Scheduled point-weight agreement needs only one supplied `LegalSchedule`, its
  gates, every raw source column, and a normalized `Qubit`; it needs neither
  pointwise local unitarity nor an arity premise. Packaged scheduled
  distribution/event/pushforward results additionally need pointwise local
  unitarity and normalized source states. None proves schedule choice or
  schedule independence.
- The primary and composed point-weight wrappers have the same stronger split:
  they quantify every raw source column and need no local-unitarity premise.
  Only packaged normalized distributions and their finite consequences need
  local unitarity. This is stronger than merely restating the normalized source
  probability theorems while remaining honest about raw weights versus actual
  probabilities.
- Finite events and deterministic pushforwards are consequences of decoded
  distribution agreement, but Stage 9C still exports separately named theorems
  so the observation level cannot be confused with the distribution relation.
- No current evidence justifies a new paper correction. The cohort phrase
  “pure uncorrelated top” continues to mean a normalized top coefficient
  parameter only; it is not a proved tensor factorization or a mixed-top claim.

## Big Picture Objective

Close every remaining cross-model observable family with proof-bearing
relations whose source and full target outcome carriers, normalized top policy,
decoder, and deterministic marginal are explicit. Deliver point-weight,
normalized-distribution, finite-event, and deterministic-postprocessing levels
separately for the primary, scheduled, and composed simulations, without
promoting any result to ray, density, channel, all-effect, product-state,
mixed-top, randomized, or resource semantics.

## Detailed Implementation Plan

- Add the low-dependency stable leaf
  `QuaternionicComputing/Simulation/OutcomeDecoder.lean` with a reusable
  decoder layer:
  - `sumSectorWeightDecoder` for generic `I ⊕ I` coordinate encodings;
  - `addedWireWeightDecoder` and `twoAddedWireWeightDecoder` for wire-facing
    target outcomes;
  - `addedWireDistributionDecoder` and
    `twoAddedWireDistributionDecoder` with normalized finite-distribution
    outputs;
  - weight-compatibility theorems and a checked identification of one-wire
    decoding with `FiniteDistribution.pushforward Circuit.tailBits`.
- Extend `QuaternionicComputing/Simulation/Postprocessing.lean`, importing that
  decoder leaf, with:
  - `realifyCircuitFullOutputDistribution`,
    `complexifyCircuitFullOutputDistribution`, and
    `quaternionToRealCircuitFullOutputDistribution` before marginalization;
  - `quaternionToRealCircuitBottomDistribution`, its source-distribution
    equality, and its finite-event and deterministic-pushforward consequences.
- Add the stable semantic leaf
  `QuaternionicComputing/Semantics/SimulationOutcomes.lean` with exactly 18
  proof-bearing wrappers, allocated by comparison level:
  1. `realTopCombination_allRebit_raw_decodedBasisWeightAgreement`;
  2. `complexTopCombination_allQubit_raw_decodedBasisWeightAgreement`;
  3. `realifyCircuit_allRebit_raw_decodedBasisWeightAgreement`;
  4. `realifyCircuit_allPureTop_decodedDistributionAgreement`;
  5. `realifyCircuit_decodedEventWeight_eq`;
  6. `realifyCircuit_decodedPushforward_eq`;
  7. `complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`;
  8. `complexifyCircuit_allPureTop_decodedDistributionAgreement`;
  9. `complexifyCircuit_decodedEventWeight_eq`;
  10. `complexifyCircuit_decodedPushforward_eq`;
  11. `scheduledComplexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`;
  12. `scheduledComplexifyCircuit_allPureTop_decodedDistributionAgreement`;
  13. `scheduledComplexifyCircuit_decodedEventWeight_eq`;
  14. `scheduledComplexifyCircuit_decodedPushforward_eq`;
  15. `quaternionToRealCircuit_allPureTop_raw_decodedBasisWeightAgreement`;
  16. `quaternionToRealCircuit_allPureTop_decodedDistributionAgreement`;
  17. `quaternionToRealCircuit_decodedEventWeight_eq`;
  18. `quaternionToRealCircuit_decodedPushforward_eq`.
- Prove the two matrix/representative wrappers directly from the normalized-top
  sector identities. Prove the four circuit point wrappers at their strongest
  raw-input scope directly from the raw bottom-weight theorems, with no
  local-unitarity premise. Prove primary, scheduled, and composed distribution
  wrappers from full target distributions and explicit decoders; derive finite
  event and deterministic-pushforward statements through the checked
  distribution relations. Obtain the scheduled family by instantiating the
  primary quaternion-to-complex result at the exact supplied chronological
  circuit.
- Replace the audit-local `sumSectorWeightDecoder` and already-decoded `id`
  examples in `Semantics/SimulationAudit.lean` with the stable explicit
  decoders. Add five disjoint aggregates allocating the 18 semantic wrappers
  exactly as `2 + 4 + 4 + 4 + 4`: representative, complex-to-real,
  quaternion-to-complex, scheduled quaternion-to-complex, and composed
  quaternion-to-real outcomes.
- Exercise both canonical `|0⟩`/`|1⟩` top specializations, an arbitrary
  normalized top, the genuinely quaternionic `j` example, existing nontrivial
  circuit examples, one actual legal schedule with locally unitary gates, the
  nested outer-real/inner-complex decoder order, and the zero-wire
  `BitBasis Empty` boundary. Do not manufacture a normalized state on an empty
  outcome carrier.
- Public-import only the stable outcome leaf from `QuaternionicComputing.lean`.
  Add every new public decoder, full-distribution, source closure, and semantic
  wrapper declaration exactly once to `AxiomAudit.lean` and the Goal 2 semantic
  API manifest, with a real aggregate consumer. Preserve the first-1,064
  manifest prefix hash and frozen Goal 1 cohort checksum; derive new totals
  from the completed source rather than projecting them in advance.
- Fold exact theorem names, scopes, counts, hashes, builds, audits, and negative
  boundaries into classification, README/public docstrings, architecture,
  conventions, mathlib API notes, traceability, corrections if and only if a
  paper issue emerges, release/axiom reports, Goal 3 prerequisites, this report,
  and `goal-2/0-plan.md`.

## Build Structure

- `QuaternionicComputing/Simulation/OutcomeDecoder.lean`: low-dependency stable
  concrete decoder API, public-importing only `State/Distribution` and
  `Circuit/AddedWire`. It contains no circuit evolution, semantic relation, or
  audit declaration.
- `QuaternionicComputing/Simulation/Postprocessing.lean`: stable full-
  distribution and missing composed finite-outcome API. It public-imports the
  decoder leaf and may add the narrow quaternion-to-real source import needed
  for the composed closure, but it must not import any semantic or audit leaf.
- `QuaternionicComputing/Semantics/SimulationOutcomes.lean`: stable high leaf
  containing only the 18 relation-valued/consequence wrappers. It public-imports
  the generic relation leaf, postprocessing source API, and scheduled source
  API; it must not import the public root, any audit, channels, hierarchy audit,
  ordering diagnostics, or resource/compiler leaves.
- `QuaternionicComputing/Semantics/SimulationAudit.lean`: non-root diagnostic
  allocation and concrete boundary consumers. No stable module imports it.
- `QuaternionicComputing.lean`: public re-export of the stable outcome leaf.
- `QuaternionicComputing/AxiomAudit.lean`: direct endpoints for every new
  stable declaration selected by the completed manifest.
- High-fanout state, matrix, circuit, density, channel, hierarchy, representative
  encoding, and operator/state wrapper leaves remain unchanged.
- Focused commands:
  `lake build QuaternionicComputing.Simulation.OutcomeDecoder
  QuaternionicComputing.Simulation.Postprocessing` and
  `lake build QuaternionicComputing.Semantics.SimulationOutcomes`.
- Adjacent commands:
  `lake build QuaternionicComputing.Simulation.Examples
  QuaternionicComputing.Semantics.SimulationAudit QuaternionicComputing
  QuaternionicComputing.AxiomAudit`, plus warning-as-error direct source and
  root-only downstream checks.

## Boundary Checks

- Every decoded relation visibly compares different source and target outcome
  carriers. The decoder is never `id` when an added wire is present.
- `sumSectorWeightDecoder` results on raw columns are weights. Only normalized
  source/output structures are described as probabilities or distributions.
- Full target distributions retain every added-wire assignment until the named
  decoder is applied. One-wire decoding sums two assignments; composed decoding
  sums four via outer-then-inner composition.
- `Qubit × Rebit` records the inner complex and outer real top parameters. The
  theorem does not assert that an arbitrary target state factors into those top
  states and the source state.
- Scheduled point weights retain only the supplied schedule and gates;
  scheduled normalized distributions retain the additional pointwise
  local-unitarity premise. No schedule is selected, quotient-identified, or
  made independent.
- Event equality is finite-event equality after decoding. Pushforward equality
  is deterministic finite classical postprocessing after decoding. Neither is
  randomized postprocessing, channel equality, or all-effect behavior.
- No cross-model outcome wrapper concludes `ExactOperatorEq`, `ExactCircuitEq`,
  state/ray phase equality, `ChannelEq`, `AllMeasurementEq`, density evolution,
  partial trace, mixed-top behavior, product structure, synthesis, runtime, or
  a resource bound.

## No-Cheating Checks

- Reject any distribution wrapper whose decoder is `id` on an
  already-marginalized target; inspect target carrier types and decoder
  definitions in every signature.
- Do not define a decoder in terms of the source distribution or the equality
  being proved. Its weight and normalization fields must depend only on the
  target distribution and the explicit sector map.
- Do not count generic `DecodedDistributionAgreement.eventWeight_eq` or
  `.pushforward_eq` alone as family closure; separately named concrete wrappers
  and real consumers are required.
- Do not reuse the scheduled exact-simulation conjunction with an unused arity
  premise. Derive raw point weights from the supplied scheduled circuit without
  local unitarity; add pointwise local unitarity only for normalized
  distributions and their consequences.
- The composed consumer must evaluate the two decoder layers in the correct
  order and compare against the original quaternionic source distribution; a
  one-layer or Equation 63 reindexing substitute is insufficient.
- No `Equivalence` instance, symmetric/transitive cross-model relation,
  impossible normalized empty value, `sorry`, `admit`, `sorryAx`, declaration
  axiom, `opaque`, `unsafe`, heartbeat override, broad simplifier, public audit
  import, tracked generated artifact, or frozen-cohort edit.

## Completion Requirements

- All seven inventory touchpoints have stable proof-bearing outcome
  classifications. The five Stage 9C-owned families are closed, and the
  scheduled/composed rows gain their exact outcome slices without changing
  their Stage 9B operator/state classifications.
- The decoder layer exposes one- and two-wire point/distribution compatibility,
  full target distributions, and the missing composed distribution/event/
  pushforward closure. The one-wire decoder is theorem-identified with
  forgetting `tailBits` or is definitionally that pushforward with the sector
  formula separately proved.
- Exactly 18 semantic wrappers strict-compile and five non-root aggregates
  allocate them once as `2 + 4 + 4 + 4 + 4`, with canonical, genuinely
  quaternionic, nontrivial-circuit, supplied-schedule, nested-decoder, and
  zero-wire values.
- Stable imports remain narrow; the public root exposes only stable outcomes;
  existing examples and source theorems still compile; no stable leaf imports
  `SimulationAudit`.
- The semantic manifest has an unchanged 1,064-entry prefix, exact source
  order, seven nonempty axes, unique names, exact aggregate consumers, and exact
  release-audit intersection. Generated names and consumers strict-compile.
- Root and local axiom parsers cover every emitted block; each endpoint uses a
  subset of the permitted standard axioms and the collective union is exactly
  `propext`, `Classical.choice`, and `Quot.sound`, with no unknown declaration
  or `sorryAx`.
- Focused, adjacent, combined, default, warning-as-error, root-only downstream,
  hole/shortcut/false-equivalence/import-boundary/artifact/Markdown/whitespace/
  stale-wording/diff/frozen-checksum checks pass.
- Documentation, traceability, corrections, release evidence, Goal 3, this
  report, and the master plan agree on exact theorem scopes and counts.
- Independent source, semantic, manifest, and integrated closure reviews return
  **PASS** before `9C-OUTCOMES` and the umbrella `9-CROSSMODEL` are marked
  complete.

## Stage Results

- Implementation pending.
