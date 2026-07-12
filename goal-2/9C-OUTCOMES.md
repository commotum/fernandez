# 9C-OUTCOMES

## Current Facts

- Stage 9C is independently implemented and verified. The current tree has 90
  Lean sources including the public root, 1,100 exact semantic-manifest
  entries, 140 resolving consumers, 308 direct release-audit labels, 494 root
  axiom commands, and 20 local `SimulationAudit` commands. Focused decoder,
  postprocessing, outcome-wrapper, and audit builds pass at `2347`, `2361`,
  `2365`, and `2385`; the final combined stable/audit/public-root/release-audit
  build passes at `2769/2769`, and the cached default build completes `2767`
  jobs. The root parser covers `491 + 3 = 494` blocks and the local parser
  covers `19 + 1 = 20`; every endpoint uses a subset and both collective
  unions are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Stage 9C began with exactly seven inventory touchpoints: five Stage 9C-owned
  frozen families (`EQC-009`, `EQC-013`, `EQC-032`, `EQC-035`, and `EQC-038`) plus the
  outcome slices of the Stage 9B-owned scheduled and composed families
  (`EQC-036` and `EQC-037`). `EQC-005` is an already-closed finite-event/
  pushforward dependency and is not reopened. Raw state families `EQC-031` and
  `EQC-034` remain separate from their observable families `EQC-032` and
  `EQC-035`.

| Touchpoint | Strongest pre-Stage 9C evidence | Gap Stage 9C was required to close |
|---|---|---|
| `EQC-009-REAL-COLUMNS-MEASUREMENT` | `realTopCombination_bottomWeight_of_rebit`, subsuming both canonical columns | no stable all-`Rebit` decoded-basis wrapper; the sector decoder was audit-local |
| `EQC-013-COMPLEX-COLUMNS-MEASUREMENT` | `complexTopCombination_bottomWeight_of_qubit`, subsuming both canonical columns | no stable all-`Qubit` decoded-basis wrapper; no reduced-density conclusion follows |
| `EQC-032-C2R-OBSERVABLE` | `realifyCircuitOutput_bottomProbability` for every locally unitary circuit, normalized source input, and `Rebit` | no all-top decoded-basis relation with the full added-wire outcome carrier visible |
| `EQC-035-Q2C-OBSERVABLE` | `complexifyCircuitOutput_bottomProbability` under the analogous quaternionic hypotheses | the same missing relation-valued wrapper and explicit decoder |
| `EQC-038-POSTPROCESSING-SIMULATION` | primary bottom-distribution, event, and deterministic-pushforward equalities | target distributions were already marginalized; an `id` decoder would erase the target carrier and marginal policy |
| outcome slice of `EQC-036-SCHEDULED-Q2C` | outcome conjunct of `scheduledQuaternionToComplex_exactSimulation` | no separately named supplied-schedule outcome relation; the old conjunction carries an irrelevant arity premise |
| outcome slice of `EQC-037-Q2R-COMPOSED` | `quaternionToRealCircuitOutput_bottomProbability` | no explicit two-wire relation, full target distribution, event theorem, or postprocessing theorem |

- `DecodedBasisWeightAgreement`, `DecodedDistributionAgreement`, their
  composition and event/pushforward consequences, and both `AllTop...`
  quantifier policies already compile in `Semantics/Simulation.lean`.
- `Simulation/Postprocessing.lean` now packages normalized source and full
  target distributions, refactors the primary bottom distributions through the
  explicit decoder, and exports the composed quaternion-to-real distribution,
  finite-event, and deterministic-pushforward closure.
- `FiniteDistribution.pushforward` can express forgetting the added wire via
  `Circuit.tailBits`. Independently, the explicit false/true sector formula
  makes a direct decoder constructive and normalization-preserving. A second
  strict-compiling probe at `/private/tmp/Stage9CRelationsProbe.lean` proves
  that the direct decoder equals `pushforward tailBits`, so this desired
  identification has no remaining proof obstruction.
- The strict-compiling prototypes
  `/private/tmp/Stage9CDecoderProbe.lean` and
  `/private/tmp/Stage9CRelationsProbe.lean` established the decoder and wrapper
  architecture before promotion. The repository implementation now provides
  the corresponding stable API, concrete consumers, direct release-audit
  endpoints, and downstream checks.

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
  4. `realifyCircuit_allRebit_decodedDistributionAgreement`;
  5. `realifyCircuit_decodedEventWeight_eq`;
  6. `realifyCircuit_decodedPushforward_eq`;
  7. `complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`;
  8. `complexifyCircuit_allQubit_decodedDistributionAgreement`;
  9. `complexifyCircuit_decodedEventWeight_eq`;
  10. `complexifyCircuit_decodedPushforward_eq`;
  11. `scheduledComplexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`;
  12. `scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement`;
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
- Use the stable explicit decoders in all new Stage 9C consumers. Retain the
  four historical Stage 9A `id` diagnostics only where they compare
  already-decoded same-carrier distributions; do not select them as Stage 9C
  endpoints or closure evidence. Add five disjoint aggregates allocating the
  18 semantic wrappers exactly as `2 + 4 + 4 + 4 + 4`: representative,
  complex-to-real, quaternion-to-complex, scheduled quaternion-to-complex, and
  composed quaternion-to-real outcomes.
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

- Added the low-dependency stable decoder leaf
  `QuaternionicComputing/Simulation/OutcomeDecoder.lean` with exactly ten
  public declarations and two private helper lemmas. Its explicit one-wire
  distribution decoder sums the false/true sectors and is proved equal to
  deterministic `pushforward tailBits`; its two-wire decoder removes the outer
  realification wire before the inner complexification wire.
- Extended `Simulation/Postprocessing.lean` with exactly eight new public
  full-target/composed declarations. Primary bottom distributions now use the
  explicit full-target decoder, and the composed quaternion-to-real family has
  normalized distribution, finite-event, and deterministic-pushforward
  closure.
- Added `Semantics/SimulationOutcomes.lean` with exactly 18 stable wrappers.
  The five Stage 9C-owned families `EQC-009`, `EQC-013`, `EQC-032`, `EQC-035`,
  and `EQC-038` are closed, and the outcome slices of `EQC-036` and `EQC-037`
  are added without changing their Stage 9B operator/state classifications.
  Raw point wrappers quantify every raw source column and need no unitarity;
  normalized distribution/event/pushforward wrappers retain normalized source
  states and the exact local-unitarity hypotheses. Scheduled wrappers retain
  the supplied schedule and gates.
- Extended the non-root `SimulationAudit` with two infrastructure aggregates
  allocating the decoder/postprocessing APIs as `10 + 8` and five semantic
  aggregates allocating the 18 wrappers as `2 + 4 + 4 + 4 + 4`. Concrete
  consumers exercise both canonical tops, a genuine quaternionic `j`, actual
  locally unitary zero-wire scalar circuits, the supplied `iThenJ` schedule,
  finite events, Boolean pushforwards, and the nested decoder order. Four
  historical Stage 9A same-carrier `id` diagnostics remain diagnostic-only and
  are not Stage 9C exports, manifest entries, selected endpoints, or evidence.
- Stable imports remain narrow: the decoder leaf has two public imports, the
  postprocessing leaf has two, and the semantic wrapper leaf has three. No
  stable Stage 9C leaf imports an audit, and the public root exports only the
  stable outcome leaf.
- Focused builds pass at `2347`, `2361`, `2365`, and `2385`; the final combined
  decoder/postprocessing/outcome/audit/public-root/release-audit build passes
  at `2769/2769`, and the cached default build completes `2767` jobs. Direct
  warning-as-error checks pass for every touched leaf, the audit, public root,
  and release audit. Public-root downstream, postprocessing-compatibility,
  relation, and concrete-audit probes all strict-compile.
- The semantic manifest contains 1,100 unique declarations, 140 consumers, and
  308 direct audit labels. The last 36 entries have exact source order, owner,
  seven nonempty axes, direct-audit intersection, and allocation
  `10 / 8 / 2 / 4 / 4 / 4 / 4`. Generated checks resolve all 1,100 public names
  and all 140 consumers. The preserved first-1,064 hash is
  `ece77e3bd826d5f2db8cc63d14a6733910c5563cb473c5f518111eaccdfcade4`;
  the full-1,100 hash is
  `d98dc2ee741dd792c204e088c396c7cbf95b1cc02f98fadceeccf94938da0870`;
  the frozen Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- Axiom parsing covers all 494 root blocks as `491 + 3` and all 20 local blocks
  as `19 + 1`. Every endpoint uses a subset of the permitted standard axioms,
  and both collective unions are exactly `propext`, `Classical.choice`, and
  `Quot.sound`, with no unknown declaration or `sorryAx`. Independent review
  found one newly introduced 101-character audit line; placing the unchanged
  fully qualified target at column zero repaired the strict style failure and
  preserved exact manifest/audit identity.
- Hole, declaration-axiom, unsafe, opaque, heartbeat, false-upgrade,
  import-boundary, tracked-artifact, stale-wording, Markdown table/fence,
  whitespace, diff, and frozen-checksum checks pass. README, public docstring,
  architecture, conventions, API notes, classification, traceability,
  corrections, release/axiom reports, and Goal 3 record the exact scopes and
  counts. Stage 9C adds no paper correction and no product/mixed-top, partial-
  trace, channel/all-effect, randomized, resource, compiler, or schedule-choice
  claim.
- Independent source, semantic, manifest, documentation, Goal 3, and integrated
  milestone reviews returned **PASS**. Stage 9C and the umbrella Stage 9
  cross-model classification are complete.

## Completion Status

- [x] Stage 9C is complete. Stage 9 is complete; Stage 10 is next.
