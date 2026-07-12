# 9A-RELATIONS

## Current Facts

- Stages 1--8 are independently closed. The current checkpoint has 84 Lean
  sources including the public root, 990 exact Goal 2 semantic-manifest
  entries, 116 resolving consumers, 236 direct manifest/root-audit labels,
  and 422 root axiom commands. The exact release union remains `propext`,
  `Classical.choice`, and `Quot.sound`.
- The frozen Goal 1 cohort assigns 18 comparison families to Stage 9:
  `EQC-007`, `008`, `009`, `011`, `012`, `013`, `019`, `025`, `030`--`038`,
  and `040`. Stage 9A directly owns the two representative-encoding families
  `EQC-007-REAL-COLUMNS-REPRESENTATIVE` and
  `EQC-011-COMPLEX-COLUMNS-REPRESENTATIVE`; its relation vocabulary must also
  support the 11 Stage 9B and five Stage 9C families without classifying them
  prematurely.
- Existing source theorems already prove exact complex-to-doubled-real and
  quaternion-to-doubled-complex column encodings, left inverses/injectivity,
  normalization, inner-product facts, arbitrary pure-top combinations, exact
  matrix/circuit intertwining, and decoded bottom weights. They are typed
  across different scalars and index spaces and therefore cannot inhabit
  `ExactStateEq`, `ExactOperatorEq`, `ExactCircuitEq`, ray equality, or the
  same-space channel relations.
- `realifyCircuit`, `complexifyCircuit`, and the composed
  `quaternionToRealCircuit` change the wire type by one or two explicit
  `AddedWire`s. Their operator equalities are already stated through
  `wireRealify`/`wireComplexify`; their normalized outcome theorems quantify
  over every supplied normalized pure top state and marginalize the added
  top assignment before comparing bottom probabilities.
- `FiniteDistribution`, event weights, and deterministic pushforwards are
  already stable. Stage 8 proves equality iff all finite events and iff all
  same-universe finite pushforwards, but these same-space characterizations do
  not themselves name a directional decoder between different outcome types.
- No existing result supplies a cross-model joint-density encoder, partial
  trace, mixed or entangled top input, cross-model channel equality, all-effect
  equality, randomized postprocessor, finite-precision bound, schedule choice,
  compiler existence, or primitive synthesis theorem.

## Updated Assumptions

- Cross-model predicates are directional certificates parameterized by the
  actual encoder/embedding/decoder. They are not symmetric relations on one
  carrier and must not receive `Equivalence`, `[refl]`, `[symm]`, or `[trans]`
  declarations that hide type or policy changes.
- Exact operator embedding should compare a target operator with a named map
  of the source operator. Exact state intertwining should expose both source
  and target evolution plus the input/output encoders; it must not be defined
  as a wrapper around the theorem being classified.
- Decoded basis-weight and distribution relations should expose the marginal
  or decoder as data. A pure-top policy must quantify over the actual normalized
  top-state type (`Rebit` or `Qubit`) rather than a Boolean basis label. It must
  not imply mixed-top or arbitrary joint-state behavior.
- Representative encoding, operator embedding, state intertwining, decoded
  basis weights, decoded distributions, events, and postprocessing remain
  separate relation levels. Later wrappers may compose them, but one level is
  never silently promoted to another.
- The most general signatures that strict-compile with real consumers will be
  exported. Avoid algebraic typeclass assumptions when a function-level
  directional relation suffices, but retain matrix-specific types where they
  materially prevent an ill-typed or vacuous certificate.

## Big Picture Objective

Create a small reusable vocabulary for exact directional simulations between
different scalar/index spaces. Apply it immediately to the existing real and
complex representative encodings so Stage 9B can classify operator/state
intertwining and Stage 9C can classify decoded outcomes without reusing a
same-space equality name or hiding top/marginal policy.

## Detailed Implementation Plan

- Add a narrow `QuaternionicComputing/Semantics/Simulation.lean` leaf. Define
  directional predicates for:
  - exact target-operator equality after a supplied source embedding;
  - exact state evolution intertwining through supplied input/output encoders;
  - equality of a decoded target basis-weight function with a source basis-
    weight function;
  - equality of a decoded target finite distribution with the source finite
    distribution;
  - all-normalized-pure-top versions whose top type and encoding/marginal are
    explicit arguments.
- Give each predicate transparent introduction/elimination lemmas and only the
  composition laws that preserve the visible order of embeddings, encoders,
  and decoders. Do not manufacture symmetry or a same-space equivalence
  instance.
- Add real consumers using `realColumn0`, `realColumn1`, and normalized
  `realTopState`; add quaternion-to-complex consumers using `complexColumn0`,
  `complexColumn1`, and `complexTopState`. These consumers should prove the
  representative encoders are injective/normalized and instantiate the policy
  types without claiming ray descent.
- Probe empty and singleton source-index types. Empty normalized state types
  are uninhabited; do not pass impossible values merely to exercise a generic
  theorem.
- Record exact theorem allocation in a non-root Stage 9 audit leaf only after
  the stable relation file compiles. Stage 9B/9C may extend that audit rather
  than importing it into stable modules.
- Append every stable new declaration exactly once to the Goal 2 semantic API
  manifest only after a named consumer compiles; preserve the first-990 prefix
  and frozen Goal 1 checksum.

## Build Structure

- `QuaternionicComputing/Semantics/Simulation.lean`: low-dependency stable
  directional relation vocabulary and elementary composition/elimination
  laws. It may import `Semantics.Measurement` and `State.Distribution`, but not
  concrete circuit translators, audits, channels, or the public root.
- `QuaternionicComputing/Semantics/SimulationAudit.lean`: non-root consumers
  for the complete Stage 9 relation/wrapper surface and negative scope checks.
  In 9A it may begin with representative-encoding consumers, but it remains
  outside the public root.
- High-fanout state, matrix, circuit, existing simulation, channel, and
  hierarchy leaves remain unchanged. Later milestones add narrow wrapper
  leaves rather than editing the Goal 1 theorem sources.
- Focused builds target the new stable relation leaf and audit consumer.
  Adjacent probes import `State.Realification`, `State.Complexification`,
  `Simulation.ComplexToReal`, and `Simulation.QuaternionToComplex` only as
  needed.

## Boundary Checks

- Compared source and target carriers, scalars, row/column indices, and added
  wires remain explicit in every predicate.
- `ExactOperatorEmbedding`-style certificates are directional mapped
  equalities, not `ExactOperatorEq` or `ExactCircuitEq`.
- State intertwining compares amplitude evolution after an encoder. It is not
  ray equality and does not descend through a quotient unless a separate
  theorem proves phase compatibility.
- A decoded bottom-weight relation quantifies only over computational-basis
  outcomes. A decoded distribution adds finite normalization; event and
  deterministic-postprocessing consequences remain separate.
- A top parameter ranges over normalized pure top states only. No theorem may
  accept or imply a mixed top density, an entangled source/top state, or a
  partial trace.
- Algebraic `EquivImage`/`MulEquiv` declarations remain nonbehavioral image
  isomorphisms. Reindexing equality remains equality after the named row and
  column equivalences.

## No-Cheating Checks

- Do not define a relation by naming a particular existing theorem or bundle
  operator, state, outcome, and resource conclusions into one opaque label.
- Do not add `Equivalence` instances, symmetric notation, or simplification
  rules that erase encoder/decoder direction.
- Do not use an impossible normalized empty state/top hypothesis or a vacuous
  universal quantifier as a consumer.
- Do not infer same-space equality, ray equality, channel/all-effect equality,
  mixed-top behavior, schedule independence, compiler existence, or runtime.
- No `sorry`, `admit`, `sorryAx`, declaration axiom, `opaque`, `unsafe`,
  heartbeat override, public audit import, or silent frozen-cohort change.

## Completion Requirements

- Every stable relation has a compiling introduction/elimination interface and
  a real cross-model consumer; no unused abstraction counts as completion.
- The two 9A cohort families have proof-bearing strongest classifications that
  expose their scalar/index change, representative scope, exactness, phase,
  and top-sector policy.
- Directional composition laws retain explicit embedding/encoding/decoder
  order and no false equivalence instance is present.
- Empty/singleton boundaries, representative injectivity/normalization, and
  the absence of ray/channel/mixed-top upgrades are checked in the non-root
  audit.
- Focused, adjacent, public-root, warning-as-error, manifest-name/consumer,
  axiom, forbidden-token/import-boundary, frozen-checksum, whitespace, and diff
  checks pass before 9A is marked complete.
- Exact results are folded into `goal-2/0-plan.md`, the Stage 9B/9C current
  facts, documentation, and Goal 3 without marking the 16 dependent Stage 9
  cohort families final early.

## Stage Results

- In progress. Relation signatures are being independently probed against the
  existing realification and complexification APIs before public names are
  fixed.
