# 4B-DESCENT

## Current Facts

- Goal 2 Stages 1--3 and milestone 4A are complete. The public tree has 59
  Lean sources, 424 Goal 2 manifest entries, 50 resolving diagnostic
  consumers, 86 direct root-audit targets, and 272 root audit commands. The
  frozen 936-declaration Goal 1 cohort checksum remains unchanged.
- `State.RealRay`, `State.ComplexRay`, and `State.QuaternionRay` quotient
  normalized representatives by real sign, complex unit right phase, and
  quaternion unit right phase respectively. Each quotient has constructor
  equality, induction, and proof-checked lifting, but no public descended
  dynamics or observable API yet.
- Representative-level phase invariance is already available without the
  semantic wrapper layer: all three phase relations preserve basis weights and
  commute with arbitrary compatible matrix action. `State.Unitary` packages
  normalized unitary evolution for all three scalar types.
- `State.FiniteDistribution` already packages normalized finite outcome
  weights, finite events, and deterministic pushforwards. It lacks the public
  functor laws `pushforward_id` and `pushforward_comp` required by the ray API.
- `Circuit.OrderedCircuit.eval` uses chronological lists with
  `eval (C ++ D) = eval D * eval C`. Local unitarity supplies a unitary
  evaluator, but append closure is not yet a named public theorem.
- Strict all-scalar probes at `/tmp/Stage4BProbe.lean`,
  `/tmp/Stage4BAllScalarProbe.lean`, `/tmp/Stage4BObservablesNarrow.lean`, and
  `/tmp/Stage4BEvolutionNarrow.lean` validate the intended quotient descent,
  beta laws, identity/composition laws, proof irrelevance, and semantic
  bridges without adding a nonempty-index hypothesis.
- The correct evolution order is theorem-checked: applying `U` and then `V`
  is the action of `V * U`; applying a chronological append `C ++ D` is first
  `C` and then `D`. This remains significant over quaternions, where the
  multiplication order cannot be commuted.
- Empty finite index types have no rays by Stage 4A, so operations out of those
  domains are sound but vacuous. Circuit state indices are `BitBasis W`, which
  remain inhabited even when `W` is empty; zero-wire circuit evolution is
  therefore nonvacuous.

## Updated Assumptions

- Keep observable descent independent of unitary evolution and circuits.
  `State/RayObservables.lean` should import only the quotient and generic
  distribution-law leaves.
- Keep normalized evolution independent of `Semantics.StatePhase`: the raw
  state-layer phase-preservation lemmas already prove representative
  independence. A separate tiny `Semantics/Ray.lean` should expose exactly the
  three normalized-state-phase/quotient-equality bridges.
- Put deterministic-pushforward identity and composition in a narrow
  `State/DistributionLaws.lean` leaf rather than making ray users depend on
  audit or semantics modules.
- Put append closure of `OrderedCircuit.IsLocallyUnitary` in a narrow
  `Circuit/LocalUnitary.lean` leaf rather than editing the high-fanout circuit
  core solely for this stage.
- Descend only normalization-preserving actions. Arbitrary matrix action
  respects the raw phase relation but need not preserve total weight, so it
  does not define a map between normalized ray types.
- Do not state that unitary evolution preserves a computational-basis
  distribution. It generally changes the distribution; the quotient proof
  only says the result is independent of the chosen phase representative.
- The two transferred paper rows remain open after 4B until 4C proves the
  embedding-orbit boundary. Stage 4B must record its exact evidence without
  prematurely assigning `closedByGoal2`.

## Big Picture Objective

Make normalized rays operational: descend computational-basis observables,
finite events, deterministic classical postprocessing, unitary evolution, and
locally-unitary chronological circuit evolution to all three quotient types,
with representative beta laws and exact identity/composition laws.

## Detailed Implementation Plan

- Add `State/DistributionLaws.lean` with generic
  `FiniteDistribution.pushforward_id` and `pushforward_comp`.
- Add `Circuit/LocalUnitary.lean` with
  `OrderedCircuit.IsLocallyUnitary.append`.
- Add `State/RayObservables.lean`. In each of `RealRay`, `ComplexRay`, and
  `QuaternionRay`, expose:
  - `distribution` and `distribution_mk`;
  - `basisWeight`, `basisWeight_mk`, and `distribution_weight`;
  - `eventWeight` and `eventWeight_mk`;
  - `pushforward`, `pushforward_mk`, `pushforward_id`, and
    `pushforward_comp`.
- Add `State/RayEvolution.lean`. In each ray namespace, expose:
  - `evolveUnitary`, its constructor beta law, identity law, and ordered
    composition law;
  - `evolveCircuit`, its constructor beta law, empty-circuit identity law,
    and chronological append law.
- Add `Semantics/Ray.lean` with explicit iff bridges between constructor
  equality and `RealStatePhaseEq`, `ComplexStatePhaseEq`, and
  `QuaternionStatePhaseEq`.
- Add non-root `State/RayDescentAudit.lean` with aggregate consumers covering
  every stable declaration, concrete rebit/qubit/quaterbit observable and
  evolution checks, the quaternionic ordered-composition check, a zero-wire
  circuit check, and representative axiom prints.
- Promote only the five stable leaves through `QuaternionicComputing.lean`;
  never import the audit leaf from the public root. Add every stable public
  declaration exactly once to `Goal2SemanticAPIManifest.json`, with all seven
  axes, resolving consumers, and representative direct root-audit endpoints.
- Fold the completed descent surface and still-open 4C boundary into all
  affected documentation, traceability, release evidence, and the Goal 3
  prerequisite forecast.

## Build Structure

- `State/DistributionLaws.lean`: generic deterministic-pushforward laws;
  stable proof API, no ray dependency.
- `Circuit/LocalUnitary.lean`: append closure for locally-unitary chronological
  circuits; stable proof API, no ray dependency.
- `State/RayObservables.lean`: stable quotient observables, importing only
  `State.Ray` and `State.DistributionLaws`.
- `State/RayEvolution.lean`: stable normalized quotient dynamics, importing
  `State.Ray`, `State.Unitary`, and `Circuit.LocalUnitary`.
- `Semantics/Ray.lean`: stable semantic iff bridges, importing only
  `State.Ray` and `Semantics.StatePhase`.
- `State/RayDescentAudit.lean`: non-root diagnostics, consumers, examples,
  and local axiom inspection.
- Focused builds target each new leaf directly. Adjacent builds target
  `Semantics.StatePhase`, `Circuit.Basic`, the public root, and the explicit
  root axiom audit. Strict source checks cover every new file.

## Boundary Checks

- Each operation is defined by `Quotient.lift` with an explicit proof that it
  is independent of the phase representative; no representative choice is
  exposed.
- Real sign, complex right phase, and quaternion right phase stay distinct.
  Quaternionic descent never changes the phase to the left or commutes matrix
  factors.
- `evolveUnitary` accepts a square matrix with an explicit membership proof in
  the unitary subgroup. `evolveCircuit` accepts a locally-unitary certificate.
  No arbitrary matrix or uncertified circuit is claimed to preserve rays.
- Observable descent means equality under change of representative, not
  invariance under arbitrary dynamics, equality of rays from equal
  distributions, channel equality, or all-effect measurement equality.
- The circuit append law follows the repository's chronological convention;
  no reversal or commutative simplification is hidden.
- All APIs are same-scalar/same-index. No complex-to-real or
  quaternion-to-complex ray map is introduced in 4B.

## No-Cheating Checks

- Do not define an observable through a chosen quotient representative.
- Do not use proof irrelevance as a substitute for proving phase invariance of
  representative data.
- Do not quotient by distribution equality, use left quaternion phase, or
  smuggle a nonzero scalar relation into normalized rays.
- Do not return a normalized ray after arbitrary matrix action without a
  normalization-preservation certificate.
- Do not describe `distribution (evolveUnitary r U hU)` as equal to
  `distribution r`; only representative independence is valid.
- Do not turn pushforward into a randomized or runtime-complexity claim.
- No `sorry`, `admit`, `sorryAx`, new axiom, unsafe/opaque shortcut, heartbeat
  override, impossible hypothesis, public audit import, or metadata-only
  classification.

## Completion Requirements

- All three ray types expose basis weights, normalized distributions, finite
  event weights, deterministic pushforwards, unitary evolution, and
  locally-unitary circuit evolution with representative beta laws.
- Pushforwards satisfy identity and ordered composition. Unitary evolution
  satisfies identity and `U`-then-`V = V * U`; circuit evolution satisfies
  empty identity and `C ++ D = C`-then-`D`.
- The three semantic phase relations are explicitly iff quotient-constructor
  equality.
- A non-root audit consumes every stable declaration and includes real,
  complex, quaternionic, noncommutative-order, and zero-wire sanity checks.
- Manifest exact-set, seven-axis, public-name, consumer-resolution,
  direct-audit, preserved-prefix, and frozen-checksum checks pass.
- Focused, adjacent, public-root, explicit-audit, warning-as-error,
  forbidden-token, diagnostic-boundary, artifact, whitespace, and
  `git diff --check` verification passes under `BUILD-PLAN.md`.
- Documentation records the exact 4B surface while leaving the realification
  orbit boundary and both transferred-row closure decisions to 4C.

## Stage Results

- `State/DistributionLaws.lean` adds the two scalar-neutral deterministic
  postprocessing laws `FiniteDistribution.pushforward_id` and
  `pushforward_comp`. The latter proves exactly that one pushforward through
  `g ∘ f` is first `f` and then `g`, by a finite fiber-sum rearrangement.
- `Circuit/LocalUnitary.lean` adds
  `OrderedCircuit.IsLocallyUnitary.append`; its proof splits membership in
  `C ++ D` and reuses the two supplied gatewise certificates. Neither helper
  leaf depends on rays or semantic comparison modules.
- `State/RayObservables.lean` contributes 33 stable declarations: for each of
  `RealRay`, `ComplexRay`, and `QuaternionRay`, `distribution`, `basisWeight`,
  `eventWeight`, and `pushforward` descend to quotient values, with
  representative beta laws, the named distribution-weight projection, and
  deterministic identity/composition laws. The distribution lift is justified
  by the existing scalar-specific basis-weight invariance theorem and
  `FiniteDistribution.ext`; it never chooses a representative.
- `State/RayEvolution.lean` contributes 24 stable declarations. Each scalar
  ray has `evolveUnitary` with representative, identity, and ordered
  composition laws, plus `evolveCircuit` with representative, empty-circuit,
  and chronological-append laws. Only explicitly unitary matrices and
  locally-unitary circuits act on normalized rays. The exact checked order is
  first `U`, then `V`, equals `V * U`; `C ++ D` acts first by `C`, then by `D`.
  The quaternionic proofs use `Matrix.mulVec_mulVec` without commuting either
  matrix or phase factors.
- `Semantics/Ray.lean` contributes exactly three stable iff bridges:
  `RealStatePhaseEq.iff_realRay_mk_eq`,
  `ComplexStatePhaseEq.iff_complexRay_mk_eq`, and
  `QuaternionStatePhaseEq.iff_quaternionRay_mk_eq`. They identify the already
  named normalized representative relations with literal constructor equality
  in the corresponding quotient, preserving quaternion phase strictly on the
  right.
- `State/RayDescentAudit.lean` is non-root and has four complete aggregate
  consumers. `sharedDescent_api` covers the three helper declarations; the
  real, complex, and quaternion aggregate consumers cover 20 declarations
  each, for exact coverage of all 63 stable Stage 4B declarations. Concrete
  rebit, qubit, and quaterbit checks exercise weights, events,
  postprocessing, and identity evolution. The existing `i`/`j` ordering
  witness proves exact distinct descended quaternionic outcome weights and
  checks singleton append chronology. Empty amplitude indices remain empty,
  while zero-wire `BitBasis Empty` rays and circuit actions are nonvacuous;
  proof-argument irrelevance is checked explicitly.
- The public root imports the five stable leaves transitively and never imports
  `RayDescentAudit`. The root overview now describes operational rays without
  promoting them to channel equality or cross-model maps. The explicit root
  audit adds 14 representative endpoints and now contains 286 commands. All
  ten audit-local prints and all root prints report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `docs/Goal2SemanticAPIManifest.json` now contains exactly 487 entries: the
  structurally preserved first 424 plus 63 source-ordered Stage 4B entries.
  All entries have the seven required axes. Consumer allocation is exactly
  `3/20/20/20` across the four new aggregates; there are 54 distinct consumers
  and 100 direct root-audit entries overall. The compact structural hash of
  the first 424 entries is
  `69c67f52353597158718bfa30d47a3fbf10216edb3d3344ca293a4a50c671b11`.
  Generated strict Lean checks resolve all 487 public names and all 54
  consumers.
- The independent manifest validator reports
  `source=487 manifest=487 missing=0 extra=0 axes=7 consumers=54 direct=100`
  with `stage4B=63/4/14`; it also checks exact source order, duplicates,
  required fields, consumer textual exercise, direct-target labels,
  quaternion right phase, no channel/distribution-invariance overclaim,
  `V * U`/append chronology, prior-stage invariants, preserved prefixes, and
  the frozen cohort checksum. The Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- Focused helper builds pass at 2,348 jobs and the non-root descent audit at
  2,361 jobs. The public root and standalone explicit audit each pass at 2,568
  jobs; the combined five-public-leaf, diagnostic, root, and audit build passes
  at 2,570 jobs. Warning-as-error source checks pass for every new leaf, the
  diagnostic, and the touched public root. The current tree has 65 Lean
  sources including the root.
- Forbidden proof-hole/project-axiom/unsafe/opaque/heartbeat, representative-
  choice, State-to-Semantics reverse-dependency, public-diagnostic-import,
  stale-path, generated-artifact, whitespace, and `git diff --check` checks
  pass. No new correction was required.
- Documentation now records the descended operations, exact assumptions,
  empty/zero-wire distinction, and ordered laws. `FER03-D01-REBIT` and
  `FER03-FND-COMPLEX-STATE-RAY` remain **partially formalized**, not
  `closedByGoal2`: Stage 4C must still prove the realification embedding-orbit
  boundary before those transferred rows close.
- An independent requirement-by-requirement closure review returned **PASS**:
  it reproduced the declaration arithmetic `2 + 1 + 33 + 24 + 3 = 63`,
  aggregate allocation `3/20/20/20`, manifest and generated-name checks,
  2,570-job combined build, strict source checks, exact axiom set, dependency
  and diagnostic boundaries, shortcut/artifact/whitespace scans, documentation
  status, and frozen checksum with no blocker.
