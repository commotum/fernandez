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

- In progress.
