# Goal 3 — Verified Computational and Operational Completion

Shorthand: `QC-COMPLETE`

## Scope Reset

This scaffold supersedes the previous 20-stage Goal 3 plan. Goal 2 is complete
and has already supplied the semantic distinctions needed to state the
remaining mathematics correctly. Goal 3 now has one focused purpose:

> Complete the reusable computational and operational core of *Quaternionic
> Computing*: turn the existing exact finite simulations into encoded,
> approximate, synthesized, resource-aware, and uniform results, and add the
> minimum native quaternionic mixed-state/channel theory needed to state and
> verify operational simulation claims.

The paper's speculative questions about protocols, physicality, multipath
computation, and alternative scalar algebras are not silently discarded. They
are an explicit research frontier, but settling every such open program is no
longer allowed to block the core Goal 3 release. Stage `12-FRONTIER` must give
each one an exact model requirement, obstruction, dependency path, and future
theorem target.

This is an intentional scope change authorized by the request to rebuild Goal
3 after reviewing whether the old scaffold should still be pursued. It is not
a claim that the excluded research questions have been solved.

## Big-Picture Objective

The completed library already proves exact finite real/complex/quaternionic
state, operator, circuit, measurement, and directional simulation results. It
does not yet prove that those simulations are executable on finite input,
stable under rounding, compiled from a constructed finite gate library,
uniform in input size and precision, or efficient in a machine model. It also
lacks native quaternionic densities, effects, partial trace, Kraus-style
channels, and the operational comparisons needed for the paper's mixed-state
and information-theoretic language.

Goal 3 closes that gap. It must:

1. freeze the exact remaining work against the completed Goal 2 release;
2. resolve the central algebraic and ordering/resource proof gaps;
3. construct the missing quaternionic mixed-state and channel layer;
4. define executable finite encodings, rounding, compilation, and resource
   models;
5. prove a complete exact-to-approximate-to-uniform simulation theorem, or the
   strongest useful corrected theorem supported by checked obstructions;
6. turn every remaining interpretive or open source question into a precise,
   traceable research problem without presenting it as a proved result; and
7. publish a clean, reusable, audited release.

If a paper claim is false or underspecified, success means a decisive
counterexample, corrected theorem, or formal underdetermination result—not a
weakened statement presented under the original name.

## Authoritative Inputs

- `Fernandez/fernandez-2003.md` and `Fernandez/images/` are the local paper
  source.
- `docs/Traceability.md` is the canonical 101-row paper-to-Lean inventory.
- `docs/Corrections.md` records the 27 current source and scope corrections.
- `docs/ReleaseReport.md`, `docs/Architecture.md`, and `docs/Conventions.md`
  describe the released library.
- `goal-1/` is the completed paper reconstruction.
- `goal-2/` is the completed semantic-equivalence retrofit and a hard
  prerequisite. Goal 3 must reuse its relations rather than create competing
  local predicates.
- `docs/Goal1ComparisonCohort.json` and its sidecar checksum are immutable
  historical inputs.
- `docs/Goal2ClassificationRegistry.json` and
  `docs/Goal2SemanticAPIManifest.json` are the checked Goal 2 classification
  and public semantic surfaces.
- Repository-root `BUILD-PLAN.md` is mandatory for every Lean-changing stage.
- Later primary literature may be used to repair, prove, or refute source
  claims, but every imported theorem must be independently restated with the
  assumptions required by the local model.

## Current Facts and Assumptions

- Lean is pinned to 4.31.0 and mathlib v4.31.0 at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Goal 2 Stages 1–12 are complete. Its final release has 102 Lean sources
  including the public root, 1,290 semantic-manifest declarations, 169
  resolving consumers, 371 direct audit labels, and 557 root axiom commands.
- The Goal 2 validator passes at 51 families, 936 frozen declarations, ten
  empty families, 1,290 semantic declarations, 169 consumers, 371 direct
  audits, and seven semantic axes.
- The frozen cohort checksum is
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
  The final Goal 2 semantic-manifest hash is
  `49a2ad069b61bdb9fbd6a3a6175265781867d7a71a3a7d996b5cd0df283766b4`.
- Goal 2's final root/local axiom union is exactly `propext`,
  `Classical.choice`, and `Quot.sound`. No project-specific axiom or proof hole
  is present in completed modules.
- The current 101-row traceability disposition is 23 proved as stated, 33
  corrected and proved, 26 partially formalized, 16 intentionally excluded,
  and 3 unresolved.
- Before Goal 2 there were 47 non-fully-proved rows. Goal 2 closed
  `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY`, leaving a forecast of 45
  rows: 26 partial, 16 excluded, and 3 unresolved.
- By default, all 29 partial or unresolved rows are Goal 3 core obligations.
  Moving one to the research frontier requires a checked impossibility or
  underdetermination result, or an explicit user-approved scope change.
- The 16 already excluded rows remain mandatory frontier-accounting items but
  are not all required to become full formal developments in Goal 3.
- Seven source-only semantic families, `EQC-045` through `EQC-051`, remain a
  separate no-skip ledger. They must be assigned to a core stage or the
  research frontier without changing the 47/45 traceability arithmetic.
- The previous Goal 3 contained only `0-plan.md`, `0-loop.md`, and
  `0-prompt.md`; no feature stage had begun. Replacing that scaffold therefore
  discards no completed Goal 3 implementation evidence.
- `docs/EquivalenceClassification.md` still names three owners from the
  superseded scaffold: old Stages 12/13 for `EQC-048`, old Stage 14 for
  `EQC-050`, and old Stages 14/16 for `EQC-051`. Stage 1 must update those
  cross-document owner labels to new Stages 10, 11, and 5/11 only after the
  executable worklist confirms the mapping. They are known handoff metadata,
  not current Goal 3 stage names.

Stage `1-REBASE` must recompute every count and assignment from the actual
files. The numbers above are release inputs, not permission to skip the
executable rebaseline.

## Non-Negotiable Constraints and No-Cheating Rules

- Never use `sorry`, `admit`, `sorryAx`, an unjustified axiom, an impossible or
  vacuous premise, or a definition engineered to make the target tautological.
- Do not close a traceability row by changing its label. Closure evidence must
  address the source claim or a clearly documented strongest correction.
- Preserve Goal 2's distinctions among exact equality, state ray, global
  phase, sided basis phase, projective action, basis behavior, measurement,
  channel behavior, cross-model simulation, and approximation.
- Quaternionic state and input-column phase multiply on the right;
  output-row phase multiplies on the left. Do not introduce an arbitrary
  unit-quaternion operator phase. Preserve the proved rank-one exception and
  central-sign higher-dimensional kernel.
- Do not use commutative tensor identities over quaternions. Every tensor,
  placement, adjoint, trace, and multiplication order must be checked.
- Do not impose an order on `ℍ` to reuse real/complex positive-semidefinite
  APIs. Native quaternionic positivity must use a justified real quadratic
  form, Hermitian spectral convention, or proved complexification criterion.
- A semantic reindexing is not a physical swap network. Routing gates must be
  emitted, evaluated, and counted.
- A supplied schedule, compiler, synthesis certificate, density certificate,
  or universal-set certificate is data—not an existence theorem or algorithm.
- Executable encoders, schedulers, compilers, and uniform generators must be
  computable definitions with evaluation tests. Noncomputable mathematics may
  support proofs but cannot stand in for runtime construction.
- Rounded entries are not automatically unitary. Any finite-precision path
  must include a proved projection, normalization, or synthesis step and must
  keep value error separate from code and runtime bounds.
- Fixed-budget approximation is not an equivalence relation. Triangle and
  composition theorems must expose accumulated budgets.
- A finite exact gate set, an approximately universal set, a uniform compiler,
  and an efficient compiler are four separate claims.
- A basis-only or one-input witness is not channel, signaling,
  entanglement, cryptographic, or complexity-class evidence.
- Do not infer physicality or a claim about Nature from a chosen mathematical
  definition. Such conclusions belong in the frontier unless a conditional
  theorem states every operational premise explicitly.
- Preserve the stable Goal 1/Goal 2 public APIs. New experimental machinery
  begins in narrow leaves and is promoted only after it has a real consumer,
  documentation, and axiom audit.
- Keep runtime/API, proof-side, diagnostic, fallback, and temporary modules
  distinct as required by `BUILD-PLAN.md`.
- A blocked proof must become a smaller proof obligation, counterexample
  search, alternate construction, or explicit frontier item. It may not simply
  disappear from the ledger.

## Required Closure Outcomes

Every core row must end in exactly one of these evidence-backed outcomes:

- **proved as stated**;
- **corrected and proved**;
- **refuted**, with a Lean counterexample and strongest useful replacement; or
- **formally underdetermined**, with two checked models satisfying the stated
  assumptions but disagreeing on the claim, or an equivalent precise
  independence result.

`partially formalized` and `unresolved` are not terminal Goal 3 core outcomes.
A core row may move to the research frontier only under the scope-change rule
above. Frontier rows retain their canonical traceability status until a future
goal supplies the missing mathematics.

## Provisional Core Ownership

Stage `1-REBASE` must verify this assignment against the canonical
traceability table. It contains each of the 29 default core rows exactly once:

| Stage | Default core rows | Count |
|---|---|---:|
| `2-ALGEBRA` | `FER03-T05-QUATERNION-COMPLEXIFICATION-GROUP`; `FER03-FND-REAL-PRESERVERS-ORTHOGONAL` | 2 |
| `3-ORDERING` | `FER03-FND-ARBITRARY-WIRE-ROUTING`; `FER03-R-TOPO-SORT-COMPLEXITY`; `FER03-Q-CUT-POSET` | 3 |
| `4-QDENSITY` | `FER03-R-PARTIAL-TRACE-BLOCK-SUM`; `FER03-R-ARBITRARY-TOP-REBIT`; `FER03-Q-ARBITRARY-TOP-QUBIT` | 3 |
| `5-QCHANNELS` | `FER03-INT-FREE-NONLOCAL-CORRELATION` | 1 |
| `6-FANOUT` | `FER03-R-REAL-GATE-OPTIMIZATION`; `FER03-R-MULTI-ANCILLA-LOG-DEPTH` | 2 |
| `7-ENCODING` | `FER03-R-LOCAL-GATE-COST`; `FER03-R-PREPROCESSING-COST`; `FER03-RES-UNIFORM-CIRCUIT-WITHOUT-UNIVERSAL-SET`; `FER03-RES-EXPLICIT-MATRIX-ARITY` | 4 |
| `8-ERROR` | `FER03-FND-FINITE-PRECISION` | 1 |
| `9-SYNTHESIS` | `FER03-RES-GENERIC-DECOMPOSITION`; `FER03-RES-CONSTANT-D`; `FER03-RES-ARBITRARY-D-OVERHEAD` | 3 |
| `10-UNIFORMITY` | `FER03-D02-REAL-ALGORITHM`; `FER03-D05-QUATERNIONIC-ALGORITHM`; `FER03-R-COMPUTATIONAL-UNIVERSALITY`; `FER03-RES-QUATERNIONIC-UNIVERSAL-SET`; `FER03-RES-ABSTRACT-LITTLE-OVERHEAD`; `FER03-INT-PREFERRED-PATH-BQP` | 6 |
| `11-STRUCTURE` | `FER03-FND-ANY-HILBERT-SCALARS`; `FER03-R-PHASE-TRACKING-INTERPRETATION`; `FER03-INT-QUATERNION-PHASE-QUBIT`; `FER03-INT-NOT-NPLUS1-REBITS` | 4 |
| **Total** | 26 partial plus 3 unresolved | **29** |

The seven source-only families have this provisional ownership:

| Family | Owner |
|---|---|
| `EQC-045-NORM-PRESERVER-CONVERSES` | `2-ALGEBRA` |
| `EQC-046-MIXED-TOP-OBSERVATIONAL` | `4-QDENSITY` |
| `EQC-047-QUATERNION-REDUCED-SEPARATION` | `4-QDENSITY` |
| `EQC-048-COMPUTATIONAL-MODEL-EQUIVALENCE` | `10-UNIFORMITY` |
| `EQC-049-PHYSICAL-SWAP-SIMULATION` | `3-ORDERING` |
| `EQC-050-TOP-WIRE-PHASE-TRACKING` | `11-STRUCTURE` |
| `EQC-051-OPERATIONAL-CONVERSE-SIMULATION` | `5-QCHANNELS`, then `11-STRUCTURE` |

The 16 baseline excluded rows have these provisional disposition paths:

| Path | Rows | Count |
|---|---|---:|
| Stage 2 prerequisite candidates | `FER03-FND-LINEAR-ISOMETRY-UNITARY`; `FER03-FND-FINITE-DIM-COMPLETE` | 2 |
| External computation result | `FER03-T01-BERNSTEIN-VAZIRANI-REAL-QTM` | 1 |
| Protocols and information theory | `FER03-INT-BIT-COMMITMENT`; `FER03-OPEN-QUATERBIT-TELEPORTATION`; `FER03-OPEN-CHANNEL-CAPACITY`; `FER03-OPEN-COMMUNICATION-COMPLEXITY`; `FER03-OPEN-REBIT-INFORMATION-THEORY` | 5 |
| Physical interpretation | `FER03-INT-RULE-OUT-PHYSICALITY` | 1 |
| Multipath and interference | `FER03-INT-DESTRUCTIVE-INTERFERENCE-CAUSE`; `FER03-OPEN-ALL-EVALUATION-PATHS`; `FER03-OPEN-PATH-WEIGHTS`; `FER03-OPEN-PATH-INTERFERENCE`; `FER03-OPEN-BEYOND-QUANTUM-SPEEDUP` | 5 |
| Alternative scalars and complexity | `FER03-OPEN-OTHER-SCALARS`; `FER03-OPEN-ALGEBRAIC-COMPLEXITY-PICTURE` | 2 |
| **Total** | Baseline intentionally excluded rows | **16** |

Baseline excluded background facts may be absorbed by a core stage when they
are small prerequisites, but they must still retain their own traceability IDs
and evidence. Every other row remains assigned to Stage 12 unless a core stage
produces a checked terminal result.

## Success Metrics and Final Verification

Goal 3 is complete only when:

- an executable worklist accounts for all 47 pre-Goal-2 rows as two
  `closedByGoal2` rows plus 45 Goal 3 rows, and separately accounts for all
  seven `EQC-045`–`EQC-051` families;
- all 29 default core rows have terminal closure outcomes and checked evidence;
- the 16 excluded rows have complete research-frontier specifications and no
  release prose implies they were proved;
- the quaternionic determinant, ordering/routing, density/channel, encoding,
  approximation, synthesis, uniformity, and structural obligations have the
  outcomes required by their stages;
- the library exposes an end-to-end theorem stack from exact mathematical
  simulation through encoded inputs, certified approximation, compiled
  circuits, decoded outcomes, and explicit resource bounds—or documents the
  exact checked obstruction to the strongest unavailable layer;
- main public results are directly covered by the executable axiom audit;
- representative downstream consumers import only the stable public root;
- focused, adjacent, strict warning-as-error, trust/audit, default, and final
  clean builds pass as required by the affected modules;
- source scans find no proof hole, project axiom, unsafe/opaque shortcut,
  unlimited-heartbeat escape, tracked generated artifact, or audit import in
  stable code;
- traceability, corrections, architecture, conventions, release report,
  worklist, frontier ledger, stage reports, and public names agree; and
- `git diff --check` and maintained Markdown structure checks pass.

## Dependency Shape

```text
1-REBASE
  ├──> 2-ALGEBRA
  ├──> 3-ORDERING ───────────────┐
  ├──> 4-QDENSITY -> 5-QCHANNELS│
  ├──> 6-FANOUT ─────────────────┤
  └──> 7-ENCODING -> 8-ERROR ────┤
                                  v
                             9-SYNTHESIS
                                  |
                                  v
                            10-UNIFORMITY

2-ALGEBRA + 5-QCHANNELS + 6-FANOUT + 10-UNIFORMITY
                         -> 11-STRUCTURE

all core stages -> 12-FRONTIER -> 13-RELEASE
```

Independent stages may proceed in parallel only when they do not edit the same
core modules or change a shared convention. Public-root promotion remains
serialized through the relevant stage's integration checks.

## Stage Index

1. `1-REBASE` — freeze the actual post-Goal-2 worklist and checker.
2. `2-ALGEBRA` — close determinant and finite-dimensional foundation gaps.
3. `3-ORDERING` — executable schedules, physical routing, and temporal cuts.
4. `4-QDENSITY` — native quaternionic densities, effects, and partial trace.
5. `5-QCHANNELS` — quaternionic channels and operational complex simulation.
6. `6-FANOUT` — real-gate optimization and multi-top depth/resource results.
7. `7-ENCODING` — executable scalar, circuit, schedule, and output encodings.
8. `8-ERROR` — certified rounding and accumulated semantic error.
9. `9-SYNTHESIS` — construct compilers and prove corrected resource bounds.
10. `10-UNIFORMITY` — uniform algorithms, universality, runtime, and BQP scope.
11. `11-STRUCTURE` — phase tracking, scalar structure, and converse boundaries.
12. `12-FRONTIER` — precise handoff for genuinely open research programs.
13. `13-RELEASE` — final clean build, audit, documentation, and reusable release.

## 1-REBASE

### Big Picture Objective

Replace every forecast with an executable, checksum-backed statement of the
actual work remaining after Goal 2.

### Detailed Implementation Plan

- Re-run the complete Goal 2 validator and record the public-root, audit,
  checksum, source-count, traceability, correction, and worktree baselines.
- Create `docs/Goal3Worklist.json` with all 47 pre-Goal-2 non-fully-proved IDs:
  two `closedByGoal2` entries and 45 Goal 3 entries.
- Give every Goal 3 entry its current status, source location, owning stage,
  dependencies, required closure outcome, primary proof route, fallback route,
  and concrete verification witness.
- Add a separate section for `EQC-045`–`EQC-051` without counting those
  families as additional traceability rows.
- Create `docs/RemainingWork.md` as the generated or mechanically checked human
  view of the worklist.
- Add a validator that checks IDs, counts, status arithmetic, ownership,
  correction links, source links, stage names, and absence of duplicates.
- Replace the superseded Goal 3 owner labels in
  `docs/EquivalenceClassification.md` from the validator-confirmed mapping;
  do not edit the frozen Goal 1 cohort.
- Re-read the primary source passages and identify later primary literature
  needed by the algebra, channel, synthesis, uniformity, and structural tracks.

### Completion Requirements

- The checker proves `47 = 2 + 45`, with the 45 rows partitioned exactly into
  26 partial, 16 excluded, and 3 unresolved at baseline.
- The seven Goal 2 source-only families occur exactly once in the separate
  boundary ledger.
- Every default core row is assigned to Stages 2–11; every excluded row is
  assigned to a core stage or Stage 12 with an explicit reason.
- Goal 2 counts, hashes, checksum, build evidence, and axiom union reproduce.
- The worklist and human view are generated from or checked against one source
  of truth.
- Focused validator tests, Markdown checks, and `git diff --check` pass.

## 2-ALGEBRA

### Big Picture Objective

Close the finite-dimensional algebraic facts on which the corrected simulation
and complexity statements depend.

### Detailed Implementation Plan

- Settle the remaining quaternion-complexification determinant-one branch using
  the narrowest justified route: symplectic determinant, Pfaffian congruence,
  connectedness, Study determinant positivity, or a checked counterexample.
- Export the strongest corrected special-unitary image theorem and propagate
  its exact target dimension and assumptions.
- Close the finite-dimensional linear-isometry/unitary, completeness, and real
  norm-preserver/orthogonal facts assigned by the Stage 1 worklist.
- Resolve the norm-preserver converse boundary in `EQC-045` with explicit
  scalar-specific linear or antiunitary hypotheses.
- Keep expensive determinant/Pfaffian arguments in proof leaves and expose a
  small stable API with downstream matrix/simulation consumers.

### Completion Requirements

- Every Stage 2 worklist row has a terminal closure outcome and named Lean
  evidence.
- The determinant result excludes the `-1` branch or proves why it cannot be
  excluded under the stated hypotheses.
- All dimensions, nonempty assumptions, scalar conventions, and group targets
  are explicit in theorem signatures.
- Focused matrix builds, adjacent simulation/resource consumers, strict
  compilation, axiom checks, counterexample tests, and static scans pass.
- Corrections and dependent traceability rows are updated immediately.

## 3-ORDERING

### Big Picture Objective

Turn supplied finite schedules and semantic reindexings into executable,
verified ordering and routing infrastructure with honest costs.

### Detailed Implementation Plan

- Define an executable topological-sort procedure for the paper's finite gate
  precedence data, returning either a certified legal schedule or a certified
  cycle obstruction.
- Prove permutation completeness, precedence preservation, evaluator
  compatibility, termination, and an explicit complexity bound.
- Define physical adjacent-swap routing for arbitrary wire placements and prove
  exact denotation, restored spectators, width, gate count, and depth bounds.
- Formalize the corrected temporal-cut/poset object needed by multi-top and
  scheduling arguments; distinguish a chosen schedule from schedule-independent
  semantics.
- Retain the existing exact schedule API as a low-level certificate interface.

### Completion Requirements

- Every Stage 3 worklist row has a terminal closure outcome.
- The scheduler evaluates on representative finite examples and rejects a
  cyclic example with a proof-bearing result.
- Routing emits actual gates; no reindexing or equivalence is counted as a
  zero-cost swap.
- Correctness, resource, and runtime theorems compile through real consumers.
- Focused/adjacent builds, executable evaluations, strict checks, audit checks,
  shortcut scans, and `git diff --check` pass.

## 4-QDENSITY

### Big Picture Objective

Build the minimum reusable native quaternionic mixed-state and measurement
layer needed for partial trace and operational simulation.

### Detailed Implementation Plan

- Select and document a quaternionic Hermitian positivity convention based on
  real quadratic forms or proved complexification; do not add an order instance
  to `ℍ`.
- Define finite quaternionic density matrices and effects with normalization,
  convexity, pure-state constructors, and real-valued Born probabilities.
- Prove preservation/reflection results under quaternion complexification.
- Define partial trace with explicit basis/tensor association and prove trace,
  positivity, product-state, pure-state, and marginal laws.
- Formalize the mixed-top hypotheses needed by the paper's arbitrary-top rebit
  and qubit simulations; distinguish product, uncorrelated, and arbitrary mixed
  top states.
- Supply small finite examples and a diagnostic separating equal diagonal
  weights from equal reduced states.

### Completion Requirements

- Every Stage 4 worklist row and `EQC-046`/`EQC-047` has a terminal closure
  outcome or an explicit checked obstruction assigned by Stage 1.
- Density/effect constructors are nonempty in intended finite dimensions and
  expose the empty-index boundary honestly.
- Born values are real and bounded; partial trace is well-defined and preserves
  the proved invariants.
- No proof relies on a fictitious quaternion order or commutative tensor law.
- Focused algebra/state builds, complexification consumers, examples, strict
  compilation, axiom audit, and scans pass.

## 5-QCHANNELS

### Big Picture Objective

Define quaternionic channels and determine their exact operational relationship
to complex channels and decoded measurements.

### Detailed Implementation Plan

- Define the narrowest mathematically justified finite quaternionic channel
  model, beginning with unitary conjugation and extending to Kraus-style maps
  only after positivity and trace preservation are proved.
- Add effects, instruments, outcome distributions, composition, identities,
  and marginal/partial-trace compatibility.
- Prove complexification simulation for preparations, transformations, and
  measurements, including explicit encoders, decoders, ancillas, and tested
  observables.
- State operational equality only at the strongest verified scope; do not infer
  a converse from nonsurjectivity of an algebraic embedding.
- Reclassify the product-input ordering witness using the new mixed/channel
  semantics: prove signaling/non-signaling or record a formal obstruction,
  without substituting ray inequality for a channel claim.

### Completion Requirements

- The Stage 5 core row and relevant `EQC-051` obligation have terminal checked
  outcomes.
- Every channel constructor has positivity and trace-preservation evidence.
- Complex simulation preserves the declared preparation/channel/effect outcome
  probabilities, with every policy visible.
- Any converse or separation theorem names the exact allowed operational tests.
- Focused/adjacent builds, channel-law tests, downstream consumers, strict
  compilation, axiom checks, and scans pass.

## 6-FANOUT

### Big Picture Objective

Settle the paper's real-gate optimization and logarithmic multi-top simulation
claims with physical circuits and exact resource accounting.

### Detailed Implementation Plan

- Reconstruct the real-gate optimization target from emitted circuit syntax,
  not from arithmetic edits to old resource formulas.
- Define the two-rail/top-sector splitter and prove its exact intertwining and
  observable behavior.
- Build an executable balanced rail tree with explicit ancillas, routing,
  chronology, and cleanup.
- Prove the strongest valid depth, size, width, and fanout theorem for the
  multi-top simulation; if the advertised class-wide logarithmic depth is
  false, prove a corrected model-specific theorem or a no-go result.
- Keep phase tracking as an invariant-subspace/orbit statement rather than a
  claim that one qubit literally stores arbitrary quaternionic phase.

### Completion Requirements

- Both Stage 6 worklist rows have terminal closure outcomes.
- The construction is executable and its evaluator theorem is consumed by the
  simulation layer.
- All routing and ancilla operations are emitted and counted.
- Claimed asymptotics follow from exact recurrences and explicit hypotheses.
- Small-width evaluations, focused/adjacent builds, strict/audit checks, and
  resource-formula scans pass.

## 7-ENCODING

### Big Picture Objective

Give circuits, schedules, scalar parameters, inputs, and outputs finite
machine-level representations with executable validation and decoding.

### Detailed Implementation Plan

- Define finite encodings for the selected exact scalar sublanguage, gates,
  wire indices, ordered circuits, schedules, precision requests, and measured
  outputs.
- Prove decode/encode laws, malformed-input rejection, size bounds, and
  compatibility with the stable exact semantics.
- Implement the real and quaternionic uniform-generator interfaces and
  deterministic/randomized postprocessing interfaces needed later.
- Separate dense matrix descriptions from bounded-arity gate codes and record
  every bit-length convention.
- Do not use host floating-point values as exact unitaries or exact proof data.

### Completion Requirements

- All four Stage 7 worklist rows have terminal closure outcomes.
- Encoders, decoders, validators, and representative generators evaluate on
  regression examples.
- Round-trip theorems and explicit code-size bounds compile.
- Invalid schedules, dimensions, gates, and precision requests are rejected.
- Focused runtime/proof builds, extraction/evaluation tests, downstream
  consumers, strict/audit checks, and scans pass.

## 8-ERROR

### Big Picture Objective

Connect finite scalar approximation to certified state, circuit, and outcome
error without confusing approximate values with exact unitaries.

### Detailed Implementation Plan

- Define a computable rounding target and prove scalar/matrix error bounds.
- Provide a certified route from encoded approximants to legal gates: exact
  synthesis into a finite library, normalization/projection with proof, or a
  rejection result when certification fails.
- Prove telescoping circuit error bounds with explicit dependence on gate count,
  placement, chronology, and local error budgets.
- Transport operator error to normalized state-ray, decoded distribution,
  finite-event, and deterministic-postprocessing error.
- Prove zero-error compatibility with Goal 2's exact semantic relations.

### Completion Requirements

- The Stage 8 finite-precision row has a terminal closure outcome.
- Every approximation theorem exposes its metric, budget, and normalization or
  legality hypotheses.
- Accumulation bounds are proved rather than inserted as arithmetic constants.
- Executable examples demonstrate accepted and rejected approximants.
- Focused metric/encoding builds, circuit and outcome consumers, strict/audit
  checks, and scans pass.

## 9-SYNTHESIS

### Big Picture Objective

Replace supplied compiler certificates with constructed compilation procedures
and prove the strongest correct gate-count, depth, and runtime bounds.

### Detailed Implementation Plan

- Select explicit finite target gate libraries and state exact universality or
  density assumptions separately from compiler construction.
- Implement exact decomposition where available and approximate synthesis where
  necessary, using Stage 7 encodings and Stage 8 error certificates.
- Prove compiler termination, semantic correctness/error, width, ancilla,
  gate-count, depth, code-size, and runtime bounds.
- Re-examine the paper's generic-decomposition, constant-arity, and
  arbitrary-arity overhead claims; refute unsupported constants and publish the
  strongest constructed replacements.
- Ensure quaternionic compilation proceeds through an explicitly proved
  simulation/complexification path rather than an assumed quaternionic tensor
  compiler.

### Completion Requirements

- All three Stage 9 worklist rows have terminal closure outcomes.
- No theorem quantifies over a supplied compiler while claiming compiler
  existence.
- At least one nontrivial encoded circuit compiles and its decoded outcome/error
  theorem evaluates.
- Resource and runtime theorems follow from the executable implementation.
- Focused compiler builds, executable tests, adjacent simulations, strict/audit
  checks, and forbidden-supplied-data scans pass.

## 10-UNIFORMITY

### Big Picture Objective

Lift the finite constructions to uniform algorithm families and settle the
paper's computational-equivalence and complexity claims at an explicit error
and resource scale.

### Detailed Implementation Plan

- Define encoded uniform real, complex, and quaternionic circuit families with
  input-size and precision parameters, executable generators, acceptance
  events, and runtime measures.
- Prove the uniform complex-to-real and ordered quaternionic-to-complex
  simulations using the constructed scheduler, encoding, error, and synthesis
  layers.
- Construct a width-independent finite bounded-arity universal/dense schema for
  the selected model, or prove a precise no-go and formulate the strongest
  corrected family-dependent theorem.
- State and prove the resulting BQP containment/equality only after generator,
  approximation, success-probability, and polynomial-overhead obligations are
  established.
- Treat circuit/QTM correspondence as a separate theorem; use external results
  only after restating all encoding and approximation hypotheses.

### Completion Requirements

- All six Stage 10 partial/unresolved worklist rows have terminal outcomes.
- The uniform theorem quantifies input size and precision and exposes width,
  size, depth, random bits, error, and runtime overhead.
- Preferred schedules remain supplied or computed according to Stage 3; no
  schedule-independence claim is smuggled into BQP language.
- The universal-set result is constructive, or its impossibility/corrected
  boundary is checked.
- Generator evaluations, complexity-bound arithmetic, focused/adjacent builds,
  strict/audit checks, and scans pass.

## 11-STRUCTURE

### Big Picture Objective

Resolve the remaining structural and interpretive partial claims using the
completed operational and uniform layers.

### Detailed Implementation Plan

- Formalize the exact complex-structure or invariant-subspace data needed to
  compare real, complex, and quaternionic models without assuming an
  unjustified left scalar multiplication.
- Give a precise phase-tracking theorem for the added top sector and distinguish
  coefficient bookkeeping, ray quotient, subsystem factorization, and
  operational observability.
- Settle the “not `n+1` rebits” limitation at its strongest justified scope.
- Address norm-preserver converses (`EQC-045`) with scalar-specific linear or
  antiunitary hypotheses.
- State any converse simulation using the operational relations from Stage 5,
  not algebraic image nonsurjectivity alone.

### Completion Requirements

- All four Stage 11 structural rows and assigned source-only families have
  terminal closure outcomes.
- Every scalar action side and linearity convention is explicit.
- No dimension-count or image-properness theorem is presented as an
  operational separation without a proved bridge.
- Positive and negative examples compile through public consumers.
- Focused structure builds, channel/uniformity consumers, strict/audit checks,
  and scans pass.

## 12-FRONTIER

### Big Picture Objective

Create an honest, precise handoff for source questions that are genuine future
research rather than prerequisites of the reusable computational core.

### Detailed Implementation Plan

- Create `docs/ResearchFrontier.md` covering every baseline intentionally
  excluded row and any user-approved core-to-frontier transfer.
- For each item record the exact source claim/question, current Lean boundary,
  missing definitions, minimum assumptions, dependency on Goal 3 core,
  falsifiable theorem candidates, counterexample routes, relevant primary
  literature, and recommended future goal.
- Group, without merging IDs: real-QTM/external results; multipath semantics;
  protocols and communication; capacity/rebit information theory; physicality;
  and alternative scalar algebras.
- Formalize any cheap decisive boundary theorem exposed by the completed core;
  do not retain a frontier label merely to avoid a now-straightforward proof.
- Add checker coverage so no excluded row or source-only family disappears.

### Completion Requirements

- All 16 baseline excluded rows occur exactly once in the frontier or have a
  checked terminal result elsewhere.
- Every frontier entry has a precise model gap and at least one concrete future
  theorem/counterexample target; vague “future work” is insufficient.
- Release prose distinguishes unproved research questions from proved Goal 3
  results.
- Frontier IDs and dependencies are mechanically checked against the worklist.
- Documentation, link, Markdown, and `git diff --check` checks pass.

## 13-RELEASE

### Big Picture Objective

Publish the computational and operational completion as a clean, reusable Lean
library with an exact frontier boundary.

### Detailed Implementation Plan

- Reconcile every Goal 3 worklist row, correction, source-only family, public
  declaration, audit endpoint, consumer, and frontier entry.
- Stabilize namespaces, imports, docstrings, examples, and public-root exposure;
  keep audits, diagnostics, and generators non-public.
- Produce the final Goal 3 report: formalized mathematics, theorem stack,
  algorithms, resource bounds, corrections, refutations, underdetermination
  results, omitted research, project structure, build/audit evidence, and
  downstream usage.
- Run a clean pinned default build, all maintained audits/examples, strict
  warning-as-error compilation, trust/axiom parsing, registry/worklist
  validators, source/artifact/import/Markdown/whitespace scans, and downstream
  public-root smoke tests.
- Obtain independent mathematical, implementation/resource, audit/release, and
  documentation/frontier reviews; repair and rerun affected checks.

### Completion Requirements

- Every default core row has a terminal evidence-backed outcome; no partial or
  unresolved core status remains.
- Every excluded/frontier row is accounted for without being called proved.
- The exact-to-encoded-to-approximate-to-compiled-to-uniform theorem stack, or
  its strongest checked corrected boundary, is documented and imported through
  the stable API.
- Quaternionic density/channel results and their complex simulation scope are
  explicit and audited.
- Completed modules contain no proof hole, project axiom, unsafe/opaque
  shortcut, or unexplained fallback.
- Clean builds, audits, validators, downstream smoke tests, scans, and
  `git diff --check` pass after final documentation edits.
- All independent reviews return **PASS**.

## Stage Status

- [ ] `1-REBASE`
- [ ] `2-ALGEBRA`
- [ ] `3-ORDERING`
- [ ] `4-QDENSITY`
- [ ] `5-QCHANNELS`
- [ ] `6-FANOUT`
- [ ] `7-ENCODING`
- [ ] `8-ERROR`
- [ ] `9-SYNTHESIS`
- [ ] `10-UNIFORMITY`
- [ ] `11-STRUCTURE`
- [ ] `12-FRONTIER`
- [ ] `13-RELEASE`
