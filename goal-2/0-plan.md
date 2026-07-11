# Goal 2 — Rigorous Semantic Equivalence Classification Retrofit

## Big-Picture Objective

Retrofit the verified Goal 1 Lean library with a precise, reusable, and
machine-checked vocabulary for every materially different meaning of “equal,”
“equivalent,” “same behavior,” “preserves,” and “simulates.”  Classify every
stable public comparison claim at its strongest justified level, prove the
valid implication hierarchy and failed converses, and make the resulting API a
hard semantic prerequisite for Goal 3.

The retrofit must distinguish same-space equality from cross-model simulation;
state phase from operator phase; representative, ray, basis, distribution,
channel, and all-effect behavior; fixed-input, all-basis-input, all-pure-input,
and mixed-input quantification; exact equality from metric approximation; and
ordinary public equivalence from algebraic equivalence onto an embedding image.

Completion also includes the normalized ray quotient work needed to close
`FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY`.  Goal 3 may mark those rows
`closedByGoal2` only after the quotient equality, descended evolution,
descended outcomes, consumers, builds, and axiom evidence all exist.

## Scope Boundary

Goal 2 includes:

- same-space finite state, operator, and ordered-circuit comparison relations;
- real sign, complex phase, and quaternion-safe sided phase relations;
- input-column phase, output-row phase, basis measurement, all-pure-input basis
  measurement, and certified classical basis behavior;
- normalized real, complex, and quaternionic ray quotient types;
- the minimum finite real/complex density-and-effect layer needed for unitary
  `ChannelEq`, `AllMeasurementEq`, and their equivalence;
- proof-bearing cross-model relations wrapping the existing exact simulations;
- a Euclidean induced operator-distance relation and basic error laws;
- the full implication/strictness audit and public classification registry.

Goal 2 deliberately leaves to Goal 3:

- generic partial trace and the paper's arbitrary mixed-top simulation claims;
- Kraus channels, instruments, native quaternionic density/channel positivity,
  channel capacity, protocols, and physicality;
- finite scalar encodings, quantization algorithms, accumulated finite-
  precision compilation, and runtime;
- gate synthesis, universality, uniform families, BQP, QTM, multipath, and
  alternative-scalar research.

Building a structure from the second list does not count as Goal 2 completion,
and Goal 2 must not preempt Goal 3 by making unproved operational claims.

## Authoritative Inputs

- The completed Goal 1 release and all stage reports under `goal-1/`.
- `QuaternionicComputing.lean` and every module it publicly imports.
- `QuaternionicComputing/AxiomAudit.lean`, currently the explicit manifest of
  main audited endpoints.
- `docs/Traceability.md`, `docs/Corrections.md`, `docs/Conventions.md`,
  `docs/Architecture.md`, and `docs/ReleaseReport.md`.
- The reindexed `goal-3/0-plan.md`, whose Stage 1 must consume Goal 2's actual
  release results rather than its pre-Goal-2 forecast.
- Repository-root `BUILD-PLAN.md`, authoritative for every Lean-changing stage.

## Non-Negotiable Constraints and No-Cheating Rules

- Never use `sorry`, `admit`, `sorryAx`, an unjustified axiom, an impossible
  premise, or a definition engineered to force a desired implication.
- Do not force the semantics into one total hierarchy.  Same-space equivalence,
  observational agreement, cross-model simulation certificates, and metric
  approximation are different families.
- A registry label or custom attribute is metadata, not proof.  Every classified
  comparison needs a theorem inhabiting the named relation.
- Do not call ordinary matrix equality “exact circuit equality” without going
  through `OrderedCircuit.eval`.
- Do not call `V = F U` same-space equality when `F` changes scalars, indices,
  dimensions, or added wires.  Use an explicit operator-embedding relation.
- Keep quaternionic state phase on the right.  Input-column quaternion phases
  multiply entries on the right; output-row phases multiply on the left.
- Never define arbitrary unit-quaternion multiplication as global operator
  phase.  The all-ray operator kernel is dimension-sensitive and expected to be
  central `±I` only in quaternionic dimension at least two; rank one is an
  explicit exceptional case that must be proved, not ignored.
- Do not identify a complex global phase after realification with ordinary real
  sign.  It becomes a top-sector rotation/orbit and needs its own relation or no
  quotient map.
- Do not define `SameBasisBehavior` by a vacuous biconditional on arbitrary
  unitaries.  Require a certified basis-permutation implementation and prove
  the induced permutation unique.
- Distinguish one fixed input, all computational-basis inputs, all normalized
  pure inputs, all density inputs, basis effects, all physical effects, and
  channel equality in theorem names and quantifiers.
- An arbitrary trace-test matrix is not a physical effect.  It may support a
  separation proof only under a separately named algebraic lemma.
- Basis-distribution equality, finite event equality, and deterministic
  postprocessing equality are not channel or all-measurement equality.
- `OperatorClose ε` is an error-budget relation, not an equivalence relation.
  Its triangle theorem changes the budget from `ε, δ` to `ε + δ`.
- Use the Euclidean induced/spectral operator norm selected explicitly for
  operator distance; do not silently inherit an unrelated entrywise or
  `ℓ∞` matrix norm.
- Group equivalences onto embedding images are algebraic isomorphisms, not
  behavioral equivalences, and must be classified separately.
- Preserve Goal 1 theorem statements where correct.  Prefer proof-bearing
  wrappers over invasive rewrites, and keep new definitions in narrow semantic
  leaves.
- Treat `BUILD-PLAN.md` module structure, focused builds, adjacent consumers,
  boundary checks, reporting, and fold-back as completion requirements.

## Current Facts and Assumptions

- Goal 1 pins Lean 4.31.0 and mathlib v4.31.0 at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- The current tree has 65 Lean sources. Clean public-root, focused diagnostic,
  combined-target, and explicit audit builds pass; 286 audited root endpoints
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- `ExactOperatorEq` now names literal same-type matrix equality and
  `ExactCircuitEq` names literal equality of `OrderedCircuit.eval`.
  Multiplication, gatewise, and append congruence theorems compile through real
  diagnostic consumers.
- Real sign, complex right phase, and quaternion right phase exist for state
  columns and are proved equivalence relations. `RealRay`, `ComplexRay`, and
  `QuaternionRay` now quotient normalized representatives by exactly those
  relations. Stage 4B descends basis distributions, finite events,
  deterministic postprocessing, supplied unitary evolution, and
  locally-unitary chronological-circuit evolution with exact identity and
  ordered-composition laws. Stage 4C now proves that complex phase becomes a
  doubled-real sector rotation, constructs the correct orbit quotient, and
  proves the exact obstruction to an ordinary target-`RealRay` map.
- `FiniteDistribution` packages normalized outcome weights, finite events, and
  deterministic pushforwards. Stage 2 now separates fixed-input
  `OutputWeightEqAt`, all-basis-input `BasisMeasurementEq`, all-normalized-pure-
  input `PureInputBasisMeasurementEq`, and packaged
  `NormalizedDistributionEq`, with checked finite classical consequences.
- The exact simulations already separate operator embedding, state
  intertwining, bottom measurement, event, and postprocessing results.  Their
  statements compare different scalars/dimensions and therefore cannot be
  classified by same-space circuit equality alone.
- The product-input ordering witness proves equal quaternionic basis weights at
  one specified input while disproving right-ray equality.  It is not an
  all-input circuit-equivalence theorem.
- The library has no generic density matrix, physical effect, unitary channel,
  `ChannelEq`, `AllMeasurementEq`, certified basis behavior, or
  operator-distance API.
- Pinned mathlib provides matrix positive-semidefiniteness, matrix order, trace,
  finite-dimensional linear algebra, and continuous-linear-map norms, but API
  probes are required before choosing representations.
- Goal 3 has been reindexed and now treats Goal 2's clean release, immutable
  pre-retrofit comparison cohort, semantic API manifest, and traceability
  fold-back as hard prerequisites.
- Stage 1 independently discovered 51 comparison families: 42 represented in
  the completed Goal 1 implementation/release surface and nine additional
  source-level families whose missing models or proofs remain explicit.
  `docs/Goal1ComparisonCohort.json` assigns 936 public declarations uniquely;
  its SHA-256 checksum is frozen in `docs/Goal1ComparisonCohort.sha256`.
- The separate `docs/Goal2SemanticAPIManifest.json` now contains 487 unique
  Stage 2/3A/3B/3C/4A/4B declarations, each with seven semantic axes and a named
  downstream consumer. All names resolve through the public root, 54 distinct
  diagnostic consumers resolve, and 100 entries are direct release-audit
  targets. The frozen Goal 1 cohort and checksum remain unchanged.
- Pinned mathlib probes validate positive-semidefinite trace-one real/complex
  densities, Loewner-interval effects, rank-one physical effects, a viable
  physical-effect separation route, finite basis columns, and the scoped L2
  induced operator norm. Complex PSD needs `ComplexOrder`; Loewner matrices
  need `MatrixOrder`; trace-one densities require a nonempty index when
  existence is used.
- Stage 2 focused, adjacent, public-root, warning-as-error, manifest, and axiom
  checks pass. `EQC-004`, `EQC-005`, `EQC-006`, and `EQC-026` have
  proof-bearing realizations; Stage 3 can build on the exact and measurement
  vocabulary without importing the diagnostic leaf.
- Stage 3A review found that the old quaternionic `phaseWitnessInput = (1,1)`
  has total weight `2`, so `EQC-001` incorrectly called that existing raw-column
  witness normalized. The implemented normalized counterexample uses
  amplitudes `3/5` and `4/5`; the evidence wording is repaired while the frozen
  cohort membership and checksum remain unchanged.
- Stage 3A now supplies real sign, complex right-phase, and quaternionic strict
  right-phase equivalence on normalized representatives, with exact-to-phase,
  basis-distribution, raw matrix/circuit, and normalized unitary-evolution
  theorems. The normalized `3/5,4/5` left-phase rejection certificate repairs
  `EQC-001`. Stages 4A--4C now supply quotient equality, descended operations,
  and the corrected embedding-orbit boundary, so the two transferred ray rows
  are recorded `closedByGoal2` with proof-bearing evidence.
- Stage 3B now exports eight distinct real/complex global, input-column,
  output-row, and projective-action operator relations plus eight evaluator-
  backed circuit relations. Their equivalence laws, exact/global/measurement
  arrows, global-phase unitarity, and sided matrix/circuit composition compile.
  Common-later and common-earlier composition are asymmetric, and projective
  common-earlier evolution requires unitarity. Rational unitary witnesses prove
  exact/global strictness, basis-side incomparability, superposition
  sensitivity, and output-measurement/projective separation. Rectangular
  operator projective action is vacuous on an empty input type, so later
  converses retain explicit positive-cardinality/nonempty hypotheses; circuit
  projective action on the inhabited `BitBasis W` is nonvacuous even at zero
  wires.
- Stage 3C exports five side-correct quaternionic operator relations and four
  evaluator-backed circuit wrappers. Raw and normalized all-input projective
  action are equivalent on every finite input type, including the empty type.
  For square unitary dimension at least two, either relation is equivalent to
  one central real sign, with no separate unitarity premise on the second
  matrix. Rank one is exactly the full unit-quaternion scalar family:
  projective triviality, scalar-matrix unitarity, and norm square one are
  equivalent, while the explicit `j` witness is not a central sign. The 101
  Stage 3C declarations have 11 complete diagnostic consumers and 13 direct
  root-audit targets; no quaternionic channel claim is made.
- Stage 4A now exports explicit normalized-state setoids and plain quotient
  types for real signs, complex unit right phases, and quaternionic unit right
  phases. Its 40 declarations include exact constructor equality,
  representative induction/lifting/function extensionality, the real
  equality-or-negation theorem, and `Nonempty (Ray I) ↔ Nonempty I`. Four
  aggregate consumers cover the surface, eight direct root audits compile,
  and the low-dependency quotient API supports a strict all-three-scalar 4B
  descent probe.
- Stage 4B now exports the all-three-scalar descent design: quotient
  distributions/events/postprocessing, normalized unitary evolution,
  locally-unitary chronological circuit evolution, phase/equality bridges,
  and their identity/composition laws. The 63 stable declarations are split
  among narrow distribution-law, local-unitarity, ray-observable,
  ray-evolution, and semantic-bridge leaves; no State-to-Semantics dependency
  or arbitrary matrix-to-normalized-ray map appears. Four non-root aggregate
  consumers exercise the exact surface, 14 direct root-audit targets compile,
  and the quaternionic diagnostic retains the noncommutative order `V * U`.
- Stage 4C exports 84 stable declarations across three narrow leaves: 66 for
  the rotation/orbit core, ten for bottom marginal observables, and eight for
  the ordinary-real-ray boundary. Complex right phase becomes the direct
  doubled-real sector action
  `(x,y) ↦ (re(eta)*x + im(eta)*y, -im(eta)*x + re(eta)*y)`.
  Its independently defined unit orbit is an equivalence relation whose
  quotient is canonically equivalent to `ComplexRay`, with both canonical
  columns, arbitrary pure top rebits, and bottom marginal distributions as
  real consumers. Ordinary `RealRay` is strictly finer: either canonical
  column assignment descends from `ComplexRay I` exactly in the vacuous
  `IsEmpty I` case, while unit phases survive as real signs exactly at `±1`.
  This proves correction C-027 without disturbing representative-level matrix
  intertwining or decoded bottom outcomes. `FER03-D01-REBIT` and
  `FER03-FND-COMPLEX-STATE-RAY` are now proved as stated and
  `closedByGoal2`; phase-kickback, mixed-state, and channel claims remain open.

## Inventory and Manifest Policy

- Stage 1 freezes an immutable `Goal1ComparisonCohort`: every semantic
  comparison claim discovered in the completed Goal 1 public surface before
  this retrofit begins. Later Goal 2 declarations never enlarge that cohort.
- New public definitions, hierarchy theorems, wrappers, counterexamples, and
  metric declarations introduced by Goal 2 are tracked separately in a
  `Goal2SemanticAPIManifest`.
- The cohort registry classifies every pre-retrofit item exactly once at its
  strongest proved level. The API manifest checks coverage and audit evidence
  for new Goal 2 exports without feeding them back into the cohort checksum.
- Stage 11 checks both finite manifests independently, and Stage 12 requires
  both checks to pass. This separation prevents self-referential inventory
  growth while still requiring complete coverage of the retrofit itself.

## Semantic Axes

Every public comparison classification must record all applicable axes rather
than only a strength label.

| Axis | Required distinctions |
|---|---|
| Space | same scalar/index space; reindexed; embedded with changed scalar/dimension; decoded/marginalized |
| Subject | state representative; state ray; operator; ordered circuit; distribution; channel; algebraic image; resource fact |
| Input scope | one stated input; every basis input; every normalized pure input; every density input; ancilla-stable input if claimed |
| Observation scope | amplitudes; one basis weight; full basis distribution; finite events; deterministic postprocessing; all physical effects; full channel |
| Phase | none; one complex/real global phase; input-column phase; output-row phase; quaternion right state phase; central operator kernel |
| Exactness | exact; equality after a named map; equality after decoding/marginalization; `ε`-bounded approximation |
| Ancilla policy | none; fixed top state; arbitrary pure top state; mixed top state; traced/decoded added wire |

## Provisional Public Relations

Exact names may be adjusted after compiling API probes, but the distinctions
may not be collapsed.

```lean
ExactOperatorEq U V := U = V
ExactCircuitEq C D := ExactOperatorEq (OrderedCircuit.eval C) (OrderedCircuit.eval D)

OutputWeightEqAt weight U V ψ :=
  ∀ y, weight ((U *ᵥ ψ) y) = weight ((V *ᵥ ψ) y)

BasisMeasurementEq weight U V :=
  ∀ x y, weight (U y x) = weight (V y x)

PureInputBasisMeasurementEq weight U V :=
  ∀ ψ : NormalizedState ..., OutputWeightEqAt weight U V ψ

ComplexGlobalPhaseEq U V :=
  ∃ ζ : ℂ, Complex.normSq ζ = 1 ∧ V = ζ • U

ComplexInputBasisPhaseEq U V :=
  ∃ φ, (∀ x, Complex.normSq (φ x) = 1) ∧
    ∀ y x, V y x = U y x * φ x

ComplexOutputBasisPhaseEq U V :=
  ∃ θ, (∀ y, Complex.normSq (θ y) = 1) ∧
    ∀ y x, V y x = θ y * U y x

QuaternionCentralSignEq U V
QuaternionInputRightPhaseEq U V
QuaternionOutputLeftPhaseEq U V
QuaternionRayActionEq U V

ProjectiveActionEq rayEq U V :=
  ∀ ψ : NormalizedState ..., rayEq (U *ᵥ ψ) (V *ᵥ ψ)

BasisPermutationImplementation U p
SameBasisBehavior certifiedU certifiedV := certifiedU.perm = certifiedV.perm
BasisTransitionRelationEq U V

ChannelEq U V := ∀ ρ : DensityMatrix ..., unitaryConjugate U ρ = unitaryConjugate V ρ
AllMeasurementEq U V :=
  ∀ ρ : DensityMatrix ..., ∀ E : Effect ...,
    born E (unitaryConjugate U ρ) = born E (unitaryConjugate V ρ)

ExactOperatorEmbedding F U V := V = F U
StateIntertwining encode U V := ∀ ψ, V *ᵥ encode ψ = encode (U *ᵥ ψ)
DecodedMeasurementAgreement ...
DecodedDistributionAgreement ...

OperatorClose ε U V := spectralOperatorDistance U V ≤ ε
PhaseAwareOperatorClose ε U V
DistributionClose ε μ ν := totalVariationDistance μ ν ≤ ε
```

Cross-model declarations use “Embedding,” “Intertwining,” “Agreement,” or
“Simulation,” not a misleading same-space `Eq` suffix.

## Target Implication Structure

For nonempty finite complex unitary spaces, the intended theorem graph is:

```text
ExactOperatorEq
        │
        ▼
ComplexGlobalPhaseEq ⇔ ProjectiveActionEq ⇔ ChannelEq ⇔ AllMeasurementEq
       ╱                                      ╲
      ▼                                        ▼
InputBasisPhaseEq        OutputBasisPhaseEq ⇔ PureInputBasisMeasurementEq
      ╲                                        ╱
       └────────────▶ BasisMeasurementEq ◀────┘
```

For certified basis-permutation unitaries, prove the appropriate restricted
equivalences among same basis permutation, input/output phase, and basis
measurement.  Do not draw those arrows for generic unitaries.

For normalized states, separately prove:

```text
ExactStateEq → RayEq → BasisWeightEq ⇔ DistributionEq
                                      ⇔ all finite-event weights
                                      ⇔ all deterministic pushforwards
```

Required strictness or boundary witnesses include:

- exact equality is strictly stronger than complex global phase;
- channel/global phase is strictly stronger than input-column phase and than
  output-row phase;
- input-column and output-row phase are incomparable in general;
- input-column phase can change superposed-input basis statistics;
- output-row phase preserves all-pure-input basis statistics but can change the
  channel/all-effect behavior;
- entrywise basis-measurement equality need not imply coherent input or output
  phase consistency;
- unrestricted equality of the raw basis-transition relation can be vacuous on
  nonmonomial unitaries and is not certified classical behavior;
- equal basis weights of states need not imply ray equality, over both complex
  and quaternionic examples;
- the existing quaternionic witness has exactly one-input strength;
- left quaternionic phase is not evolution-natural;
- fixed-budget `OperatorClose ε` is not transitive, while the additive triangle
  budget theorem is valid.

## Dependency Shape

```text
1-INVENTORY -> 2-CORE
2-CORE -> 3-PHASE, 6-DENSITY, 9-CROSSMODEL, 10-APPROX
3-PHASE -> 4-RAYS, 5-BASIS
6-DENSITY -> 7-CHANNELS
3-PHASE + 4-RAYS + 5-BASIS + 7-CHANNELS -> 8-HIERARCHY
2-CORE + 3-PHASE + 4-RAYS -> 9-CROSSMODEL
all feature stages 2-10 -> 11-REGISTRY -> 12-RELEASE
```

## Mandatory Compiling Milestones

Broad stages must be split into these independently verified reports before
implementation.  An umbrella stage remains incomplete until every milestone
and consumer passes.

| Workstream | Required milestones |
|---|---|
| 3-PHASE | `3A-STATEPHASE`: reuse/normalize state relations; `3B-COMPLEXREAL`: operator global/input/output phases; `3C-QUATERNION`: central sign, sided basis phase, ray-action kernel and rank-one exception |
| 4-RAYS | `4A-QUOTIENTS`: real/complex/quaternion normalized quotients; `4B-DESCENT`: evolution and basis distributions; `4C-EMBEDORBIT`: realification top-rotation boundary and source-row closure |
| 6-DENSITY | `6A-DENSITY`: real/complex density and pure states; `6B-EFFECTS`: physical effects/Born values; `6C-SEPARATION`: genuine effects separate densities |
| 7-CHANNELS | `7A-FORWARD`: channel implies all measurements; `7B-CONVERSE`: effect separation converse; `7C-PHASE`: global phase implies channel; `7D-CHARACTERIZE`: complex and real unitary converses |
| 8-HIERARCHY | `8A-ARROWS`: all valid implications; `8B-WITNESSES`: failed converses/incomparability; `8C-CLASSICAL`: restricted certified-basis equivalences |
| 9-CROSSMODEL | `9A-RELATIONS`: cross-space predicates; `9B-WRAPPERS`: primary/composed/scheduled/compiler simulations; `9C-OUTCOMES`: distributions/events/postprocessing and negative channel classification |
| 11-REGISTRY | `11A-MANIFEST`: immutable Goal 1 cohort plus Goal 2 semantic API manifest; `11B-CERTIFICATES`: proof-bearing wrappers; `11C-CHECKER`: independent exact-coverage validation and documentation generation/fold-back |

## Success Metrics and Verification Requirements

- Stage 1 discovers and freezes the immutable `Goal1ComparisonCohort`; the
  scaffold does not invent its final count. Every pre-retrofit semantic
  comparison appears exactly once in its checked cohort registry.
- Every new public Goal 2 semantic declaration appears exactly once in the
  separately checked `Goal2SemanticAPIManifest` and does not alter the frozen
  cohort checksum.
- Every cohort-registry row names its strongest proved relation and all semantic
  axes.
  Algebraic image equivalences, resource equalities, internal identities, and
  non-comparison support theorems are classified separately.
- Every implication in the published graph is a Lean theorem; every asserted
  strictness or missing arrow has a Lean counterexample or exact obstruction.
- Real, complex, and quaternionic ray quotient equality and descended
  operations compile.  `FER03-D01-REBIT` and
  `FER03-FND-COMPLEX-STATE-RAY` are corrected/proved with traceability and audit
  evidence sufficient for Goal 3's `closedByGoal2` disposition.
- `ChannelEq ↔ AllMeasurementEq` is proved using genuine density matrices and
  physical effects.  On explicitly nonempty finite complex unitary spaces,
  channel equality and projective action are characterized by one complex
  global phase; the real global-sign/projective-action analogue is proved or
  its exact obstruction documented without weakening the complex result.
- Every current simulation comparison has a proof-bearing cross-model wrapper
  recording its scalar/index change, state encoder, top-state quantifier,
  marginal/decoder, input scope, and observable scope.
- Operator approximation uses the selected Euclidean induced norm and is never
  advertised as an equivalence relation or a finite-precision compiler.
- All completed modules contain no holes, project-specific axioms, unsafe or
  opaque shortcuts, or status-only classifications.
- Focused leaf, adjacent consumer, public root, clean audit, warning-as-error,
  registry checker, downstream import smoke, forbidden-token, whitespace,
  artifact, and `git diff --check` verification passes under `BUILD-PLAN.md`.
- Goal 3 is rebaselined from actual Goal 2 results, with every transferred row
  and new module/audit/correction count explicitly accounted for.

## Stages

### 1-INVENTORY

#### Big Picture Objective

Freeze the exact semantic comparison surface and viable mathlib APIs before
introducing irreversible relation names.

#### Detailed Implementation Plan

- Enumerate every public theorem comparing circuit evaluations, state actions,
  rays, basis weights, distributions, events/postprocessings, channels, or
  embeddings.  Use the public root, AxiomAudit endpoints, traceability rows,
  public docstrings, and documentation claims as independent discovery inputs.
- Give every candidate one provisional disposition: behavioral comparison,
  cross-model certificate, algebraic image equivalence, internal algebraic
  identity, resource equality, supporting theorem, or genuinely out of scope.
- Inventory ambiguous uses of “same,” “equal,” “equivalent,” “preserves,” and
  “simulates”; record the missing axes for each.
- Probe pinned mathlib APIs for positive-semidefinite matrices, matrix order,
  effects, trace separation, finite bases, continuous linear maps, and the
  Euclidean induced operator norm with compiling files.
- Seed `docs/EquivalenceClassification.md`, the machine-readable immutable
  `Goal1ComparisonCohort`, and a separate `Goal2SemanticAPIManifest` without
  marking unproved classifications or exports complete.

#### Completion Requirements

- The frozen `Goal1ComparisonCohort` has a checksum and every candidate has
  exactly one provisional owner stage/disposition.
- The initially seeded `Goal2SemanticAPIManifest` is structurally separate and
  records every new public semantic declaration as Goal 2 introduces it.
- Every existing main comparison family and every source claim involving
  behavioral equivalence is represented; no final count is assumed in advance.
- API probes establish viable density/effect/operator-norm representations or
  record exact alternate routes.
- Goal 1 clean build/audit and current worktree state are recorded in
  `1-INVENTORY.md`; no implementation result is inferred from inventory alone.

### 2-CORE

#### Big Picture Objective

Define the low-dependency exact and computational-basis comparison vocabulary
with explicit input and observation scopes.

#### Detailed Implementation Plan

- Add narrow `Semantics/Core.lean` and `Semantics/Measurement.lean` leaves.
- Define exact operator and ordered-circuit equality through public evaluation.
- Define output-weight agreement at one state, all-basis-input measurement
  agreement, all-normalized-pure-input basis agreement, and normalized
  distribution agreement.
- Prove reflexivity, symmetry, and transitivity for actual same-domain `Eq`
  relations; add congruence and circuit-lift lemmas.
- Connect pointwise weight agreement to `FiniteDistribution.ext`, finite event
  equality, and deterministic pushforward equality.
- Add basis-ket and entry-characterization lemmas used by later phase stages.

#### Completion Requirements

- One-input, all-basis-input, and all-pure-input relations are distinct types or
  predicates with noninterchangeable theorem signatures.
- `ExactCircuitEq` unfolds only to equality of `OrderedCircuit.eval`.
- Distribution/event/postprocessing implications compile through the existing
  public distribution API.
- Focused builds, adjacent circuit/state consumers, edge-index examples, and
  axiom spot-audits pass.

### 3-PHASE

#### Big Picture Objective

Formalize scalar- and side-correct state/operator phase relations without
reintroducing the paper's quaternionic left-phase error.

#### Detailed Implementation Plan

- Reuse the existing complex/quaternion state right-phase definitions and
  theorem families; add a real unit-sign state relation and consistent public
  naming/wrappers where useful.
- Define complex global operator phase and real global sign, plus input-column
  and output-row phase relations with explicit multiplication side.
- Define quaternion central-sign, input-right-phase, output-left-phase, and
  all-ray-action relations.  Define real/complex projective-action relations
  through their state-ray APIs.  Prove the quaternion central-kernel theorem in
  dimensions at least two and the quaternionic rank-one exception, or isolate
  any exact additional prerequisite without exporting a false generic theorem.
- Prove equivalence-relation laws, exact-to-phase implications, basis-weight
  consequences, and compatible matrix/circuit lifts.
- Add concrete complex and quaternion sign/order tests.

#### Completion Requirements

- No public relation treats arbitrary unit quaternion multiplication as global
  operator phase or uses left phase for physical quaternionic states.
- Input column phases and output row phases have different names and correct
  right/left order over `ℍ`.
- Complex/real global operator phase and all state phase relations compile as
  equivalence relations with public examples.
- Quaternion dimension hypotheses and the rank-one exception are theorem-
  checked and documented, not hidden by a typeclass.

#### Mandatory Milestone Status

- [x] `3A-STATEPHASE`
- [x] `3B-COMPLEXREAL`
- [x] `3C-QUATERNION`

### 4-RAYS

#### Big Picture Objective

Turn normalized state phase relations into usable quotient types and close the
two transferred paper rows completely.

#### Detailed Implementation Plan

- Add `State/Ray.lean` with normalized `RealRay`, `ComplexRay`, and
  `QuaternionRay` quotients using real sign, complex unit phase, and quaternion
  unit right phase respectively.
- Prove constructor equality iff the intended relation, representative
  induction, nonempty/normalization facts, and faithful interfaces to concrete
  normalized states.
- Prove arbitrary compatible matrix action respects phase at the column level;
  descend unitary/certified-normalization-preserving circuit evolution, basis
  weights, normalized basis distributions, finite events, and deterministic
  postprocessing to normalized rays.
- Audit embedding descent: complex phase under realification is a top-sector
  rotation, not ordinary real sign.  Define a separate encoding-orbit relation
  only if it has real consumers; otherwise prove/document the obstruction and
  omit a false `ComplexRay → RealRay` map.
- Add rebit/qubit/quaterbit examples and update both source rows and dependent
  documentation.

#### Completion Requirements

- Quotient equality is iff the correct state phase relation for all three
  scalars; no quotient by all nonzero scalars or quaternion left phase appears.
- Evolution and computational-basis distributions are well-defined on quotient
  representatives with identity/composition laws.
- The realification orbit boundary is theorem-checked and cannot be mistaken
  for real-ray equality.
- `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` are moved to **corrected
  and proved** or **proved as stated** with named Lean declarations, consumers,
  correction effects, focused builds, and axiom audit entries.

#### Mandatory Milestone Status

- [x] `4A-QUOTIENTS`
- [x] `4B-DESCENT`
- [ ] `4C-EMBEDORBIT`

### 5-BASIS

#### Big Picture Objective

Define nonvacuous classical reversible basis behavior and connect it to the
phase/measurement vocabulary only under certified hypotheses.

#### Detailed Implementation Plan

- Define basis columns and `BasisPermutationImplementation U p`, including the
  phase attached to each basis input where appropriate.
- Define the raw basis-transition relation from the user's biconditional as a
  diagnostic notion and prove why it can be vacuous for generic nonmonomial
  operators; do not call it classical reversible behavior.
- Bundle basis-classical unitary operators/circuits with their permutation
  certificate and prove the induced permutation unique.
- Define `SameBasisBehavior` as equality of certified permutations rather than
  a biconditional that generic quantum circuits satisfy vacuously.
- Prove exact/global/input/output phase and basis-measurement consequences on
  the certified monomial class, with all necessary unitary/nonempty hypotheses.
- Wrap existing basis preparation and permutation results where they genuinely
  implement this interface.

#### Completion Requirements

- Generic nonclassical circuits cannot inhabit certified basis behavior without
  an implementation proof.
- The induced basis permutation and its uniqueness compile over the declared
  real/complex/quaternion settings.
- Every arrow involving `SameBasisBehavior` is explicitly restricted to the
  certified basis-classical class.
- Focused builds, permutation examples, failed generic examples, and audits
  pass.

### 6-DENSITY

#### Big Picture Objective

Build only the finite real/complex physical state-and-effect core required to
state and prove channel/all-measurement equivalence.

#### Detailed Implementation Plan

- Add minimal `Semantics/Density.lean` and `Semantics/Effect.lean` leaves using
  pinned mathlib positive-semidefinite and matrix-order APIs.
- Define finite real/complex density matrices as Hermitian positive-semidefinite
  trace-one matrices, pure outer products, basis densities, physical effects,
  basis effects, and Born values.
- Define unitary conjugation and prove preservation of Hermiticity, positivity,
  trace, normalization, and physical-effect probability bounds.
- Prove that genuine physical effects separate density matrices.  Use arbitrary
  trace-test matrices only in a separately named supporting lemma and derive
  the physical theorem explicitly.
- Handle empty/nonempty index cases and real/complex differences visibly.

#### Completion Requirements

- `DensityMatrix` and `Effect` have actual positivity/trace/order invariants;
  arbitrary matrices are not accepted by aliases.
- Pure states and computational basis effects recover existing basis weights.
- Unitary conjugation produces a density matrix and Born values lie in the
  proved physical range.
- Physical-effect separation compiles.  Partial trace, Kraus channels, and
  quaternionic positivity remain absent and documented as Goal 3 work.

### 7-CHANNELS

#### Big Picture Objective

Prove the strongest rigorous same-space unitary-channel equivalences over the
minimal real/complex physical layer.

#### Detailed Implementation Plan

- Define unitary-induced `ChannelEq` as equality of conjugated density outputs
  for every density input.
- Define `AllMeasurementEq` using every density input and genuine physical
  effect, not arbitrary test matrices.
- Prove `ChannelEq → AllMeasurementEq` directly and the converse through Stage
  6 physical-effect separation.
- Prove complex global phase implies channel equality and, for explicitly
  nonempty finite complex unitary spaces, channel equality implies one global
  phase.
- Prove the corresponding real/complex projective-action equivalences, so the
  kernel of action on rays is related to channels by theorem rather than prose.
- Prove the analogous real channel/global-sign characterization or record the
  exact additional premise needed without weakening the complex theorem.
- Add channel congruence/equivalence laws and public circuit lifts.

#### Completion Requirements

- `ChannelEq U V ↔ AllMeasurementEq U V` compiles with exact scalar, dimension,
  density, effect, and unitarity assumptions.
- On nonempty finite complex unitaries,
  `ComplexGlobalPhaseEq U V ↔ ChannelEq U V` compiles in both directions.
- The real global-sign analogue is resolved honestly; quaternionic channels are
  neither invented nor inferred.
- Arbitrary trace-test separation is not substituted for quantification over
  physical effects, and all main theorems enter the axiom audit.

### 8-HIERARCHY

#### Big Picture Objective

Prove the complete valid implication graph and demonstrate every material
failed converse or incomparability with exact witnesses.

#### Detailed Implementation Plan

- Prove all arrows in the target complex-unitary graph, the state-phase-to-
  distribution chain, and the certified-basis restricted equivalences.
- Prove output-row phase is equivalent to all-pure-input basis measurement under
  the exact finite assumptions justified by row-functional separation.
- Add narrow witnesses for exact versus global phase, input versus output phase,
  superposition sensitivity, basis measurement versus phase consistency, and
  output measurement versus channel equality.
- Repackage the existing product-input ordering witness at precisely one-input
  state strength and retain the left-quaternion-phase counterexample.
- Put counterexamples and exhaustive finite diagnostics in a heavy audit leaf,
  not the semantic core.

#### Completion Requirements

- Every drawn arrow is a Lean theorem and every asserted non-arrow has a Lean
  witness satisfying the relevant unitary/normalization hypotheses.
- Input/output phase incomparability and the restricted nature of basis-
  behavior implications are explicit.
- No one-input witness is promoted to an all-basis or all-pure circuit relation.
- The published diagram, theorem names, examples, and axiom audit agree.

### 9-CROSSMODEL

#### Big Picture Objective

Classify the existing realification and complexification simulations with
proof-bearing cross-space relations rather than same-space equivalence names.

#### Detailed Implementation Plan

- Add `Semantics/Simulation.lean` definitions for exact operator embedding,
  state intertwining, decoded basis-measurement agreement, decoded distribution
  agreement, and explicitly parameterized top-state/marginal policies.
- Wrap `eval_realifyCircuit`, `eval_complexifyCircuit`, quaternion-to-real,
  scheduled, exact compiler, and Equation 63/reindexing results at their exact
  operator levels.
- Wrap state-evolution, arbitrary pure-top, bottom-probability, normalized
  distribution, finite-event, and deterministic-pushforward theorems at their
  actual input and observation scopes.
- Add any missing composed distribution/event/postprocessing wrapper only when
  it is an immediate theorem from completed Goal 1 results.
- Explicitly classify current simulations as not proving same-space equality,
  ray equality, mixed-top behavior, channel equality, or all measurements.
- Mark unitary equivalences onto embedding images as algebraic/nonbehavioral.

#### Completion Requirements

- Every existing simulation comparison family has a compiling wrapper in its
  strongest relation with scalar/index/added-wire/top-state/marginal data.
- Cross-model certificates are not declared `Equivalence` instances and cannot
  be used as same-space equality by simplification.
- Operator, state, basis-distribution, event, and postprocessing levels remain
  separately named.
- Focused simulation builds, existing examples, negative classification checks,
  and audits pass.

### 10-APPROX

#### Big Picture Objective

Add a rigorous metric comparison boundary without pretending to solve finite
precision or compilation.

#### Detailed Implementation Plan

- Define spectral/Euclidean induced operator distance through the appropriate
  finite continuous-linear-map representation selected by Stage 1 probes.
- Define `OperatorClose ε U V` and mapped/cross-model variants only where the
  normed spaces genuinely match.
- Define complex phase-aware operator closeness existentially over one unit
  global phase, quaternion operator closeness only over central signs, state-ray
  closeness over the correct sided phase action, and total-variation distance
  for finite distributions.
- Prove nonnegativity, symmetry, triangle inequality, zero distance iff exact
  equality, monotonicity in the budget, and additive composition/error bounds
  supported by the chosen norm.
- Give an exact counterexample to fixed-`ε` transitivity and show raw distance
  remains phase-sensitive, for example between `I` and `-I`.
- Prove the smallest useful state/output-weight bound needed to classify the
  relation, leaving code generation and accumulated finite-precision circuit
  budgets to Goal 3.

#### Completion Requirements

- The distance is the documented Euclidean induced operator norm, not an
  accidental entrywise or `ℓ∞` norm.
- `OperatorClose 0` agrees with exact equality; fixed positive-budget closeness
  is never given an `Equivalence` instance.
- Raw, phase-aware, state-ray, and distribution distances have distinct names
  and no quaternion operator metric minimizes over arbitrary unit quaternions.
- Triangle/error theorems expose the changed budget explicitly.
- No scalar encoder, rounding algorithm, synthesis compiler, or runtime claim
  is smuggled into this stage.

### 11-REGISTRY

#### Big Picture Objective

Give every discovered public semantic comparison a checked strongest
classification and remove ambiguous equivalence prose across the project.

#### Detailed Implementation Plan

- Add a proof-bearing wrapper leaf such as
  `Semantics/ExistingResults.lean` and keep any metadata/attribute registry thin.
- Complete `docs/EquivalenceClassification.md` with one row per frozen Stage 1
  cohort item: declaration, same/cross space, scalar, subject, input scope,
  observation scope, phase side, exactness, ancilla/marginal policy, strongest
  wrapper, weaker consequences, and strictness witness where applicable.
- Implement a checker ensuring every frozen cohort item appears exactly once
  and every behavioral label points to a theorem, while nonbehavioral/resource/
  algebraic-image entries have explicit dispositions.
- Check the separate `Goal2SemanticAPIManifest` for exact coverage of every new
  public semantic definition, hierarchy theorem, wrapper, counterexample, and
  metric declaration, including its consumer and axiom-audit evidence. Never
  add those declarations to the frozen cohort.
- Update README, Architecture, Conventions, Traceability, Corrections, release
  documentation, and public docstrings to remove unqualified “equivalent” or
  “same behavior.”
- Close and document the two transferred ray rows, then rebaseline Goal 3's
  immutable 47-row cohort, expected 45-row residual worklist, Lean source count,
  correction count, and axiom-audit count from actual results.

#### Completion Requirements

- Cohort-registry checksum equals the frozen `Goal1ComparisonCohort` with no
  duplicate, missing, or label-only row.
- The independent Goal 2 API-manifest check has no missing, duplicate, or
  unaudited public semantic export and leaves the cohort checksum unchanged.
- Every comparison wrapper compiles and every noncomparison disposition is
  justified; algebraic `EquivImage` declarations are visibly nonbehavioral.
- Documentation and Lean names agree on input/observation/phase/exactness scope.
- Both transferred traceability rows and every affected correction/dependent
  are folded back before Goal 3 is rebaselined.

### 12-RELEASE

#### Big Picture Objective

Publish the semantic comparison layer as a stable prerequisite that Goal 3 can
use without learning the retrofit's implementation history.

#### Detailed Implementation Plan

- Stabilize semantic namespaces, imports, relation names, docstrings, examples,
  registry tooling, and public-root exposure.
- Extend `QuaternionicComputing/AxiomAudit.lean` with every main relation,
  hierarchy theorem, quotient descent, channel theorem, cross-model wrapper,
  distance theorem, and strictness witness.
- Run focused/adjacent builds, a clean public-root build, explicit audit build,
  warning-as-error checks, registry checker, source/shortcut/stale-path/
  artifact/whitespace scans, and `git diff --check`.
- Compile a downstream file importing only `QuaternionicComputing` and checking
  representative relations at every layer.
- Independently audit the semantic graph, registry coverage, the two source-row
  closures, Goal 3 prerequisite/rebaseline, and all completion requirements.

#### Completion Requirements

- The pinned clean build, explicit axiom audit, strict source checks, registry
  checker, downstream import smoke, scans, and diff checks all pass.
- No completed module contains a proof hole, project-specific axiom, unsafe or
  opaque shortcut, false equivalence instance, or classification without proof.
- Every pre-retrofit public comparison claim has exactly one strongest checked
  classification, every new Goal 2 semantic export has exactly one API-manifest
  entry, and the complete published hierarchy has no unsupported arrow.
- `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` have terminal proved
  statuses and Goal 3 records them `closedByGoal2` with exact evidence.
- Goal 3's plan, prompt, expected residual ledger, semantic prerequisites, and
  counts are synchronized with the actual Goal 2 release.
- A final report lists the APIs, theorem hierarchy, strictness witnesses,
  classified existing results, deliberate Goal 3 boundaries, build/audit
  evidence, and downstream usage guidance.

## Stage Status

- [x] 1-INVENTORY
- [x] 2-CORE
- [x] 3-PHASE
- [ ] 4-RAYS
- [ ] 5-BASIS
- [ ] 6-DENSITY
- [ ] 7-CHANNELS
- [ ] 8-HIERARCHY
- [ ] 9-CROSSMODEL
- [ ] 10-APPROX
- [ ] 11-REGISTRY
- [ ] 12-RELEASE
