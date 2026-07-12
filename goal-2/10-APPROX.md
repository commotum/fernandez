# 10-APPROX

## Current Facts

- Stage 9 and all three cross-model milestones are complete. The current tree
  has 90 Lean sources including the public root, 1,100 semantic-manifest
  declarations, 140 resolving consumers, 308 direct audit labels, 494 root
  axiom commands, and 20 local simulation-audit commands. The final Stage 9
  combined build passes at `2769/2769`, the cached default build completes
  `2767` jobs, and independent integrated review returned **PASS**.
- Pinned mathlib's scoped `Matrix.Norms.L2Operator` instance is the Euclidean
  induced operator norm for finite rectangular matrices over `RCLike` scalars.
  It exposes `Matrix.l2_opNorm_def`, `Matrix.l2_opNorm_mulVec`,
  `Matrix.l2_opNorm_mul`, `Matrix.l2_opNorm_conjTranspose`, and square-matrix
  `Matrix.toEuclideanCLM`. A strict probe at
  `/private/tmp/Stage10OperatorProbe.lean` proves the metric laws, a two-factor
  perturbation bound, exact one-dimensional distances, and fixed-budget
  nontransitivity.
- Quaternionic matrices cannot instantiate the `RCLike` L2 matrix norm:
  quaternions are a noncommutative `NormedDivisionRing`, not an `RCLike` or
  `NormedField`. A strict probe at
  `/private/tmp/Stage10QuaternionProbe.lean` instead constructs the native
  quaternionic action as a continuous real-linear map
  `PiLp 2 (fun _ => ℍ) →L[ℝ] PiLp 2 (fun _ => ℍ)`. The construction is
  injective and already proves zero/add/neg/sub, multiplication-as-composition,
  norm-zero detection, submultiplicativity, and the induced mul-vector bound.
  No global or scoped norm instance is installed on quaternionic matrices.
- `PiLp 2` supplies a single finite column L2 metric for real, complex, and
  quaternionic amplitudes. `/private/tmp/Stage10PiLpProbe.lean` strict-compiles
  nonnegativity, identity of indiscernibles, symmetry, triangle inequality,
  and invariance under unit right multiplication over any `NormedDivisionRing`.
  This supports correctly right-sided complex and quaternionic state-ray
  closeness without numerical phase minimization.
- `/private/tmp/Stage10TVProbe.lean` strict-compiles the standard finite total-
  variation distance `(1/2) * ∑ |μ-ν|`, its nonnegativity, symmetry, triangle,
  zero/equality characterization, upper bound by one, deterministic-
  pushforward contraction, and the sharp finite-event bound.
- `/private/tmp/Stage10MetricProbe.lean` independently compiles exact zero-
  budget bridges for complex global phase, quaternion central sign through an
  explicitly mapped metric, complex/quaternion state rays, a normalized
  complex output-column bound, a complex-unitary fixed-budget nontransitivity
  chain `1, I, -1`, raw distance `d(I,-I)=2`, and a Boolean distribution chain.
  The stable implementation uses the stronger native quaternion norm, retains
  its explicit underlying-real construction in public names/documentation, and
  proves equality with canonical complexification's L2 operator norm.
- Stage 10 now supplies semantic approximation relations over exact
  mathematical values. There is still no finite-precision scalar encoder,
  rounding algorithm, primitive gate synthesis procedure, accumulated circuit
  budget, or runtime theorem. `EQC-042` is refined by the new metric boundary;
  Goal 3 still owns numerical compilation and complexity consequences.

## Updated Assumptions

- `operatorDistance` for real/complex matrices is literal metric distance
  under the explicitly opened L2 operator-norm scope. Named theorems identify
  it with `‖U - V‖` and the corresponding continuous-linear-map norm,
  preventing an entrywise or `ℓ∞` reinterpretation.
- Quaternionic operator distance is the native induced norm of the underlying
  real-linear left action on finite quaternionic L2 columns. It installs no
  matrix norm instance and is not called an `RCLike` or complex spectral norm.
  `quaternionOperatorNorm_eq_l2_opNorm_complexify` proves exact equality with
  the L2 operator norm of canonical complexification, so no unrelated mapped
  diagnostic is substituted for the native construction.
- Raw operator closeness is a budget relation. It is reflexive only for
  nonnegative budgets, symmetric at a fixed budget, and composes by adding
  budgets. It receives no `Equivalence` instance and no fixed-budget
  transitivity theorem.
- Complex phase-aware closeness quantifies one unit complex global phase.
  Quaternion phase-aware operator closeness quantifies only a central real
  sign `s` with `s*s=1`; arbitrary unit-quaternion matrix-wide phase remains
  forbidden. State-ray closeness instead uses the existing correct right action
  and may quantify an arbitrary unit complex/quaternion scalar.
- Existential phase-aware closeness is preferable to defining a numerical
  infimum over phases in this stage. It states exactly the error-budget claim
  needed by the classification and avoids importing compactness/attainment
  machinery merely to manufacture a computed quotient metric.
- `MappedOperatorClose` is directional and only compares a mapped source with a
  target that already inhabits one common normed RCLike matrix space. It is not
  symmetric cross-model equality and does not hide an index/scalar embedding.
- The smallest useful quantum consequence is an L2 output-column bound:
  operator error times input L2 norm bounds the output-column error. Normalized
  real/complex/quaternionic inputs give factor one without requiring unitarity;
  unitarity is needed only when additionally packaging outputs as normalized
  probability distributions.
- Total variation uses the standard half-L1 convention. It controls every
  finite event sharply and contracts under deterministic pushforward. It does
  not model randomized channels, trace distance, physical effects, or runtime.

## Big Picture Objective

Add a reusable, proof-bearing metric boundary for finite operators, pure-state
rays, and classical output distributions. Prove exact zero-budget bridges,
metric/error laws, phase-correct variants, observable consequences, and exact
fixed-budget counterexamples while keeping finite precision, synthesis,
runtime, and false equivalence claims outside Goal 2.

## Detailed Implementation Plan

- Add `QuaternionicComputing/Semantics/Approximation/Operator.lean` as the
  low-dependency real/complex operator core:
  - `operatorDistance` and `OperatorClose` under the scoped Euclidean induced
    norm;
  - nonnegativity, symmetry, triangle, zero iff `ExactOperatorEq`, monotonicity,
    nonnegative-budget reflexivity, and additive-budget composition;
  - left/right/two-factor multiplication error laws, unitary additive
    composition where justified, and the raw mul-vector L2 bound;
  - directional `mappedOperatorDistance`/`MappedOperatorClose` with a zero-
    budget `ExactOperatorEmbedding` bridge;
  - rectangular reindex isometry only if the compiled linear-isometry proof
    remains narrow and does not require a global norm choice.
- Add `Semantics/Approximation/OperatorPhase.lean` for explicit real and complex
  global-phase budget relations. Prove zero-budget equivalence with
  `RealGlobalSignEq` and `ComplexGlobalPhaseEq`, monotonicity, symmetry, and
  additive-budget composition. No arbitrary quaternion scalar belongs here.
- Add `Semantics/Approximation/Quaternion.lean` for the unbundled native
  quaternionic induced norm/distance, `QuaternionOperatorClose`, its metric and
  multiplication/mul-vector laws, and `QuaternionCentralSignClose`. Prove the
  zero-budget bridge to `QuaternionCentralSignEq` and the valid sign-aware
  symmetry/additive laws without installing a quaternionic matrix norm instance.
- Add `Semantics/Approximation/State.lean` with generic `columnL2Distance` and
  `ColumnClose`, unit-right-multiplication isometry, and normalized
  `RealStateRayClose`, `ComplexStateRayClose`, and `QuaternionStateRayClose`.
  Prove zero-budget bridges to the existing state-phase relations plus
  monotonicity, symmetry, and additive-budget composition with the correct
  phase order. Export real/complex operator-to-output-column bounds here; add
  the quaternionic bound through the native operator leaf.
- Add `Semantics/Approximation/Distribution.lean` with
  `totalVariationDistance` and `DistributionClose`; prove nonnegativity,
  symmetry, triangle, zero iff distribution equality, upper bound one,
  monotonicity, additive-budget composition, sharp point/event bounds, and
  deterministic-pushforward contraction.
- Add `Semantics/Approximation/Strictness.lean` with exact finite witnesses:
  - `OperatorClose 1` on real scalar matrices `0,1,2` is not transitive;
  - preferably the stronger complex-unitary chain `1,I,-1` at budget `√2`;
  - raw complex distance between `I` and `-I` is `2`, while global-phase close
    holds at budget zero;
  - Boolean delta/uniform/delta distributions have distances `1/2,1/2,1`, so
    fixed-half distribution closeness is not transitive either.
- Add a non-root `Semantics/ApproximationAudit.lean` with exact-allocation
  aggregate consumers for every stable declaration, concrete zero-wire and
  nontrivial unitary values, phase-side checks, mapped cross-model examples,
  output-column bounds, event/pushforward contraction, and every strictness
  witness. No stable module imports the audit.
- Promote only stable approximation leaves through `QuaternionicComputing.lean`.
  Add selected main declarations and all strictness witnesses to
  `AxiomAudit.lean`; append every new public semantic declaration exactly once
  to the Goal 2 manifest with seven nonempty axes and a real aggregate consumer.
- Fold exact names, scopes, counts, hashes, builds, axiom results, the
  `EQC-042` disposition, and the explicit Goal 3 boundary into all affected
  docs, traceability, corrections only if a paper issue emerges, release
  evidence, Goal 3 prerequisites, this report, and the master plan.

## Build Structure

- `Semantics/Approximation/Operator.lean`: stable public RCLike operator metric
  and directional mapped comparison; imports only the exact semantic core and
  mathlib's L2 matrix norm.
- `Semantics/Approximation/OperatorPhase.lean`: stable public real/complex
  phase-aware operator budgets; imports the operator core and existing
  real/complex exact phase leaf.
- `Semantics/Approximation/Quaternion.lean`: stable public quaternionic native
  real-linear induced norm and central-sign budget; imports the quaternion
  exact phase leaf plus finite-dimensional real-linear/L2 support.
- `Semantics/Approximation/State.lean`: stable public finite L2 column and
  right-ray budgets plus output-column consequences; imports the operator,
  quaternion, and existing state-phase leaves.
- `Semantics/Approximation/Distribution.lean`: stable public scalar-independent
  total-variation layer; imports only `State/Distribution` and ordered finite-
  sum support.
- `Semantics/Approximation/Strictness.lean`: stable public exact witnesses;
  imports only the approximation leaves needed by those examples.
- `Semantics/ApproximationAudit.lean`: non-root diagnostic allocation and
  concrete consumers.
- `QuaternionicComputing.lean`: public re-export of the stable leaves only.
- `QuaternionicComputing/AxiomAudit.lean`: selected direct endpoints from the
  completed manifest.
- Focused builds will target each stable leaf separately, then the non-root
  audit. Adjacent builds will include existing hierarchy/simulation consumers,
  the public root, release audit, generated manifest checks, and a root-only
  downstream approximation smoke.

## Boundary Checks

- Every real/complex operator theorem is tied to
  `Matrix.Norms.L2Operator`; no unscoped matrix norm is accepted as evidence.
- The quaternionic induced norm remains an explicit definition through an
  underlying real continuous-linear map. No `Norm`, `MetricSpace`, `RCLike`,
  or `CStarRing` instance is added to quaternion matrices.
- Phase-aware operator relations use one scalar globally. Complex matrices use
  one unit complex scalar; quaternion matrices use one central real sign only.
  State rays retain right multiplication, including noncommutative phase order.
- Mapped closeness exposes the map and direction. A realified, complexified, or
  reindexed target is never called same-space raw operator equality.
- `OperatorClose 0` and its phase-aware variants recover the exact relations;
  positive fixed-budget closeness is never registered as reflexive/symmetric/
  transitive equivalence data beyond the separately proved valid laws.
- Output-column error is an L2 amplitude statement. Total variation concerns
  already packaged finite classical distributions. Neither is trace distance,
  channel diamond norm, all-effect approximation, or mixed-state semantics.
- No finite-precision representation, scalar rounding, primitive compiler,
  synthesis algorithm, accumulated gate budget, randomized computation,
  runtime, or complexity-class result is introduced.

## No-Cheating Checks

- Inspect every norm definition after elaboration and prove its CLM/induced-norm
  identity; a convenient entrywise or default Pi norm is forbidden.
- Do not define a phase-aware distance to be zero by quotienting first or by
  reusing the exact phase relation as the distance. The relation must contain a
  real metric inequality with an explicit unit witness.
- Do not quantify arbitrary unit quaternions in operator phase closeness. Such
  phases remain valid only for right state-ray closeness and the proved rank-one
  exact exception, not the general operator API.
- Do not give fixed-budget closeness an `Equivalence` instance or theorem named
  `trans`; only an explicitly additive-budget theorem is valid.
- Counterexamples must evaluate exact distances and, for the stronger complex
  witness, prove actual unitarity rather than assume it.
- Mapped relations cannot choose an encoder or identify source/target types
  internally; consumers supply and expose the map.
- No `sorry`, `admit`, `sorryAx`, declaration axiom, `opaque`, `unsafe`,
  heartbeat override, impossible premise, broad global norm/simp instance,
  public audit import, tracked generated artifact, or frozen-cohort edit.

## Completion Requirements

- RCLike and native quaternionic operator distances have checked induced-norm
  definitions, metric laws, zero/equality bridges, multiplication/mul-vector
  error bounds, and budget monotonicity/additive composition.
- Real/complex global-phase, quaternion central-sign, and all three normalized
  state-ray close relations have correct scalar sides and zero-budget bridges
  to the existing exact relations. Their symmetry and additive-budget laws
  compile; no numerical phase infimum or false quaternion operator phase is
  claimed.
- `MappedOperatorClose` retains an explicit map and common target space, with a
  zero-budget exact-embedding bridge and at least one real cross-model consumer.
- Total variation is exactly half L1 and has all promised metric, bound, event,
  and deterministic-pushforward theorems. `DistributionClose 0` is exact
  equality, while fixed positive budgets receive no equivalence instance.
- Exact real and complex-unitary operator counterexamples, raw phase
  sensitivity, phase-aware zero closeness, and the Boolean distribution
  counterexample all compile through concrete consumers.
- At least one normalized pure-state theorem turns operator error into an L2
  output-column bound with factor one; all scalar/unity assumptions remain
  explicit and no probability/channel conclusion is inferred without its
  hypotheses.
- Stable imports remain narrow, the public root exports no audit leaf, every
  public declaration has exactly one manifest row and resolving aggregate
  consumer, and every selected audit endpoint parses to a subset of the
  permitted standard axiom union.
- Focused, adjacent, combined, default, warning-as-error, root-only downstream,
  generated name/consumer, manifest/frozen-checksum, hole/shortcut/false-
  equivalence/norm-instance/import-boundary/artifact/Markdown/whitespace/stale-
  wording/diff checks pass.
- `EQC-042`, documentation, traceability, release/axiom evidence, corrections,
  Goal 3, this report, and the master plan agree on exactly what Stage 10 proves
  and what finite-precision work remains. Independent source, mathematical,
  manifest, and integrated closure reviews return **PASS** before Stage 10 is
  marked complete.

## Stage Results

- Added six stable approximation leaves with exactly 169 public declarations:
  `Operator` 24, `OperatorPhase` 23, `Quaternion` 48, `State` 43,
  `Distribution` 17, and `Strictness` 14. Their focused builds pass at 2,365,
  2,372, 2,376, 2,378, 2,345, and 2,374 jobs respectively, and every leaf
  passes direct warning-as-error compilation.
- `operatorDistance` is tied by theorem to the scoped L2 operator norm and its
  continuous-linear-map realization. `OperatorClose 0` is exactly
  `ExactOperatorEq`; multiplication, unitary additive composition, raw
  mul-vector, and directional mapped zero-budget embedding laws compile. The
  optional rectangular reindex-isometry extension was not exported: pinned
  mathlib has no narrow norm-reindex lemma, it would require broader isometry
  machinery, and no Stage 10 completion theorem depends on it.
- `RealGlobalSignClose` and `ComplexGlobalPhaseClose` quantify one scalar for
  the whole matrix and have exact zero-budget bridges plus valid
  reflexive/monotone/symmetric/additive-budget laws. No quaternionic definition
  occurs in that leaf.
- Quaternionic matrices use `quaternionMulVecCLM`, an explicit underlying-real
  continuous linear action on `PiLp 2`. The native norm detects zero, is
  submultiplicative, bounds matrix action and product perturbations, and gives
  the metric/budget laws. `QuaternionCentralSignClose` quantifies only a real
  `s` with `s*s=1`. No quaternionic matrix norm/metric/RCLike/CStar instance is
  installed. A checked real-linear L2 isometry proves
  `quaternionOperatorNorm_eq_l2_opNorm_complexify`.
- `columnL2Distance`, `ColumnClose`, and `RightUnitPhaseColumnClose` work over
  all three scalar conventions. Right multiplication is an L2 isometry, and
  the quaternionic composite witness has the noncommutative order
  `theta * eta`. The normalized real/complex/quaternionic `*StateRayClose`
  predicates remain on representatives, have zero-budget bridges to the exact
  state-phase relations, and provide normalized output-column bounds without
  unitarity or probability/channel overclaims.
- `totalVariationDistance` is exactly half L1. It satisfies the metric laws,
  is at most one, sharply bounds every finite point/event, and contracts under
  deterministic pushforward. Its fixed-budget relation has only additive
  composition.
- The strictness leaf proves exact real `0,1,2` nontransitivity at budget `1`,
  proves `1,I,-1` are genuine complex unitaries with distances
  `sqrt 2, sqrt 2, 2`, separates raw distance `2` from zero global-phase
  closeness, and proves the Boolean point/fair/point total-variation chain
  `1/2,1/2,1`.
- Added non-root `Semantics/ApproximationAudit.lean`. Its 24 source-order
  aggregates allocate all 169 stable declarations exactly as
  `15/5/4/2/5/8/8/13/11/11/5/7/1/12/7/5/5/5/3/6/13/4/9/5`.
  Concrete consumers cover an inhabited zero-wire basis, a nontrivial unitary,
  real-to-complex mapped zero closeness, quaternionic right phase, normalized
  singleton output bounds, finite events/pushforwards, and every strictness
  family. Its warning-as-error focused build passes at 2,383 jobs. All 16 local
  audit commands are nonempty and have exact union `propext`,
  `Classical.choice`, and `Quot.sound`.
- The public root exports all six stable leaves and no audit leaf. The root
  audit adds 42 Stage 10 commands, reaching 536 total; its parser covers
  `533 + 3` blocks and has the same exact standard-three union. The combined
  stable/audit/public-root/release-audit build passes at 2,775 jobs, and the
  cached default build passes at 2,773. The adjacent hierarchy/simulation-audit
  build passes at 2,745.
- `docs/Goal2SemanticAPIManifest.json` preserves the first 1,100 entries with
  hash `d98dc2ee741dd792c204e088c396c7cbf95b1cc02f98fadceeccf94938da0870`
  and appends all 169 declarations in exact source order. The manifest now has
  1,269 declarations, 164 resolving consumers, and 348 direct audit labels;
  the full hash is
  `298a8b5ebdf9e428f203d383473269dc77ca7944ee0663286fe930b9b1a3f5dc`.
  Generated checks resolve every name and consumer, all seven axes are
  nonempty, and the frozen Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- `EQC-042`, C-024, traceability, conventions, architecture, mathlib API notes,
  README, release/axiom reports, the master plan, and Goal 3 now distinguish
  this exact-object metric layer from finite encoding, rounding,
  code-to-value certification, accumulated circuit error, approximate
  compilation/synthesis, runtime, and uniformity. Stage 10 introduces no new
  paper correction; it sharpens the resolution of existing C-024.

## Completion Status

- Stage 10 implementation, allocation, manifest, public-root, and axiom gates
  pass. Independent source, mathematical, manifest, documentation, and
  integrated closure review remain required before `10-APPROX` is checked in
  the master plan.
