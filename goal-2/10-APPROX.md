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
  Stage 10 will use the stronger native quaternion norm only after retaining
  its explicit underlying-real construction in public names and documentation.
- There is no finite-precision scalar encoder, rounding algorithm, primitive
  gate synthesis procedure, accumulated circuit budget, runtime theorem, or
  approximation relation in the current stable library. `EQC-042` is the
  frozen exact-versus-approximate boundary assigned to this stage; Goal 3 still
  owns numerical compilation and complexity consequences.

## Updated Assumptions

- `operatorDistance` for real/complex matrices will be literal metric distance
  under the explicitly opened L2 operator-norm scope. A named theorem will
  identify it with `‖U - V‖` and the corresponding continuous-linear-map norm,
  preventing an entrywise or `ℓ∞` reinterpretation.
- Quaternionic operator distance will be the native induced norm of the
  underlying real-linear left action on finite quaternionic L2 columns. It will
  not install a matrix norm instance and will not be called an `RCLike` or
  complex spectral norm. A complexification-pullback distance may be exported
  separately only if its relation to the native norm is proved; otherwise it
  remains an explicitly mapped diagnostic.
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

- Implementation pending.
