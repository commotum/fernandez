# 8-HIERARCHY

## Current Facts

- Stages 1--7 are independently closed. The checkpoint has 80 Lean sources
  including the public root, 941 exact Goal 2 semantic-manifest entries, 104
  resolving consumers, 207 direct manifest/root-audit labels, and 393 root
  axiom commands. The exact release union remains `propext`,
  `Classical.choice`, and `Quot.sound`.
- The exact, phase, ray, computational-basis, density/effect, and same-space
  unitary-channel relations are already stable public APIs. Stage 8 must prove
  and audit their complete valid implication graph; it must not rename or
  redefine those relations.
- Existing real/complex/quaternion operator theorems already cover exact
  equality to global/central phase, global/central phase to input phase,
  output phase and projective action, input phase to basis measurement,
  output phase to basis and all-pure-input basis measurement, and projective
  action to all-pure-input basis measurement.
- Existing Stage 7 theorems identify, on explicitly inhabited bundled real and
  complex square unitaries, global phase, raw projective action, normalized
  projective action, `ChannelEq`, and `AllMeasurementEq`. Their circuit lifts
  are evaluator-backed and cover zero-wire circuits through the inhabited
  `BitBasis W` space.
- Existing state theorems cover exact normalized representative equality to
  scalar-correct phase equality, phase equality to ray-constructor equality
  and basis weights, and basis-weight equality iff packaged normalized
  distribution equality. Distribution equality already implies every finite
  event equality and every deterministic pushforward equality; the converses
  have not yet been packaged as public iff theorems.
- Stage 5 already proves the complete certified-basis equivalences for real,
  complex, and quaternionic matrices and chronological circuits:
  `SameBasisBehavior`/`SameCircuitBasisBehavior` is equivalent to the
  scalar-correct input phase, output phase, and `BasisMeasurementEq`. Stage 8C
  should consume and audit that API rather than duplicate it.
- The main missing covering arrow is the converse from
  `PureInputBasisMeasurementEq` to output-row phase. A compiled square-unitary
  prototype proves it for all three scalars using only the first matrix's
  unitarity. A stronger rectangular proof is being checked: extend normalized
  agreement homogeneously to raw inputs, select one nonzero anchor per row,
  and use two-support cancellation inputs to force one output-row phase. The
  empty input type must remain an explicit, valid boundary rather than an
  impossible premise.
- Existing rational real/complex rotation and input/output-twist diagnostics
  already prove exact/global strictness, global-to-input/output strictness,
  input/output incomparability, input-phase superposition sensitivity, and
  output-phase preservation of all-pure basis statistics without projective
  action. Stage 7 can now repackage the same unitary twists as explicit
  failures of channel and all-effect equality.
- Existing diagnostics also prove the vacuity of raw basis-transition
  biconditionals on nonmonomial unitaries, the normalized quaternionic
  left-phase failure, the dimension-one quaternionic projective-kernel
  exception, and a one-fixed-input quaternionic ordering witness with equal
  complete basis weights but unequal right rays. A separate complex
  equal-basis-weights/not-one-ray witness is still required.

## Updated Assumptions

- The hierarchy is a poset with incomparable branches, not one strength chain.
  Same-space representative/ray comparisons, observation comparisons,
  certified classical behavior, and channels must remain visibly separate.
- The published real/complex unitary graph should use existing Stage 7 iff
  theorems rather than reproving the phase kernel. Stage 8 adds only missing
  edges, useful composed eliminators, and exhaustive consumers.
- The strongest row-phase converse that strict-compiles will be exported. The
  preferred theorem is rectangular and requires only finite input indices; the
  already checked square-unitary theorem is the honest fallback. Any retained
  unitarity, decidable-equality, or nonempty hypothesis must be justified by
  the proof and exposed in the theorem name or signature.
- Quaternionic output-left phase can be included in the row-functional
  converse only with a checked noncommutative proof. It must never be inferred
  from the commutative `RCLike` channel layer.
- The event and pushforward converses should be stated at their exact finite
  codomain scope. Identity pushforward or singleton events may recover the
  distribution; this is a proof, not permission to conflate distributions
  with channels or randomized postprocessing.
- No new partial trace, quaternionic density/channel, cross-model simulation,
  operator metric, schedule/resource, or compiler claim belongs in Stage 8.

## Big Picture Objective

Prove the complete valid same-space semantic implication graph for normalized
states, finite real/complex/quaternion operators and chronological circuits,
and certified basis-classical implementations. Supply exact unitary or
normalized witnesses for every material failed converse and incomparable
branch, package the graph through real consumers, and publish no arrow whose
input or observation scope is stronger than its proof.

## Detailed Implementation Plan

### 8A-ARROWS

- Add a narrow output-phase hierarchy leaf. Prove real output sign, complex
  output phase, and—if the noncommutative proof strict-compiles—quaternion
  output-left phase from equality of all normalized pure-input basis weights.
  Prove the corresponding iff theorems using the existing forward directions.
- Lift the row-phase iff results through `OrderedCircuit.eval`. Circuit
  statements must be semantic evaluator theorems; they do not compare gate
  lists, schedules, or resources.
- Add scalar-specialized eliminators from all-pure-input basis measurement to
  basis measurement so callers do not have to resupply the normalization proof
  for computational-basis kets.
- Add a finite-state hierarchy leaf proving packaged distribution equality iff
  equality of all finite-event weights and iff equality of all deterministic
  pushforwards at the exact stated codomain universe. Connect those results to
  the existing `BasisWeightEq` iff theorem without defining a second
  distribution relation.
- Add a thin operator/circuit graph leaf only for useful missing composed
  arrows, such as real/complex channel or all-effect equality to pure-input and
  basis-measurement equality. Reuse Stage 7 global/projective iff theorems and
  keep every `Nonempty`/unitary premise visible.
- Compile aggregate graph consumers covering the intended complex-unitary
  diamond, its real analogue, the all-three state chain, and circuit lifts.

### 8B-WITNESSES

- Put all strictness and incomparability results in a non-root hierarchy audit
  leaf. Reuse the existing rational unitary rotation/twist definitions through
  named wrappers rather than copying their arithmetic proofs.
- Bundle the real and complex rotation/twist matrices as `UnitaryOperator`
  values and prove explicit `¬ ChannelEq` and `¬ AllMeasurementEq` results from
  the checked Stage 7 phase kernels. Record that output phase still gives
  `PureInputBasisMeasurementEq` while the channel fails.
- Repackage the input-twist diagnostics as basis-measurement agreement with a
  concrete normalized superposition that refutes all-pure agreement. Repackage
  input/output twists as the two directions of phase incomparability.
- Add normalized rational complex states with identical complete basis weights
  but no common complex phase. Prove the corresponding
  `BasisWeightEq`/`NormalizedDistributionEq` and negated
  `ComplexStatePhaseEq`/`ComplexRay.mk` equality facts.
- Wrap the existing quaternionic product-ordering result at exactly one input
  as `OutputWeightEqAt`, pair it with its existing unequal-right-ray theorem,
  and do not promote it to `BasisMeasurementEq` or all-pure agreement.
- Consume the existing normalized left-phase failure, raw-transition vacuity,
  and quaternionic rank-one exception under their exact scopes.
- Every diagram non-arrow must point to a named witness whose normalization,
  unitarity, dimension, and input scope compile in the same audit leaf.

### 8C-CLASSICAL

- Import the stable Stage 5 basis-behavior circuit leaf and build one complete
  aggregate consumer for the nine matrix and nine circuit real/complex/
  quaternion iff results.
- Verify that every theorem is restricted to supplied
  `BasisPermutationImplementation`/`BasisClassicalCircuit` certificates and
  that the induced permutation is the compared datum.
- Retain the nonmonomial-vacuity witness as the negative boundary showing why
  no corresponding equivalence may be drawn for arbitrary unitaries.

### Integration

- Add only stable hierarchy leaves to `QuaternionicComputing.lean`; keep the
  hierarchy audit non-root.
- Append every new stable declaration once to
  `docs/Goal2SemanticAPIManifest.json` with all seven axes, a resolving
  consumer, and direct or transitive axiom evidence. Preserve the first-941
  entry prefix and the frozen Goal 1 cohort checksum.
- Extend `QuaternionicComputing/AxiomAudit.lean` with representative arrows and
  every published strictness family. Update the classification diagram,
  README, architecture, conventions, traceability/corrections only when a
  paper claim changes, release evidence, and Goal 3 checkpoint counts.

## Build Structure

- `QuaternionicComputing/Semantics/Hierarchy/OutputPhase.lean`: stable
  row-functional converses and iff theorems, with only the imports required for
  real/complex/quaternion phase and pure-input measurement semantics.
- `QuaternionicComputing/Semantics/Hierarchy/State.lean`: stable finite
  distribution/event/pushforward iff theorems and scalar state-chain wrappers.
- `QuaternionicComputing/Semantics/Hierarchy/Operator.lean`: optional thin
  composed same-space operator/circuit graph; create it only for declarations
  with real downstream consumers.
- `QuaternionicComputing/Semantics/HierarchyAudit.lean`: non-root aggregate
  coverage, strictness witnesses, fixed-input boundaries, and certified-basis
  consumers. It may import existing audit leaves; stable hierarchy leaves may
  not.
- Avoid edits to State, Matrix, Circuit, density/effect, phase-kernel, and
  existing witness leaves. Public-root, AxiomAudit, manifest, and documentation
  edits occur only after focused leaves and consumers pass.
- Focused builds target each new leaf. Adjacent builds include
  `OperatorPhase.ComplexRealAudit`, `OperatorPhase.QuaternionAudit`,
  `BasisBehaviorAudit`, `ChannelAudit`, the public root, and AxiomAudit as
  appropriate.

## Boundary Checks

- `ExactOperatorEq` and `ExactCircuitEq` remain literal same-space matrix and
  evaluator equality. No relation on circuit syntax is introduced.
- Input-column phase and output-row phase remain incomparable. Over
  quaternions, input phase acts on the right and output phase on the left.
- `BasisMeasurementEq` sees only basis preparations. It is not all-pure,
  all-density, channel, or all-effect equality.
- `PureInputBasisMeasurementEq` sees every normalized pure input but only
  computational-basis output weights. Its output-row-phase iff does not imply
  projective, channel, or all-effect equality.
- `ChannelEq` compares complete density outputs and `AllMeasurementEq` uses
  every genuine effect. Stage 8 may derive weaker observations but may not
  reverse those arrows from basis-only data.
- State ray equality is scalar-correct quotient equality. Equal basis
  distributions, events, or pushforwards do not recover a ray.
- `SameBasisBehavior` is used only on certified basis-permutation
  implementations. The raw transition biconditional remains diagnostic.
- The quaternionic one-input ordering witness remains one-input evidence.
- Cross-model encoders/decoders and metric error budgets remain owned by
  Stages 9 and 10.

## No-Cheating Checks

- Do not define a new relation so a desired implication is tautological; prove
  each arrow through the stable relation definitions.
- Do not use impossible normalized inputs or hidden nonempty premises to prove
  a row-phase converse. Check the empty input type explicitly.
- Do not infer row phase from basis inputs alone; the proof must consume the
  all-normalized-pure-input hypothesis.
- Do not infer channel or all-effect equality from output-row phase or basis
  statistics. Compile unitary output-twist counterexamples.
- Do not generalize a concrete/fixed-input witness through prose or metadata.
- Do not count a manifest label, diagram edge, aggregate conjunction, or green
  build as the proof-bearing theorem.
- No `sorry`, `admit`, `sorryAx`, declaration axiom, unsafe/opaque shortcut,
  heartbeat override, public audit import, silent frozen-cohort edit, or
  project-specific axiom.

## Completion Requirements

- Every arrow in the published real/complex unitary graph and all-three-scalar
  state chain names a compiling Lean theorem with exact assumptions.
- Output-row phase iff all-pure-input basis measurement compiles at least for
  finite square real/complex unitaries; export the stronger rectangular and/or
  quaternion theorem only if independently checked.
- Distribution equality iff all event weights and iff all deterministic
  pushforwards compiles, including empty and singleton finite boundaries.
- Every asserted failed converse or incomparable branch has a normalized,
  unitary where relevant, exact Lean witness. The output-phase/channel
  separation and complex distribution/ray separation are explicit.
- Certified-basis equivalences are completely consumed without creating an
  unrestricted `SameBasisBehavior` theorem.
- A non-root audit consumes every stable Stage 8 declaration and exercises all
  existing arrows/witnesses claimed by the final diagram.
- Public-root, exact manifest set/seven-axis/name/consumer/audit checks,
  focused/adjacent/root/default builds, warnings-as-errors, downstream smoke,
  exact axiom union, frozen checksum, forbidden-token/import-boundary/artifact/
  whitespace/Markdown/diff checks all pass.
- Documentation and Goal 3 publish the checked graph and exact missing-arrow
  boundaries without adding a paper correction unless the formal proof changes
  a source claim or assumption.

## Stage Results

- Inventory is in progress. No Stage 8 theorem is counted complete until the
  selected row-phase proof, state converses, strictness audit, manifest,
  builds, and independent closure review all pass.
