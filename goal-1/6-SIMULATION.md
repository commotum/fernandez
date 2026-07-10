# 6-SIMULATION

## Current Facts

- `OrderedCircuit.eval_map_of_denote_eq` lifts a gatewise denotation identity
  through chronological reverse-product evaluation using an actual matrix
  monoid homomorphism.
- `realifyPlacedGate_denote` and `complexifyPlacedGate_denote` provide the two
  required gatewise identities; both wire embeddings are bundled star-monoid
  homomorphisms.
- The same target wire type `AddedWire W := Unit ⊕ W` is used for every
  translated gate, and translated local arity is exactly source arity plus one.
- State columns and their matrix-action/bottom-weight theorems currently use
  sum indices.  A generic reindexing bridge is required before circuit-facing
  state evolution can be stated on `BitBasis (AddedWire W)`.
- `OrderedCircuit.eval_mem_unitary` proves source and target circuit operators
  unitary from local unitarity.  A reusable finite-vector lemma should connect
  matrix unitarity to normalized-state evolution instead of leaving
  “probability distribution” normalization implicit.
- Gate count is already list length.  Width, per-gate arity, arity bounds, and
  maximum arity need explicit machine-checked APIs; the empty-circuit edge case
  prevents an unconditional equality `targetMax = sourceMax + 1`.
- Stage 5's fixed-value `i`/`j` audit certifies the evaluation orientation used
  by the list induction.
- Repository-root `BUILD-PLAN.md` remains authoritative for the module split,
  focused builds, adjacent consumers, boundary scans, and fold-back.

## Updated Assumptions

- A shared `Simulation/Basic.lean` can own only scalar-generic transport from
  sum-index columns to the explicit added-wire basis and a parameterized
  bottom-weight operation.
- A narrow `Circuit/Cost.lean` can own reusable arity bounds/maximum arity and
  width facts without widening `Circuit/Basic.lean`.
- Complex-to-real and quaternion-to-complex whole-circuit results should live
  in separate leaves and import only their corresponding circuit/state
  embeddings plus shared simulation/cost infrastructure.
- Operator preservation, embedded state evolution, normalization, and
  pointwise observable preservation should remain separate exported theorems;
  a final named simulation theorem may package them but may not define the
  desired equalities into its semantics.
- The composed quaternion-to-real result is useful and algebraically cheap
  once both central translations are stable; it should be a separate leaf so
  it does not burden either primary simulation.

## Big Picture Objective

Prove the paper's two central finite ordered-circuit simulations at four
distinct levels—operator embedding, state evolution, normalized output, and
bottom computational-basis outcome equality—and machine-check the exact
one-wire/one-gate/one-local-wire overhead.  Then compose them into the corrected
two-added-rebit corollary where practical.

## Detailed Implementation Plan

- Add generic added-wire column transport and bottom-weight definitions, with
  exact top-sector evaluation, injectivity, reindexed matrix-action, and
  weight-sum lemmas.
- Add reusable circuit cost definitions for per-gate arity bounds and maximum
  local arity.  Prove membership/bound laws, exact map count, added width, exact
  per-gate `+1`, target bound `d+1`, and the correct maximum theorem including
  the empty-list case.
- Establish a reusable unitary matrix-action norm/total-weight theorem and
  normalized-state evolution constructors for complex and quaternionic source
  states (and real targets if needed).
- Define `realifyCircuit := List.map realifyPlacedGate` and
  `complexifyCircuit := List.map complexifyPlacedGate`.
- Prove whole-circuit operator identities via
  `OrderedCircuit.eval_map_of_denote_eq`, gate-count equality, shared width,
  per-gate support/arity preservation, arity-bound transformation, and local
  unitarity preservation.
- Define wire-facing versions of both state columns.  Prove translated circuit
  action commutes with each column and prove pointwise bottom-weight equality
  after arbitrary circuit evolution.
- Package corrected Theorems 2 and 4 with explicit hypotheses and conclusions;
  keep operator equality, state equality, and observable equality separately
  accessible.
- Add a composed quaternion-to-real leaf proving operator, count, width, arity,
  and (if the nested weight API stays clean) state/observable consequences for
  the corrected Corollary 1.
- Add non-real complex and genuinely quaternionic end-to-end examples that
  exercise public circuit translation/evaluation and measurement APIs.
- Update root imports, axiom audit, traceability, C-010/C-019/C-024, README, and
  architecture/conventions only after leaves stabilize.

## Build Structure

- `Simulation/Basic.lean`: low-dependency public bridge importing
  `Circuit/AddedWire` and `State/Basic`; no concrete embedding or circuit
  translation.
- `Circuit/Cost.lean`: generic public resource leaf importing `Circuit/Basic`;
  owns arity/maximum/width facts, not simulation-specific statements.
- `State/Unitary.lean` (only if required): proof/API leaf importing
  `State/Basic` and the narrow matrix star/unitary surface; owns unitary
  total-weight and normalized evolution, not circuit translation.
- `Simulation/ComplexToReal.lean`: primary proof/API leaf importing the real
  circuit/state embeddings and shared basic/cost/unitary leaves.
- `Simulation/QuaternionToComplex.lean`: primary proof/API leaf importing only
  the quaternionic circuit/state embeddings and shared leaves; no determinant
  or real-simulation import.
- `Simulation/QuaternionToReal.lean`: composition proof leaf importing the two
  stable primary simulations.
- `Simulation/Examples.lean`: narrow diagnostic/example leaf importing the
  completed simulations; examples do not sit in high-fanout core modules.
- `QuaternionicComputing.lean` and `AxiomAudit.lean`: high-fanout public/audit
  consumers changed only after focused and adjacent simulation builds pass;
  this root change requires a full build.

## Boundary Checks

- Circuit translation must be `List.map` of the actual Stage 5 placed-gate
  translations; it may not store or substitute the desired embedded global
  operator.
- Whole-circuit operator preservation must use the public chronological
  evaluator and its monoid-hom induction law, not a new evaluator with a
  convenient definition.
- State evolution must apply the translated public operator to a separately
  defined reindexed state column.  It may not define the target final state as
  the theorem's desired right side.
- Observable preservation must expand to the existing scalar basis weights and
  sum over the actual false/true assignments of the shared top wire.
- Normalization/probability claims require a proved unitary norm-preservation
  theorem and normalized input; arbitrary-vector weight identities must not be
  mislabeled as normalized distributions.
- Exact gate count counts mapped abstract gates only.  Semantic reindexings are
  not physical swaps and contribute zero gates under this model.
- Width is the cardinality of `AddedWire W`, not an informal `n+1` rewrite.
  Arity overhead is exact per gate; maximum-arity statements must handle the
  empty circuit explicitly.
- Quaternionic proofs may not use `Matrix.mul_kronecker_mul`, coefficient
  commutativity, left quaternionic phase, determinant one, or equality of
  differently typed source/target states.
- Composed quaternion-to-real results must visibly apply the two independent
  embeddings/translations rather than introduce a direct definition tailored
  to Corollary 1.
- Exact abstract matrix translation is separate from finite-precision gate
  encoding, synthesis, runtime, depth, and uniformity; those remain Stage 8.

## Completion Requirements

- Whole ordered-circuit operator preservation compiles for both translations
  over arbitrary finite wire types/supports and arbitrary circuit lengths.
- Embedded evolution and both canonical state-column identities compile after
  whole-circuit evaluation.
- Pointwise bottom outcome weights are equal after arbitrary evolution; named
  normalized corollaries justify the word “probability.”
- Local-unitarity preservation yields unitary translated circuits, and
  normalized input evolves to normalized source and target outputs.
- Gate count is exactly unchanged, global width is exactly one larger, every
  translated gate's local arity is exactly one larger, and the corrected
  bound/maximum theorem handles empty circuits.
- Corrected source-numbered Theorems 2/4 and Lemmas 3/8 have public Lean
  counterparts; the composed Corollary 1 is proved or its exact remaining
  obstruction is documented.
- End-to-end complex and quaternion examples exercise public translation,
  evaluation, state evolution, and weight APIs.
- Focused leaves, adjacent consumers, root, full build, warning-as-error,
  downstream import smoke, axiom audit, forbidden/boundary scans, and
  `git diff --check` pass and are recorded below.

## Stage Results

- In progress.  Stage opened after verified completion of 5-CIRCUITS on
  2026-07-09.
