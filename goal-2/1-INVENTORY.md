# 1-INVENTORY

## Current Facts

- The stage began from clean commit
  `aade00ea3c46a6bc00735d11b88767a089c63022` on branch `master`.
- The project is pinned to Lean 4.31.0 and mathlib v4.31.0 at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- The Goal 1 baseline contains 43 modules below `QuaternionicComputing/` plus
  the public root, for 44 Lean sources. The root has 22 direct public imports.
- `QuaternionicComputing/AxiomAudit.lean` contains 186 executable
  `#print axioms` endpoints. The current clean root and audit builds pass using
  only the standard foundations recorded in `docs/AxiomAudit.md`.
- The implementation/documentation audit found 42 existing comparison
  families. Independent inspection of the paper found nine additional
  source-level comparison families that the existing public API does not
  establish. The discovered family count is therefore 51, not a count assumed
  by the scaffold.
- The nine source-level additions are real sign-ray equality, certified basis
  behavior, norm-preserver converses, mixed-top observation, quaternionic
  reduced-matrix versus diagonal separation, computational-model equivalence,
  physical swap routing, top-wire phase tracking, and operational converse
  simulation.
- Goal 1 has no generic exact-circuit relation, generic basis-measurement
  relation, input/output basis-phase relation, certified basis-behavior
  relation, density/effect/channel layer, or operator-distance relation.

## Updated Assumptions

- A frozen family row may own several closely related declarations, but the
  machine manifest must list every included declaration explicitly and assign
  it to exactly one row. Routine constructor unfoldings, nonnegativity lemmas,
  and local-support bookkeeping may be excluded only by the written cohort
  policy.
- Source-only comparison rows may have an empty declaration array. Their empty
  arrays are evidence of a boundary, not permission to label the claim proved.
- Finite real and complex densities can use positive-semidefinite trace-one
  matrices. Effects can use the genuine Loewner interval `0 ≤ E ∧ E ≤ 1`.
- `Matrix.ext_iff_trace_mul_left/right` supplies only algebraic trace-test
  separation. Physical-effect separation requires a separate rank-one-effect
  argument; a focused probe established a viable route.
- Complex positive-semidefinite matrices require `ComplexOrder`, Loewner
  matrix order requires `MatrixOrder`, and the Euclidean operator norm requires
  `Matrix.Norms.L2Operator`.
- An empty finite index type has no trace-one density. Later channel
  characterization theorems must expose nonemptiness where they use a physical
  input.
- The L2 induced operator norm from `Matrix.toEuclideanCLM` is the intended
  Stage 10 norm. No existing exact simulation theorem supplies finite-
  precision compilation or an approximation relation.

## Big Picture Objective

Freeze the exact pre-retrofit semantic comparison surface, record every
ambiguous use of equality/simulation terminology, and establish viable pinned
mathlib representations before introducing public Goal 2 relation names.

## Detailed Implementation Plan

- Inventory the public Lean surface through the root imports, all relevant
  source declarations, the 186 audit endpoints, traceability, corrections,
  release documentation, and completed Goal 1 reports.
- Cross-check that inventory directly against the paper, including claims that
  Goal 1 deliberately left partial, excluded, or unresolved.
- Freeze the 51 family rows in `docs/EquivalenceClassification.md` with every
  required semantic axis and provisional owner.
- Freeze a machine-readable `docs/Goal1ComparisonCohort.json` with explicit
  declaration arrays and seed a structurally independent empty
  `docs/Goal2SemanticAPIManifest.json`.
- Validate JSON syntax, unique family IDs, unique declaration ownership,
  family/document agreement, declaration availability through the public root,
  and a stable checksum.
- Compile focused temporary probes for density/effect/order/trace APIs,
  physical-effect separation, and the L2 induced operator norm. Fold the
  selected APIs and exact cautions into `docs/MathlibAPI.md`.

## Build Structure

- `docs/EquivalenceClassification.md`: human-readable family inventory and
  terminology backlog. It is documentary evidence, never a relation proof.
- `docs/Goal1ComparisonCohort.json`: immutable machine-readable pre-retrofit
  cohort. New Goal 2 declarations never enter this file.
- `docs/Goal2SemanticAPIManifest.json`: separate growing manifest for public
  semantic declarations introduced after the freeze; it begins empty.
- `docs/MathlibAPI.md`: records only representations and theorem routes that
  compiled against the pinned dependency.
- `goal-2/1-INVENTORY.md`: stage evidence and exact commands.
- No Lean library module or public-root import is changed in Stage 1. Temporary
  API/name probes remain outside the repository.
- Baseline commands are `lake build`,
  `lake build QuaternionicComputing.AxiomAudit`, and
  `lake env lean -DwarningAsError=true QuaternionicComputing.lean`.

## Boundary Checks

- Same-space equality, cross-scalar/dimension simulation, algebraic image
  equivalence, schedule/list structure, resource equality, and diagnostic
  counterexamples have separate dispositions.
- Quaternionic state phase is right-sided. Nothing in the inventory is allowed
  to turn it into arbitrary unit-quaternion operator phase.
- One-input order witnesses are not promoted to all-basis or all-pure-input
  circuit relations.
- Pure-top decoded probabilities are not mixed-top, channel, or all-effect
  results.
- Equation 63 is equality after a named simultaneous reindexing, not a second
  identical circuit translator.
- Algebraic non-surjectivity is not operational converse-simulation failure.
- Exact abstract gate counts are not primitive compilation, runtime, or
  complexity-class equivalence.

## No-Cheating Checks

- Inventory labels and JSON metadata do not count as proofs. Every behavioral
  row remains provisional until a later proof-bearing wrapper compiles.
- Source-only rows remain visibly unimplemented and are assigned to the exact
  Goal 2 or Goal 3 owner that can supply the missing model.
- Arbitrary trace-test matrices are kept distinct from physical effects.
- The operator-norm probe explicitly opens the L2 operator scope; no default
  entrywise matrix norm is accepted.
- No stage result is inferred merely from the successful Goal 1 build/audit.
- No `sorry`, `admit`, axiom, impossible premise, or tautological relation is
  introduced.

## Completion Requirements

- The frozen cohort has 51 unique family IDs, an explicit declaration-level
  scope policy, unique declaration ownership, and a recorded checksum.
- The separate Goal 2 API manifest parses and is empty before Stage 2 creates
  any public semantic declaration.
- Every existing implementation family and every source-level behavioral
  comparison is represented once with a provisional owner/disposition.
- The terminology backlog records missing phase, input, observation,
  exactness, ancilla, decoder, or operational axes with exact references.
- Focused mathlib probes compile for real/complex PSD/order/effects, trace
  separation support, physical rank-one effects, matrix-to-CLM conversion, and
  the L2 induced operator norm.
- Clean Goal 1 root/audit builds, warning-as-error root compilation, JSON and
  coverage validators, source/whitespace scans, and `git diff --check` pass.

## Stage Results

- The root build completed successfully with 2,553 jobs, and the explicit
  audit replay completed successfully with the same 2,553-job closure.
- Warning-as-error compilation of `QuaternionicComputing.lean` passed.
- Five temporary representation probes compile:
  `/tmp/OrderOnlyProbe.lean`, `/tmp/L2OnlyProbe.lean`,
  `/tmp/SemanticsAPIProbe.lean`, `/tmp/PositiveBridgeProbe.lean`, and
  `/tmp/EffectSeparationRouteProbe.lean`.
- The 51-row human-readable classification and 25-item ambiguity backlog are
  present in `docs/EquivalenceClassification.md`.
- The selected density/effect/trace/operator-norm APIs and their exact scope
  cautions are folded into `docs/MathlibAPI.md`.
- The machine-manifest freeze, checksum, declaration-name probe, and final
  validation remain the active work before this stage may be marked complete.
