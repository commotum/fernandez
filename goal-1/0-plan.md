# Goal 1 — Verified Lean Formalization of *Quaternionic Computing*

## Big-Picture Objective

Reconstruct the important mathematics of José M. Fernandez and William A.
Schneeberger's *Quaternionic Computing* (`quant-ph/0307017v2`) as a clean,
reusable Lean 4 library.  Independently verify the paper's claims, prove the
sound corrected versions, expose stable public APIs, and preserve a precise
record of omissions, obstructions, and material differences from the source.

Completion means the original objective is genuinely resolved: the central
real-to-complex and quaternion-to-complex simulation results are formalized at
the strongest justified level, all important paper claims have an explicit
disposition, and the pinned project builds and passes its axiom audit without
`sorry`, `admit`, or unexplained project-specific axioms.

## Non-Negotiable Constraints and No-Cheating Rules

- Verify the mathematics rather than transcribing prose or trusting displayed
  derivations.
- Never use `sorry`, `admit`, `sorryAx`, an unjustified `axiom`, or an
  impossible hypothesis to manufacture a completed result.
- Never silently alter a statement.  Record every changed assumption,
  conclusion, dimension, convention, or notion of equivalence in the
  traceability table and correction log.
- Distinguish literal state equality, equality up to an explicitly sided
  scalar phase, and equality of observable outcome distributions.
- Make dimensions, scalar sides, multiplication order, adjoints, wire
  permutations, normalization, and noncommutative assumptions explicit.
- Do not encode the desired simulation theorem into circuit semantics or
  observational equivalence.
- Prefer mathlib definitions when their assumptions match; wrap or replace
  them only for a documented mathematical or API reason.
- Keep general algebraic infrastructure separate from paper-specific circuit
  packaging wherever practical.
- Keep the project compiling after each coherent increment.  A green build is
  necessary evidence, never sufficient evidence that the model is faithful.
- Convert blockers into explicit experiments, smaller proof obligations,
  alternative representations, counterexamples, or documented unresolved
  claims; do not erase them by narrowing the goal.
- Preserve unrelated user changes in the worktree.
- Treat repository-root `BUILD-PLAN.md` as an authoritative requirement for
  every Lean-changing stage.  Its incremental module, import, focused-build,
  adjacent-consumer, boundary-check, reporting, and fold-back rules are part of
  this goal even when not repeated in a stage paragraph.

## Current Facts

- The source is `Fernandez/fernandez-2003.md` (1,296 lines), with all seven
  referenced figures present under `Fernandez/images/`.
- The source contains Definitions 1–5, Theorems 1–5, Lemmas 1–10, Corollary 1,
  and additional unnumbered circuit, interpretation, and resource claims.
- The metadata is internally ambiguous: it displays February 1, 2008 while
  identifying arXiv version 2 as November 5, 2004.  This must be documented,
  not silently resolved.
- The repository initially has no Lean project.  It contains an empty README
  and an unrelated placeholder Python/uv scaffold.
- Lean 4.31.0 is installed.  A clean, matching mathlib v4.31.0 checkout and
  compiled cache exist locally, so the project can be pinned reproducibly.
- Initial source red flags requiring adjudication include the target dimensions
  in Theorems 3 and 5, the determinant-one part of Theorem 5, the meaning of
  “linear” for realification maps, sided quaternionic phase conventions,
  noncommutative tensor identities, and the unstated cost model behind depth
  and simulation-overhead claims.
- The only initial untracked repository item is `.DS_Store`; it is user state
  and is not part of this goal.
- Stage 1 completed on 2026-07-09.  The full inventory is in
  `docs/Traceability.md`; `docs/Corrections.md` currently records 24 confirmed
  issues or proof obligations.
- The project now pins Lean 4.31.0 and mathlib v4.31.0 at resolved commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the baseline `lake build`
  succeeds.
- Compiling API probes confirmed that quaternionic column evolution is a right
  module action exposed by `Matrix.mulVecBilin ℍ ℍᵐᵒᵖ`, that
  `Matrix.fromBlocks` supports the required noncommutative algebra, and that
  quaternionic unitaries must use generic `unitary (Matrix … ℍ)` rather than
  the commutative-only `Matrix.unitaryGroup`.
- `BUILD-PLAN.md` is now part of the active goal requirements.  Every current
  and future Lean stage must include `Build Structure` and `Boundary Checks`
  sections and record the smallest builds that actually cover its changes.
- Stage 2 completed on 2026-07-09.  Public scalar modules now prove the
  complex/`j`-component decomposition, multiplication, conjugation, and
  norm-square laws; a norm-preserving two-coordinate counterexample proves
  that the paper's left-phase ray relation is not evolution-stable.
- Stage 3 completed on 2026-07-09.  Public matrix leaves now provide
  dimension-safe injective realification and complexification maps with
  rectangular multiplication and adjoint laws, star-monoid/group embeddings,
  complex-unitary-to-special-orthogonal preservation, and
  quaternionic-unitary-to-complex-unitary/symplectic preservation.
- The paper's missing realification determinant argument is repaired by
  `realify_det`.  For quaternionic complexification, the determinant is proved
  real and equal to `1` or `-1`; selecting `1` remains an exact isolated
  obstruction because the pinned mathlib lacks Pfaffian, connectedness, or
  Study-determinant infrastructure.  No simulation theorem depends on it.
- Stage 4 completed on 2026-07-09.  The library now has explicit-weight
  normalized real, complex, and quaternionic finite states; corrected generic
  quaternionic right phase; both realification and complexification state
  columns; four typed evolution identities; and pointwise bottom-basis weight
  preservation for canonical and arbitrary normalized pure top states.
- The real state leaf also proves the canonical reduced rank-one matrices are
  equal.  A generic mixed-density/partial-trace API remains optional and is not
  needed by the central ordered pure-state simulations.
- Stage 5 completed on 2026-07-09.  The library now has locality-certified
  placed gates on arbitrary finite supports, noncommutative-safe contextual
  placement, chronological reverse-product evaluation, circuit unitarity, and
  one-added-wire placed-gate translations for both embeddings.
- `wireRealify_place` and `wireComplexify_place` discharge the paper's missing
  local padding/naturality obligations against the actual placement
  definition.  Both translated gates preserve the old bottom support and
  complement, increase local arity by exactly one, and preserve local
  unitarity.
- The public order audit was independently strengthened from a symmetric
  noncommutation inequality to fixed values: the unique entry after
  chronological quaternion gates `[i,j]` is `-k`, while `[j,i]` gives `k`.
  Thus it detects a global evaluator-order reversal rather than merely
  distinguishing the two lists.

## Current Assumptions to Test

- **Confirmed:** `Quaternion ℝ`, finite matrices, star/adjoint APIs, opposite-
  ring right modules, and generic unitary APIs in mathlib 4.31.0 support the
  algebraic core without a bespoke quaternion implementation.
- A compact semantics built from finite index types, matrices, explicit gate
  support, and ordered composition will be sufficient for the central exact
  simulation theorems.
- The main observable claim can be stated directly as equality of computational
  basis outcome probabilities; density matrices and partial trace should be
  introduced only if they add a separately useful theorem.
- Exact gate-count and arity bounds are likely formalizable.  Depth and
  asymptotic encoding claims may require extra models or corrected scope.
- **Confirmed:** the sum-indexed matrix embeddings transport to the explicit
  distinguished wire `AddedWire W := Unit ⊕ W`; the wire wrappers are
  multiplicative/star-preserving and natural with actual local placement.

## Success Metrics and Verification Requirements

- A committed `lean-toolchain`, `lakefile.toml` or `lakefile.lean`, and manifest
  pin a mutually compatible Lean 4.31.0/mathlib v4.31.0 project.
- `lake build` succeeds from the project root.
- Focused examples cover scalar multiplication order, a non-real complex gate,
  a genuinely quaternionic entry, a noncommuting gate-order witness, and
  measurement preservation.
- Source scans find no `sorry`, `admit`, `sorryAx`, placeholder declarations,
  or unexplained project-local `axiom` in completed Lean modules.
- A dedicated audit module runs `#print axioms` on every main exported theorem;
  the release report distinguishes expected Lean/mathlib foundations from
  project-defined assumptions.
- `docs/Traceability.md` assigns each important paper item exactly one terminal
  status: **proved as stated**, **corrected and proved**, **partially
  formalized**, **intentionally excluded**, or **unresolved**.
- `docs/Corrections.md` records each issue's source locator, diagnosis, repair
  or obstruction, Lean declaration, justification, and dependent effects.
- A clean downstream import smoke test demonstrates that users need only the
  public root module and documented conventions.
- Final verification includes focused builds, full build, audit output,
  forbidden-token scan, import smoke test, and `git diff --check`.
- Every stage that changes Lean code satisfies `BUILD-PLAN.md`: declarations
  are classified by dependency/API role, narrow leaf ownership and import
  hygiene are justified, focused module builds and necessary adjacent-consumer
  builds pass, boundary shortcuts are checked, and exact results are folded
  back into the stage file and this plan.

## Lean Build-Plan Requirements

The following requirements are incorporated from `BUILD-PLAN.md` and are part
of **every** stage's completion requirements by reference:

- At initial sync, read `BUILD-PLAN.md`, this plan, the execution loop, the
  previous completed stage, and the first incomplete stage before editing Lean.
- Classify each declaration/module as public API, proof-side, diagnostic,
  fallback, temporary scaffolding, or executable/runtime where applicable.
- Put cheap definitions in low-dependency modules and expensive proofs,
  counterexamples, diagnostics, and audits in narrow leaves.  Keep public API
  and umbrella modules thin and avoid unnecessary high-fanout edits/imports.
- Each active stage file must contain `Build Structure` and `Boundary Checks`
  sections identifying touched modules, ownership, avoided high-fanout files,
  focused build commands, adjacent consumers, and forbidden shortcuts.
- Build the touched leaf after skeleton/import changes and after implementation;
  build adjacent consumers that exercise its public surface.  Run a full build
  when a public root, high-fanout import, build configuration, notation, global
  instance/simp surface, or explicit stage requirement changes.
- A diagnostic or unused abstraction is never completion evidence for a target
  theorem.  Failed structural obligations become checked lemmas, named
  obstructions, or documented target revisions—not silent scope changes.
- Record exact build, scan, audit, and `git diff --check` results in the stage
  file, then fold theorem names, module paths, failed obligations, and next
  actions back into this plan before marking the stage complete.

## Stages

### 1-INVENTORY

#### Big Picture Objective

Establish a reproducible baseline and turn the entire paper into an evidence-
backed claim/dependency inventory before choosing irreversible representations.

#### Detailed Implementation Plan

- Read the full Markdown source and inspect figures where they carry
  mathematical information.
- Assign stable IDs to numbered and important unnumbered claims; record source
  locations, intended statements, dependencies, priority, and initial status.
- Seed `docs/Traceability.md`, `docs/Corrections.md`,
  `docs/Conventions.md`, and `docs/Architecture.md`.
- Test every initial red flag with direct algebra, small counterexamples, or
  precise proof obligations; distinguish confirmed errors from suspicions.
- Inspect relevant mathlib quaternion, matrix, star, determinant, finite-index,
  and inner-product APIs with compiling probes.
- Bootstrap and pin the Lean/mathlib project, create a public root module and a
  minimal build/audit smoke test, and update repository documentation/ignores.

#### Completion Requirements

- Every important source claim has a stable row and dependency information;
  all numbered Definitions 1–5, Theorems 1–5, Lemmas 1–10, and Corollary 1 are
  present.
- Conventions explicitly fix index types, vector orientation, scalar-action
  side, multiplication order, adjoints, basis ordering, and simulation notion.
- Each initial red flag has evidence and a logged provisional disposition.
- The pinned project builds a minimal mathlib import with no placeholders.
- API probes establish a viable representation or record a concrete fallback.
- Stage results and verification commands are recorded in `1-INVENTORY.md` and
  folded back into this plan.

### 2-SCALARS

#### Big Picture Objective

Prove the scalar identities underlying complex realification and quaternionic
complexification, with conventions strong enough to prevent later order errors.

#### Detailed Implementation Plan

- Reuse mathlib's complex and quaternion types and conjugation/norm structures.
- Define the paper's complex and “weird” quaternion components with neutral,
  reusable names and prove reconstruction, extensionality, multiplication,
  conjugation, and norm-square identities corresponding to Equations 34–43.
- Package complex real/imaginary multiplication and conjugation identities used
  by the real simulation.
- Add explicit `i`, `j`, and mixed noncommutative sanity checks.

#### Completion Requirements

- All scalar prerequisites of both embeddings compile as theorem proofs.
- Multiplication-order and conjugation signs are checked by concrete examples.
- Public names, source mappings, and any convention corrections are documented.
- Focused build and forbidden-token scans pass.

### 3-MATRICES

#### Big Picture Objective

Construct reusable finite-matrix embeddings from complex matrices to real block
matrices and quaternionic matrices to complex block matrices.

#### Detailed Implementation Plan

- Define dimension-safe block/index representations independent of powers of
  two.
- Prove additivity where useful, identity, injectivity, multiplication,
  transpose/star-adjoint preservation, and norm/unitarity/orthogonality
  consequences.
- State image/subgroup results with correct dimensions; independently resolve
  determinant-one claims rather than inferring them from unitarity.
- Add low-dimensional evaluation tests and document any result generalized
  beyond square circuit matrices.

#### Completion Requirements

- Correct versions of paper Lemmas 1, 2, 6, and 7 are proved.
- Correct image/group consequences of Theorems 3 and 5 needed downstream are
  proved, with determinant claims either proved or precisely isolated.
- Dimension and zero-size edge cases are tested or explicitly constrained.
- Traceability, corrections, focused build, and axiom spot-audit are current.

### 4-STATES

#### Big Picture Objective

Formalize state embeddings and computational-basis measurements without
conflating vector equality, rays, reduced states, and observed probabilities.

#### Detailed Implementation Plan

- Define normalized finite states only where normalization is semantically
  required; keep algebraic vector lemmas more general.
- Define both column/state embeddings for complex-to-real and
  quaternion-to-complex simulations.
- Prove reconstruction/injectivity, appropriate real or complex linearity,
  norm preservation, orthogonality where true, and evolution compatibility.
- Define computational-basis weights/distributions and prove bottom-wire
  probability preservation; add density/partial-trace results only if useful.
- Formalize phase relations with an explicit scalar side and test whether the
  paper's quaternionic ray statement is compatible with chosen linear maps.

#### Completion Requirements

- Correct versions of Lemmas 4, 5, 9, and 10 are proved at the strongest useful
  algebraic/measurement level available before circuits.
- All claimed probability equalities have normalization and nonnegativity
  support rather than being true by definition.
- Linearity and phase claims have correct scalar domains/sides.
- Representative states pass exact evaluation checks and the stage build/audit.

### 5-CIRCUITS

#### Big Picture Objective

Build the minimum reusable ordered-circuit semantics needed to lift local gates
to arbitrary wires and compose their matrix meanings.

#### Detailed Implementation Plan

- Represent finite wires, gate arity/support, well-formed placement, and ordered
  gate lists with explicit source and target scalar types.
- Define contextual lifting via finite equivalences/permutation matrices or an
  equally auditable construction; do not rely on invalid noncommutative tensor
  interchange.
- Prove identity, composition order, locality, unitarity preservation, and
  compatibility of each matrix embedding with gate padding/placement.
- Include a small order-sensitive test capable of detecting reversed products.

#### Completion Requirements

- Circuit evaluation is independent of the theorems it will be used to prove.
- Arbitrary noncontiguous support and all dimension constraints are checked.
- Local-to-global embedding lemmas compile for real and quaternionic paths.
- No hidden swap-gate overhead is counted; semantic swaps and circuit gates are
  explicitly distinguished and documented.

### 6-SIMULATION

#### Big Picture Objective

Prove the paper's two central exact simulations compositionally, including
state evolution, measurements, and exact structural overhead.

#### Detailed Implementation Plan

- Translate every ordered source gate through the appropriate matrix embedding
  while threading one shared top wire.
- Prove by ordered-list induction that translated circuit evaluation is the
  embedded source evaluation (paper Lemmas 3 and 8).
- Combine state and measurement lemmas into corrected forms of Theorems 2 and
  4, making the chosen notion of “exactly simulates” explicit.
- Prove exact gate-count, width, and maximum-arity statements supported by the
  representation and include nontrivial end-to-end examples.

#### Completion Requirements

- Corrected central theorems have no placeholders and cover arbitrary legal
  gate order/support in the stated finite model.
- Operator preservation and observable preservation are separate exported
  theorems.
- Gate count, width, and arity conclusions are machine-checked, not prose.
- Interim full build, forbidden-token scan, and axiom audit pass; traceability
  records every difference from Theorems 2 and 4.

### 7-ORDERING

#### Big Picture Objective

Formalize the quaternionic ordering ambiguity and the broader circuit-order
claims without importing commutative tensor laws into a noncommutative setting.

#### Detailed Implementation Plan

- Relate circuit dependency DAGs/topological orders to ordered evaluation where
  this adds mathematical content beyond the ordered-list core.
- Produce and prove a minimal quaternionic counterexample in which independent
  gate orders yield distinct operators or observable outcomes.
- Prove order independence under useful central/real/0–1 hypotheses and state
  precisely which form of tensor interchange is valid.
- Connect each fixed legal ordering to the Stage 6 simulation theorem.

#### Completion Requirements

- Definitions 4 and 5 and the paper's ambiguity claim have explicit formal
  counterparts or a documented boundary of formalization.
- At least one order-sensitive witness is evaluated and proved nontrivial.
- Sufficient order-independence conditions are proved with exact hypotheses.
- Ordering terminology and affected corrections are propagated to dependents.

### 8-RESOURCES

#### Big Picture Objective

Adjudicate the paper's size, width, arity, depth, preprocessing, universality,
and computational-power claims in explicit cost models.

#### Detailed Implementation Plan

- Define the cost measures and encodings before stating asymptotic results.
- Reuse structural results from Stage 6 for exact size/width/arity bounds.
- Analyze serialization depth loss, the claimed `O(log s)` depth alternative,
  circuit-description conversion time, and universal-gate consequences.
- Separate finite exact simulation from Turing-machine/oracle and complexity-
  class claims that require external frameworks.

#### Completion Requirements

- Every important resource claim is either proved in a stated model or assigned
  a terminal non-proved status with an exact obstruction.
- Exact algebraic simulation is never presented as circuit synthesizability or
  an asymptotic complexity theorem without the required encoding assumptions.
- Corollary 1 and all dependent prose claims have traceability dispositions.

### 9-COVERAGE

#### Big Picture Objective

Close the claim inventory and formalize useful remaining mathematics without
letting peripheral material destabilize the central library.

#### Detailed Implementation Plan

- Revisit every nonterminal traceability row and correction dependency.
- Add nearby correct theorems or counterexamples where source claims cannot be
  established.
- Classify historical, physical-interpretive, bibliographic, and open-question
  material deliberately rather than treating it as missing proof work.
- Run an independent statement/assumption review of all exported results.

#### Completion Requirements

- Every important inventory row has exactly one allowed terminal status.
- Every correction records transitive effects on dependent claims.
- No important central claim is merely excluded because it was difficult.
- The full library and audit build remain green after coverage closure.

### 10-RELEASE

#### Big Picture Objective

Deliver a stable, documented Lean library that another project can import
without learning the paper's original organization.

#### Detailed Implementation Plan

- Stabilize namespaces, module boundaries, public root imports, docstrings,
  examples, and naming.
- Finish README usage guidance, architecture/conventions documents,
  traceability map, correction log, and generated or recorded audit report.
- Test a minimal downstream consumer and run all release verification.
- Prepare the final report covering formalized content, exports, structure,
  corrections, unresolved/omitted material, build/audit results, and reuse.

#### Completion Requirements

- Pinned clean full build and downstream import smoke test succeed.
- Forbidden-token/project-axiom scans and `#print axioms` audit are explained
  and clean under the stated policy.
- `git diff --check` succeeds and no generated build artifact is tracked.
- Documentation is complete, mutually consistent, and maps every important
  source item to its terminal status.
- The final report contains every deliverable requested in the objective.

## Stage Status

- [x] 1-INVENTORY — completed 2026-07-09
- [x] 2-SCALARS — completed 2026-07-09
- [x] 3-MATRICES — completed 2026-07-09
- [x] 4-STATES — completed 2026-07-09
- [x] 5-CIRCUITS — completed 2026-07-09
- [ ] 6-SIMULATION — in progress
- [ ] 7-ORDERING
- [ ] 8-RESOURCES
- [ ] 9-COVERAGE
- [ ] 10-RELEASE
