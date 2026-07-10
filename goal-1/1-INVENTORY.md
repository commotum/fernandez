# 1-INVENTORY

## Current Facts

- The authoritative local source is `Fernandez/fernandez-2003.md`, titled
  *Quaternionic Computing* by José M. Fernandez and William A. Schneeberger and
  labeled `quant-ph/0307017v2`.
- It contains 1,296 lines, seven resolving figure references, Definitions 1–5,
  Theorems 1–5, Lemmas 1–10, Corollary 1, and unnumbered resource/interpretive
  claims.
- No PDF or TeX source is locally available.  A nearby duplicate Markdown copy
  is byte-identical and supplies no independent evidence.
- The displayed 2008 date conflicts with the stated 2004 arXiv version date.
- The repository has no Lean files, Lake configuration, or toolchain pin yet.
- Lean 4.31.0 and an exact clean mathlib v4.31.0 source/build cache are locally
  available; the repo must still be configured reproducibly.
- Initial inspection reveals likely dimension typos in Theorems 3 and 5 and
  several convention/proof obligations, but none will be declared corrected
  until its mathematics and downstream effect are checked.

## Updated Assumptions

- Mathlib's existing quaternion and finite-matrix APIs probably suffice; this
  requires compiling probes, not source-name guesses.
- The central theorem should first target ordered lists of placed gates.  A DAG
  and topological-sort layer can be added after the semantic core is stable.
- Computational-basis probabilities may capture the exact simulation claim
  more directly than a full density-matrix framework; both formulations must be
  compared before committing.
- Determinant-one preservation in the quaternionic embedding may be materially
  harder than unitarity and must not be smuggled into a definition.

## Big Picture Objective

Create an evidence-backed claim/dependency map, fix the formal conventions and
architecture, adjudicate initial red flags, and establish a pinned Lean/mathlib
baseline that can compile the first real proofs.

## Detailed Implementation Plan

- Read all sections, footnotes, displayed claims, and figure captions; inspect
  figures 6 and 7 at minimum because ordering/resource claims depend on them.
- Create `docs/Traceability.md` with stable source IDs, exact locators, concise
  intended statements, dependencies, priority, Lean target, and status.
- Create `docs/Corrections.md`, `docs/Conventions.md`, and
  `docs/Architecture.md`; seed them with evidence, not conclusions by fiat.
- Check source dimensions, quaternion multiplication/conjugation conventions,
  module side, phase relation, tensor interchange conditions, determinant
  claims, and resource-model assumptions using hand calculations and small
  executable witnesses where useful.
- Inspect mathlib sources and compile focused API probes for `Quaternion ℝ`,
  `Matrix`, conjugate transpose/star, block/sum indices, unitarity, determinant,
  finite permutations, and inner products.
- Add `lean-toolchain`, Lake configuration, a public `QuaternionicComputing`
  root, one smoke module, and a minimal audit module; obtain the exact pinned
  dependency without modifying the external reference checkout.
- Update `.gitignore` and README only for Lean artifacts and project usage,
  preserving the placeholder Python files unless removal becomes necessary.

## No-Cheating Checks

- The inventory must include every numbered result and important negative or
  resource claim, not merely the results likely to be easy in Lean.
- “Corrected” statuses require a calculation, counterexample, type/dimension
  proof, or a completed Lean result; suspicion alone remains an open issue.
- API probes may use temporary/example declarations but no `sorry`, `admit`, or
  new axioms.
- The semantic architecture must not define simulation as membership in the
  image of the embedding or otherwise assume the desired preservation theorem.
- Check that no impossible dimension/normalization hypotheses make a smoke
  theorem vacuous.

## Completion Requirements

- Traceability includes Definitions 1–5, Theorems 1–5, Lemmas 1–10, Corollary
  1, the quaternionic ordering ambiguity, and all material resource claims,
  each with dependencies and an initial disposition.
- Conventions fix vector orientation, index/basis order, scalar side, adjoint,
  multiplication/evaluation order, local-gate placement, phase relation, and
  observable simulation.
- Every red flag listed in `0-plan.md` has an evidence-backed log entry or a
  precise experiment scheduled in the next relevant stage.
- A normal pinned mathlib dependency and project manifest exist; `lake build`
  succeeds without relying on edits to the external cached project.
- Focused API probes select a viable representation for Stages 2–5.
- `rg`-based forbidden-token/project-axiom scans, a smoke `#print axioms`, and
  `git diff --check` pass, with exact commands and outputs summarized below.

## Stage Results

- In progress.  Scaffold created on 2026-07-09.
- Next action: finish source inventory and pin/bootstrap the Lean project.

