# Goal 3 Execution Loop

Use this protocol to execute `goal-3/0-plan.md` one evidence-backed stage at a
time. Repository-root `BUILD-PLAN.md` remains authoritative for Lean module
layout, import hygiene, focused builds, adjacent consumers, and fold-back.

## Repeatable Loop

1. **Sync current state with reality.**
   - Read `goal-3/0-plan.md`, this loop, `BUILD-PLAN.md`, and the previous stage
     report if one exists.
   - Inspect actual Lean sources, public imports, audits, validators, docs,
     traceability, corrections, worklist/frontier data, Git status, and relevant
     tests.
   - Re-run the smallest checks needed to distinguish current evidence from
     historical prose.
2. **Update `0-plan.md` before implementation.**
   - Correct stale counts, assumptions, dependencies, stage ownership, or
     theorem targets.
   - Record why any change is necessary. Never preserve a forecast after the
     executable baseline contradicts it.
3. **Select the first dependency-ready incomplete stage.**
   - Normally choose the first unchecked stage.
   - A later independent stage may begin only when all of its declared inputs
     are stable and it will not conflict with unfinished shared-module work.
4. **Create or refresh `goal-3/[INDEX]-[SHORTHAND].md`.**
   - Use the template below.
   - State exact source IDs, `EQC` families, target declarations, files,
     consumers, build commands, forbidden shortcuts, and completion evidence.
5. **Implement only that stage.**
   - Prefer narrow low-dependency definitions and proof leaves.
   - Build after the skeleton and every import-boundary change.
   - Do not perform unrelated cleanup or preempt a later stage.
6. **Add verification and no-cheating checks.**
   - Give each new public definition a real theorem consumer.
   - Add diagnostics or counterexamples for failed implications and boundary
     claims.
   - Extend the executable axiom audit for main exported results.
   - Add worklist/registry checks whenever ownership or status changes.
7. **Run proportionate verification.**
   - Build touched leaves and adjacent consumers.
   - Run executable examples for algorithms.
   - Run strict warning-as-error compilation for stable and audit surfaces.
   - Run the default/full build whenever a public root, shared instance,
     notation, build configuration, or high-fanout module changes.
   - Run proof-hole, shortcut, import, artifact, Markdown, whitespace, and
     `git diff --check` scans.
8. **Record exact results in the stage file.**
   - Include commands, job counts, theorem names, axiom output, validator
     results, counterexamples, failed approaches, and remaining obstructions.
   - Distinguish fresh results from inherited release evidence.
9. **Fold results back into `0-plan.md` and canonical docs.**
   - Update Current Facts, dependencies, stage status, worklist dispositions,
     traceability, corrections, architecture, conventions, and frontier links.
   - Mark a stage complete only when every listed requirement is covered.
10. **Continue toward the stated Goal 3 objective.**
    - If stopping for the session, leave the repository resumable: exact
      current evidence, first next action, failed experiments, unblock paths,
      and assumptions to challenge must be recorded.

## Invariants

- Do not narrow the Goal 3 core without saying so and recording explicit user
  authorization or a checked impossibility/underdetermination result.
- Do not widen the core by silently promising to solve an entire frontier
  research program.
- Do not mark a stage complete because a build is green unless that build and
  its consumers cover every mathematical and algorithmic requirement.
- Do not treat a structure definition as evidence that an instance, algorithm,
  compiler, or protocol exists.
- Do not treat metadata, a registry label, or documentation as a proof.
- Prefer small stages and narrow modules that reduce uncertainty before large
  infrastructure is promoted.
- Convert blockers into work: isolate the missing lemma, construct a finite
  counterexample, test an alternate representation, prove underdetermination,
  or create a precise frontier obligation.
- Preserve the distinction among runtime/API code, proof-side theorems,
  diagnostics, verifiers, fallbacks, and temporary scaffolding.
- Preserve Goal 2's semantic distinctions and quaternionic multiplication-side
  conventions everywhere.
- Keep exact values, encoded data, approximation, synthesis, uniformity,
  runtime, and complexity claims in separate layers.
- Preserve unrelated user changes and never delete or rewrite frozen Goal 1/2
  inputs merely to make a new checker pass.

## Evidence Rules

### Mathematical claims

A positive result requires a compiled theorem with the intended assumptions and
a real downstream consumer. A refutation requires a compiled counterexample to
the source-level statement. A formal-underdetermination outcome requires two
checked models, or an equivalent independence theorem, demonstrating that the
declared assumptions do not determine the claim.

### Algorithms

An executable scheduler, encoder, compiler, or generator requires:

- a computable definition;
- termination accepted by Lean without an unsafe escape;
- a semantic correctness theorem;
- malformed-input or failure behavior;
- evaluation on representative inputs; and
- size/runtime theorems stated in the selected cost model.

Existentially supplied data does not satisfy an algorithm requirement.

### Approximation

Every approximate result must name:

- the metric or observable distance;
- input normalization and legality assumptions;
- the local and accumulated error budgets;
- the exact zero-budget bridge when one is valid; and
- the distinction between mathematical values, encoded approximants, and
  executable construction.

### Resource and complexity claims

Every resource theorem must arise from emitted syntax or an executable
algorithm. Big-O, polynomial time, BQP, uniformity, and universal-set claims
must expose the size/precision parameter, encoding, machine/cost model, and
success/error convention.

### Frontier claims

Moving an item to `docs/ResearchFrontier.md` is not a proof. It is valid only
when the item lies outside the reset Goal 3 core or has a checked obstruction,
and the entry records its exact missing model, dependencies, and falsifiable
future targets.

## Verification Matrix

Choose the applicable checks for each stage and record exact commands in the
stage file.

### Always

- focused builds for every touched Lean leaf;
- adjacent consumer builds;
- proof-hole/project-axiom/unsafe/opaque scans;
- goal-specific forbidden-shortcut scans;
- documentation and worklist consistency checks;
- `git diff --check`.

### Public API changes

- public-root build;
- root-only downstream smoke file;
- direct `#print axioms` coverage for main exports;
- stable/audit import-boundary check;
- default build when the import closure changes.

### Executable algorithms

- evaluation on positive, boundary, and malformed inputs;
- correctness and termination consumers;
- code-size/resource/runtime checks;
- scan proving runtime does not call proof-side choice or a supplied reference
  certificate as an implementation.

### Heavy algebra or semantics

- low-dimensional sanity examples;
- empty/nonempty and dimension-boundary cases;
- scalar-side, multiplication-order, adjoint, and tensor-association checks;
- strict warning-as-error compilation and exact axiom parsing.

### Stage and release closure

- Goal 3 worklist validator;
- Goal 2 frozen checksum/manifest validator;
- traceability/correction/frontier arithmetic;
- maintained audit/example builds;
- source/module/public-import counts;
- tracked-artifact and Markdown structure scans;
- default or clean pinned build according to the stage requirements;
- independent review when the stage has a broad semantic or release impact.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current Lean code, tests, docs, worklist, and previous stages.
- Exact source IDs and `EQC` families owned by this stage.
- Current build, audit, and worktree evidence.

## Updated Assumptions

- Assumptions that remain justified.
- Assumptions that changed after inspection or failed proofs.
- Assumptions requiring a probe, counterexample, or primary-source check.

## Big Picture Objective

- Restate the stage objective using the current facts.
- Name the intended positive, corrected, negative, or underdetermination
  outcomes.

## Detailed Implementation Plan

- Concrete Lean, executable, documentation, and validator changes.
- Expected files and declarations.
- New examples, tests, or counterexamples.
- Primary proof route and fallback route for each hard obligation.

## Build Structure

- New or touched modules and why each owns its declarations.
- Runtime/API, proof-side, diagnostic, verifier, and temporary classifications.
- High-fanout modules intentionally avoided.
- Focused build commands and required adjacent consumers.

## Boundary Checks

- Scalar, dimension, multiplication-side, tensor, chronology, observation,
  approximation, encoding, resource, and uniformity boundaries that apply.
- Stable/audit/public import boundaries.
- Forbidden shortcuts and the exact scan or theorem check enforcing each one.

## No-Cheating Checks

- Checks proving the implementation does not route through supplied
  certificates, noncomputable runtime choice, fake unitarity, semantic
  reindexing counted as routing, metadata-only closure, or another forbidden
  fallback.

## Completion Requirements

- Requirement-by-requirement theorem, algorithm, counterexample, documentation,
  validator, build, audit, and scan evidence.
- Exact commands that must pass.
- Worklist, traceability, correction, architecture, and frontier updates.

## Stage Results

- Fill in only after implementation.
- Declarations and files added or changed.
- Builds, evaluations, validators, scans, and audit outputs.
- Failed approaches and what they established.
- Final disposition of each owned row/family.
- Fold-back changes and the first dependency-ready next stage.
```

## Session Stop Rule

Do not mark a genuinely blocked stage complete. If work stops before completion,
the stage file must contain:

- the smallest failing theorem, program, or model obligation;
- exact compiler/test output or mathematical counterexample evidence;
- at least one next construction or alternate formulation;
- dependencies or external primary results still needed;
- the safe current build state; and
- the precise command or file from which the next session should resume.
