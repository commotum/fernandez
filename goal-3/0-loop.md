# Goal 3 Execution Loop

Use this protocol for every stage in `goal-3/0-plan.md`, together with the
authoritative Lean workflow in repository-root `BUILD-PLAN.md`.

## Repeatable Loop

1. Verify Goal 2 is complete with its clean build/audit, semantic-classification
   manifest, traceability/correction fold-back, and downstream smoke evidence.
   If not, stop Goal 3.  Otherwise read `BUILD-PLAN.md` and sync current state
   with the actual repository, paper source, primary references, builds, tests,
   closure ledger, traceability, corrections, prior stage results, and diff.
2. Update `goal-3/0-plan.md` with current facts before starting the next stage.
   If evidence changes a route, dependency, or target, record why.
3. Select the first dependency-ready incomplete stage or mandatory compiling
   milestone.  Prefer source order among ready work.  If a hard branch has an
   exact recorded obstruction and its declared primary/fallback probes are
   exhausted, keep it incomplete but advance an independent branch; never
   launder the blocker or mark the umbrella stage complete.
4. Create or refresh `goal-3/[INDEX]-[SHORTHAND].md` from the template below.
5. Implement only that stage.  Split uncertain work into small compiling API
   probes, explicit theorem obligations, counterexamples, and fallback routes.
6. Add verification and no-cheating checks that exercise the actual source
   claim, its model, its public consumer, and any executable/cost assertion.
7. Run focused leaf and adjacent-consumer builds, executable fixtures, relevant
   full verification, axiom checks, closure-ledger checks, forbidden-shortcut
   scans, whitespace checks, and `git diff --check` as required by
   `BUILD-PLAN.md`.
8. Record exact commands, results, failures, corrections, literature sources,
   assumptions, and learned facts in the stage file.
9. Fold results back into `goal-3/0-plan.md`, `docs/RemainingWork.md`,
   `docs/Traceability.md`, `docs/Corrections.md`, architecture/conventions, and
   all dependent stages.
10. Continue toward the original objective.  If stopping for a session, leave
    a resumable state with current evidence, the next concrete proof or
    experiment, unblock actions, failed approaches, and assumptions still to
    challenge.

## Claim-Adjudication Loop

For every assigned traceability row inside a stage:

1. Quote or precisely paraphrase the source claim and locator.
2. State the formal model, types, scalar conventions, equality notion, cost
   model, and quantifiers before attempting the proof.
3. Identify the exact gap between the existing Lean result and closure.
4. Try the primary constructive proof through small checked lemmas.
5. When a proof fails structurally, test the statement with concrete finite
   examples and isolate a counterexample or missing hypothesis.
6. Select one permitted closure outcome from `0-plan.md`; do not silently
   weaken the claim.
7. Prove the corrected theorem, negative result, conditional reduction, or
   underdetermination theorem and exercise it through a real consumer.
8. Update the source mapping, correction dependencies, and residual frontier.

## Invariants

- Do not narrow the user's “tackle the immutable 47-row cohort” objective.
  Account for each row as `closedByGoal2` or assigned to Goal 3, and record any
  coverage consequence of a changed post-Goal-2 baseline.
- Do not mark a stage complete without requirement-by-requirement evidence.
- A green build is necessary evidence, never evidence that the mathematical or
  research requirement was met.
- Prefer small, low-dependency modules and experiments that narrow uncertainty.
- Treat the mandatory A/B/C milestones in `0-plan.md` as separate stages with
  separate reports and verification.  Split any newly discovered multi-layer
  stage before implementation.
- Convert blockers into work items: decompose them, try a second representation,
  prove a no-go, or expose an exact external theorem obligation.
- Preserve the distinction between public implementation, proof-side helper,
  verifier, executable algorithm, diagnostic, counterexample, fallback, and
  temporary scaffold.
- A conditional structure is not an implementation of its fields.  A density
  certificate is not a density constructor; a legal schedule is not a sorting
  algorithm; a compiler interface is not a compiler; a dense-generator
  certificate is not a universality proof.
- Exact, approximate, probabilistic, asymptotic, and complexity-class claims
  remain separate until explicit bridge theorems connect them.
- No runtime theorem may hide parsing, scalar bit length, arithmetic,
  precision, routing, schedule construction, output size, or primitive
  synthesis that its named cost model is meant to charge.
- Recheck right quaternionic phase, multiplication order, adjoints, tensor
  hypotheses, normalization, dimensions, basis permutations, and chronology at
  every boundary.
- Do not infer signaling, entanglement, cryptographic security, causality, or
  physical impossibility from operator/ray inequality alone.
- For an explicit paper question, definitions alone are not completion.  The
  stage needs a constructive theorem, formal counterexample, reduction, or
  underdetermination proof in the declared model.
- Completed modules remain free of `sorry`, `admit`, `sorryAx`, unexplained
  axioms, opaque/unsafe shortcuts, impossible assumptions, and definitions
  tailored to force target theorems.
- Preserve unrelated user work and keep generated artifacts untracked.
- Follow `BUILD-PLAN.md`: keep imports narrow, avoid high-fanout edits when a
  leaf works, record focused and adjacent builds, and fold every result back.

## Verification Layers

Use the smallest layer that covers the work, then broaden when the stage
changes shared APIs or claims completion:

1. **API probe:** compile a temporary or diagnostic file establishing that the
   intended mathlib/local representation is viable.
2. **Focused build:** build every touched leaf by its Lake target.
3. **Adjacent consumers:** build modules that use the new public theorem or
   executable definition.
4. **Executable checks:** run `#eval`/test fixtures for algorithms, malformed
   inputs, edge cases, and cost counters.
5. **Mathematical checks:** exact examples, counterexamples, edge dimensions,
   normalization, and theorem-signature inspection.
6. **Boundary scans:** proof holes/project axioms, forbidden commutative or
   noncomputable shortcuts, status laundering, and uncounted fallback paths.
7. **Broader build:** run the public root/full audit when imports, shared APIs,
   notation, instances, or stage completion require it.
8. **Repository checks:** closure checksum, docs consistency, whitespace,
   tracked artifacts, and `git diff --check`.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, builds, docs, paper sources, primary literature, and
  previous stage results.
- Exact assigned traceability IDs and their present statuses.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that require checked probes before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current evidence without narrowing
  the original closure requirement.

## Detailed Implementation Plan

- Concrete code, proof, counterexample, executable, documentation, and test
  changes for this stage.
- Files expected to change and primary/fallback mathematical routes.
- New tests, probes, examples, or source audits required.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- Classification of declarations as public API, proof-side, executable,
  diagnostic, fallback, or temporary scaffolding.
- High-fanout modules intentionally avoided or necessarily changed.
- Focused build command for every touched leaf.
- Adjacent consumer and broader builds required to exercise the result.

## Boundary Checks

- Claim-specific forbidden shortcuts and how they will be detected.
- Exact/approximate, semantic/executable, supplied/constructed, and
  mathematical/operational boundaries relevant to the stage.
- Checks proving no fallback path is being counted as the target result.

## Completion Requirements

- Requirement-by-requirement checks from `goal-3/0-plan.md`.
- Closure outcome and evidence for every assigned traceability ID.
- Required build, executable, scan, axiom-audit, and diff commands.
- Traceability, correction, architecture, and closure-ledger updates.
- `BUILD-PLAN.md` evidence and fold-back required.

## Stage Results

- Work completed and exact declaration/module names.
- Proofs, counterexamples, algorithms, and models delivered.
- Builds, tests, scans, audits, and checks run with outcomes.
- Failed approaches and what they establish.
- What was learned, remaining exact frontier, and changes required in
  `0-plan.md` before the next stage.
```

## Session Fold-Back

Before stopping:

1. Update the active stage report with exact evidence.
2. Update `goal-3/0-plan.md` facts and stage status only if all requirements are
   met.
3. Update the closure ledger and source traceability for every touched row.
4. Record new correction IDs, theorem names, module paths, source references,
   failed obligations, and dependent-stage changes.
5. Leave the next stage or blocked proof resumable from a concrete command and
   theorem obligation.

Never mark a stage complete because its framework exists.  Completion requires
the source-facing theorem, counterexample, algorithm, or research result named
by that stage.
