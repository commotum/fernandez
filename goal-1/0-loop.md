# Goal 1 Execution Loop

Use this protocol for every stage in `goal-1/0-plan.md`, together with the
authoritative Lean workflow in repository-root `BUILD-PLAN.md`.

## Repeatable Loop

1. Read `BUILD-PLAN.md`, then sync current state with the actual repository
   files, paper source, build, tests, traceability table, correction log, and
   recent diffs.
2. Update `goal-1/0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage; do not skip a blocker merely because a
   later task looks easier.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the template below.
5. Implement only that stage, splitting uncertain work into small compiling
   probes and proof obligations.
6. Add `Build Structure` and `Boundary Checks` evidence that exercises the
   actual mathematical requirement and classifies new declarations.
7. Run the touched-leaf and necessary adjacent-consumer builds first; run the
   appropriate full verification under the conditions in `BUILD-PLAN.md`, plus
   forbidden-token/project-axiom scans, axiom spot-audits, and diff checks.
8. Record commands, results, failures, corrections, and learned facts in the
   stage file.
9. Fold the evidence back into `goal-1/0-plan.md`, the traceability table, the
   correction log, and dependent stages.
10. Continue toward the original objective.  If stopping for a session, leave
    a resumable state with current evidence, the next concrete experiments,
    unblock actions, and assumptions that still need to be challenged.

## Invariants

- Do not narrow the user's objective without saying so and recording the
  resulting coverage impact.
- Do not mark a stage complete without requirement-by-requirement evidence.
- Do not use a green build or test as evidence unless it covers the stated
  mathematical requirement.
- Prefer small, low-complexity stages and probes that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn
  them into explicit proof, counterexample, API, and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic,
  counterexample, and fallback paths.
- Log a correction in the same stage in which it is discovered; include source
  locator, diagnosis, repair/obstruction, Lean name, justification, and effects
  on dependent claims.
- Preserve literal equality, phase equivalence, operator equality, and outcome-
  distribution equality as distinct notions.
- Re-check scalar side, dimensions, multiplication order, adjoints, and basis
  ordering whenever crossing an abstraction boundary.
- Keep completed modules free of `sorry`, `admit`, `sorryAx`, unexplained
  project axioms, vacuous assumptions, and definitions tailored to make the
  desired theorem tautological.
- Preserve unrelated user changes and never treat generated build output as
  source.
- Prefer narrow leaf modules and imports, keep API/umbrella modules thin, and
  record why any high-fanout file must change.
- A proof or diagnostic that no public/goal consumer uses is not evidence that
  the stage's target has been achieved.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- High-fanout modules intentionally avoided or necessarily changed.
- Focused build command for every touched leaf.
- Adjacent consumer builds required to exercise the public surface.

## Boundary Checks

- Runtime/API/proof-side/diagnostic/fallback boundaries relevant to the stage.
- Explicit checks proving the implementation does not route through forbidden shortcuts.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test commands.
- Documentation updates required.
- `BUILD-PLAN.md` evidence and fold-back required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and outcomes.
- Include what was learned.
- Include what should change in `0-plan.md` before the next stage.
```
