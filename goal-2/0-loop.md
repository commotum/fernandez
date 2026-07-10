# Goal 2 Execution Loop

Use this protocol for every stage in `goal-2/0-plan.md`, together with the
authoritative Lean workflow in repository-root `BUILD-PLAN.md`.

## Repeatable Loop

1. Read `BUILD-PLAN.md`, then sync current state with the actual public root,
   relevant Lean leaves, AxiomAudit, frozen Goal 1 comparison cohort, Goal 2
   semantic API manifest, paper traceability, corrections, documentation,
   completed Goal 1 evidence, reindexed Goal 3 scaffold, builds, tests, and
   current diff.
2. Update `goal-2/0-plan.md` with current facts before starting the next stage.
   If a compiled probe changes a relation, implication, dimension hypothesis,
   or Goal 3 boundary, record the change and its transitive effects.
3. Select the first dependency-ready incomplete stage or mandatory compiling
   milestone.  Prefer source order among ready work; keep a hard blocked branch
   incomplete while advancing an independent branch only after its exact
   obstruction and next proof target are recorded.
4. Create or refresh `goal-2/[INDEX]-[SHORTHAND].md` from the template below.
5. Implement only that stage or milestone, using small compiling relation
   definitions, theorem probes, counterexamples, and real consumers.
6. Add verification and no-cheating checks covering semantic axes, scalar
   side, input/observation scope, same-space versus cross-model typing,
   equivalence laws, failed converses, and registry proof links.
7. Run focused leaf and adjacent-consumer builds, relevant executable/examples,
   broader verification required by `BUILD-PLAN.md`, axiom checks, registry
   checks, forbidden-shortcut scans, whitespace checks, and `git diff --check`.
8. Record commands, outcomes, failed approaches, assumptions, theorem names,
   classification changes, correction effects, and learned facts in the stage
   file.
9. Fold results back into `goal-2/0-plan.md`, the frozen cohort registry, the
   Goal 2 semantic API manifest, `docs/EquivalenceClassification.md`,
   traceability, corrections, conventions, architecture, release docs,
   AxiomAudit, and the Goal 3 rebaseline forecast.
10. Continue toward the original objective.  If stopping for the session,
    leave a resumable state with current evidence, the next exact theorem or
    counterexample, unblock actions, and assumptions still to challenge.

## Relation-Adjudication Loop

For every comparison claim or proposed hierarchy arrow:

1. Identify the compared objects and whether their scalar/index spaces agree.
2. Record subject, input scope, observation scope, phase side, exactness,
   ancilla/top-state policy, encoder/decoder, and marginalization policy.
3. State the strongest candidate relation before attempting a wrapper proof.
4. Prove the relation through the actual public definitions and consumers.
5. Attempt the converse on the smallest nontrivial exact examples.
6. If the converse fails, formalize a witness satisfying all advertised
   unitarity, normalization, and dimension assumptions.
7. If the theorem needs a special class—basis-classical, nonempty, dimension at
   least two, commutative scalar—put that condition in its signature.
8. Register the classification only after the proof-bearing theorem compiles.

## Invariants

- Do not narrow “classify every public semantic comparison” without recording
  the manifest consequence and obtaining an exact replacement scope.
- Do not mark a stage complete without requirement-by-requirement evidence.
- A green build proves type correctness, not semantic strength or completeness.
- Prefer small low-dependency leaves; split multi-layer work into the mandatory
  A/B/C milestones in `0-plan.md` before implementation.
- Preserve implementation, proof-side helper, verifier, diagnostic,
  counterexample, fallback, registry metadata, and public API distinctions.
- Registry metadata never substitutes for a theorem inhabiting the relation.
- Same-space equivalence, observational agreement, cross-model certificates,
  algebraic image equivalence, resource equality, and approximation remain
  distinct categories.
- Do not promote one-input evidence to all-basis, all-pure, density, all-effect,
  or channel scope.
- Keep quaternionic state phase on the right, input-column phase on the right,
  and output-row phase on the left.  Never export arbitrary quaternion global
  operator phase.
- Do not identify complex phase after realification with real sign.
- Do not define classical basis behavior for generic operators through a
  vacuous relation; require a certified basis permutation.
- Physical effects carry positivity/order invariants.  Arbitrary trace-test
  matrices remain supporting algebra with distinct names.
- Cross-model simulation declarations expose every encoder, scalar/dimension
  change, top-state quantifier, decoder, and marginal.
- Fixed-budget closeness is not an equivalence relation; triangle theorems add
  budgets explicitly.
- Do not move a Goal 3 row to `closedByGoal2` until its full Goal 2 completion
  evidence—including consumers and axiom audit—is recorded.
- Completed modules remain free of `sorry`, `admit`, `sorryAx`, unexplained
  axioms, unsafe/opaque shortcuts, impossible hypotheses, and tautological
  encodings of target claims.
- Preserve unrelated user changes and keep generated artifacts untracked.

## Verification Layers

1. **Representation probe:** compile the exact mathlib/local API needed for the
   relation, density/effect structure, trace separation, or operator norm.
2. **Focused build:** build every touched semantic leaf directly.
3. **Adjacent consumer:** build a real circuit/state/simulation module using the
   relation-valued theorem.
4. **Law checks:** prove equivalence laws only for genuine equivalence relations
   and additive budget laws for approximation.
5. **Scope checks:** inspect theorem signatures for scalar, dimension, input,
   observation, phase, top-state, and marginal hypotheses.
6. **Strictness checks:** compile exact witnesses for every published missing
   implication or incomparable pair.
7. **Registry checks:** every frozen cohort row appears once and links to a
   proof-bearing wrapper or justified nonbehavioral disposition; every new
   public Goal 2 semantic export appears once in the separate API manifest.
8. **Broader release checks:** public root, explicit audit, warning-as-error,
   downstream import, source/shortcut/stale-path/artifact scans, whitespace,
   and `git diff --check` when required.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, public APIs, builds, frozen cohort registry, Goal 2
  semantic API manifest, documentation, previous stage results, and exact
  examples.
- Assigned inventory rows, relations, and current proof status.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions requiring compiling probes or counterexamples.

## Big Picture Objective

- Restate the stage objective, adjusted for current evidence without weakening
  the original semantic-classification requirement.

## Detailed Implementation Plan

- Concrete definitions, theorem wrappers, hierarchy proofs, counterexamples,
  docs, registry, tests, and consumers for this stage.
- Expected files and primary/fallback proof routes.
- Exact semantic axes and Goal 3 boundaries affected.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- Public API, proof-side, diagnostic, counterexample, metadata, fallback, and
  temporary classifications.
- High-fanout modules avoided or necessarily changed.
- Focused leaf, adjacent consumer, and required broader build commands.

## Boundary Checks

- Same-space/cross-model, state/operator/channel, exact/approximate, phase-side,
  input-scope, observation-scope, and physical-effect boundaries.

## No-Cheating Checks

- Forbidden shortcuts, signature inspections, consumers, and scans proving no
  weaker relation, metadata label, arbitrary test matrix, or false phase action
  is counted as the target theorem.

## Completion Requirements

- Requirement-by-requirement checks from `goal-2/0-plan.md`.
- Proof-bearing classification and strictness evidence for every assigned item.
- Required builds, examples, scans, axiom audits, registry checks, and diff
  commands.
- Traceability, correction, documentation, and Goal 3 rebaseline updates.
- `BUILD-PLAN.md` evidence and fold-back required.

## Stage Results

- Definitions, theorem names, wrappers, counterexamples, and modules delivered.
- Builds, tests, registry checks, scans, and audit outcomes.
- Failed approaches and the exact obstruction they establish.
- Learned facts, remaining theorem targets, and changes required in
  `0-plan.md` or Goal 3 before the next stage.
```

## Session Fold-Back

Before stopping:

1. Update the active stage report with exact evidence.
2. Update `goal-2/0-plan.md` facts and stage status only when every completion
   requirement is covered.
3. Update the frozen cohort registry, Goal 2 semantic API manifest, docs,
   traceability, corrections, AxiomAudit, and Goal 3 forecast for every
   affected result.
4. Record exact theorem names, module paths, failed implications, dimension/
   scalar exceptions, and next actions.
5. Leave the next ready milestone or blocked theorem resumable from a concrete
   command and proof obligation.

Never mark a classification stage complete because relation definitions or a
documentation table exist.  Completion requires the promised hierarchy theorem,
strictness witness, quotient descent, channel result, or proof-bearing wrapper.
