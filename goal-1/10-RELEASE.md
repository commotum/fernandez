# 10-RELEASE

## Current Facts

- Stages 1–9 are complete.  The public root imports every stable mathematical
  leaf, all 101 traceability rows have exactly one terminal status, and the
  correction log contains 26 source issues/repairs.
- Lean 4.31.0 and mathlib v4.31.0 at resolved commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` are pinned by the project files.
- The latest Stage 9 evidence is green: strict root and touched-leaf checks,
  full build (2,553 jobs), compiled axiom audit, downstream root-only smoke,
  hole/shortcut scans, artifact scan, and `git diff --check`.
- The main residual mathematical obstruction is the general determinant-one
  refinement for quaternionic complexification.  Resource/uniformity,
  finite-precision, generic synthesis, mixed-state, physical, cryptographic,
  and open-question boundaries already have terminal documented dispositions.
- Repository-root `BUILD-PLAN.md` remains authoritative for release ownership,
  verification, and fold-back.

## Updated Assumptions

- Release work should not change the mathematical model unless the completion
  audit finds a real correctness or usability defect.
- The public API audit found one such defect: quaternionic
  `RightPhaseEquivalent` had operational invariance theorems but, unlike the
  complex relation, no reflexive/symmetric/transitive packaging.  The checked
  repair belongs in the existing low-dependency phase owner.
- A persistent `docs/ReleaseReport.md` should carry the user-requested report;
  `docs/AxiomAudit.md` should explain the executable audit and its accepted
  standard foundations.
- The public root plus narrow imports are the supported consumer interfaces.
  A downstream smoke must import only `QuaternionicComputing` and exercise the
  major Stage 9 exports in addition to the central simulation theorems.

## Big Picture Objective

Deliver a stable, self-contained Lean library and documentary handoff that a
later project can import without reconstructing the paper's organization.
Prove release readiness requirement by requirement rather than treating a green
build alone as completion evidence.

## Detailed Implementation Plan

- Audit public namespaces, root imports, module paths, theorem names, and README
  usage guidance against the actual compiled environment.
- Add the missing quaternionic right-phase equivalence laws, focused-build the
  owning leaf, and extend the axiom audit before the final broad verification.
- Add a persistent axiom-audit explanation recording the command, audited
  surface, accepted Lean/mathlib foundations, and absence of project axioms.
- Add the final release report covering formalized mathematics, main exports,
  project structure, every material correction category, unresolved/omitted
  claims, exact build/audit results, and future-project usage guidance.
- Cross-check every explicit user requirement and every Stage 10 completion
  requirement against authoritative files or command output.
- Run strict root/audit checks, the full build, root-only downstream smoke,
  terminal-status validation, hole/project-axiom/unsafe/shortcut scans,
  tracked-artifact checks, and `git diff --check`.
- Fold exact release evidence into this file and `0-plan.md`; mark the active
  goal complete only after the requirement audit has no missing item.

## Build Structure

- `Scalar/Phase.lean`: existing low-dependency public API owner; touched only to
  add `rightPhaseEquivalent_refl`, `_symm`, `_trans`, and `_equivalence` after
  the release audit exposed the missing relation packaging.  No scalar
  representation or downstream semantics changes.
- `docs/AxiomAudit.md`: documentary audit result; the executable source remains
  `QuaternionicComputing/AxiomAudit.lean`.
- `docs/ReleaseReport.md`: durable user-facing handoff and requirement summary.
- `README.md`: only small consumer-oriented usage/link corrections if the
  release audit finds them necessary.
- `QuaternionicComputing.lean` and mathematical leaves are high-fanout and
  should remain unchanged unless an actual release blocker is found.
- Focused documentation checks are path/name scans.  Any Lean change requires a
  warning-as-error build of its owner and adjacent consumer before the final
  full build.

## Boundary Checks

- Do not describe exact finite algebraic simulation as a uniform runtime, BQP,
  finite-precision, or primitive synthesis result.
- Do not claim general `SU(2N)` membership for quaternionic complexification;
  retain the proved `det = 1 ∨ -1` boundary.
- Do not turn matrix non-surjectivity into a circuit-width, signaling,
  communication, or information-theoretic lower bound.
- Keep direct Equation 63 realification matrix-only; the public circuit
  corollary remains the explicit two-wire composition.
- Keep literal normalized-column equality, right-phase ray equality, and
  computational-basis distribution equality distinct.
- No release report sentence may outrun a cited Lean declaration, traceability
  disposition, or recorded build/audit command.

## Completion Requirements

- `lake build` and `lake build QuaternionicComputing.AxiomAudit` pass from the
  pinned project root after all release edits.
- A warning-as-error downstream file importing only `QuaternionicComputing`
  checks representative scalar, matrix, state, circuit, simulation, resource,
  direct-map, correction-witness, and example APIs.
- Lean-only scans find no `sorry`, `admit`, `sorryAx`, declaration-level
  `axiom`/`opaque`, `unsafe`, or forbidden noncommutative shortcut.
- Axiom audit results are documented and contain only `propext`,
  `Classical.choice`, and `Quot.sound` for the main exported endpoints.
- All 101 traceability rows have exactly one allowed terminal status; all 26
  corrections have source, diagnosis, repair/obstruction, declarations where
  applicable, and dependent effects.
- README, architecture, conventions, mathlib API notes, traceability,
  corrections, release report, and stage/goal documents are mutually
  consistent and cite only real module paths/declarations.
- No generated build artifact is tracked, and `git diff --check` passes.
- The final report contains every deliverable requested in the original
  objective and gives actionable future-project import guidance.

## Stage Results

- In progress.  Stage opened after verified completion of 9-COVERAGE on
  2026-07-10.
