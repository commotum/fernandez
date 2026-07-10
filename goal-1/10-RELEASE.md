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

- Completed 2026-07-10 after verified completion of 9-COVERAGE.
- The public API audit found one reusable gap rather than changing the model:
  quaternionic `RightPhaseEquivalent` lacked relation packaging.
  `Scalar/Phase.lean` now exports reflexivity, symmetry, transitivity, and
  `rightPhaseEquivalent_equivalence`.  Direct warning-as-error compilation and
  focused `lake build QuaternionicComputing.Scalar.Phase` passed (2,342 jobs).
  The audit now also checks quaternionic total-weight phase invariance.
- The root/API audit verified that all 42 README narrow imports exist and cover
  all 42 non-audit leaves; the Architecture tree covers all 43 modules below
  `QuaternionicComputing/`; the public root exposes every stable family; and no
  stale path, namespace collision, or unqualified low-rank properness claim
  remains.
- `docs/AxiomAudit.md` records the executable audit policy and
  `docs/ReleaseReport.md` supplies the requested durable handoff: formalized
  content, main exports, project structure, all 26 correction summaries,
  unresolved/partial/excluded scope, build/audit evidence, and future-project
  guidance.  README links both reports and includes the selected narrow import
  surface.
- Reproducibility inspection confirmed Lean 4.31.0, mathlib v4.31.0, resolved
  mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, and all eight
  transitive checkout HEADs match the manifest.  The dependency checkouts were
  clean; network bootstrap from a fresh clone was not rerun.
- `lake clean quaternionicComputing` removed stale root-package objects.  The
  subsequent `lake build` freshly rebuilt the 43-module public-root closure and
  completed 2,553 jobs.  `lake build QuaternionicComputing.AxiomAudit` compiled
  the remaining diagnostic source and completed 2,553 jobs.  Together the two
  commands cover all 44 current/tracked Lean sources; no stale Smoke or old
  EntanglementWitness object remains.
- Warning-as-error compilation passed for `Scalar/Phase.lean`,
  `QuaternionicComputing.lean`, and `AxiomAudit.lean`.  Parsing all 186
  `#print axioms` results found zero dependency outside `propext`,
  `Classical.choice`, and `Quot.sound`.
- `/tmp/ReleaseImportSmoke.lean` imported only `QuaternionicComputing`, checked
  representative scalar, phase, matrix, state, placement, schedule, simulation,
  resource, distribution, correction-witness, and example declarations, and
  proved `card (DirectRealIndex Bool) = 8`; it compiled with warnings as errors.
- Terminal-status validation found exactly 101 rows with one allowed status:
  21 proved as stated, 33 corrected and proved, 28 partially formalized, 16
  intentionally excluded, and 3 unresolved.  All 26 correction entries have
  source/status/diagnosis, a repair or documentary resolution, and dependent
  effects; 25 mathematical entries cite Lean declarations.
- Final Lean-only hole/project-axiom/opaque/unsafe scans, forbidden
  noncommutative-shortcut scans, stale-path scans, tracked-artifact checks, and
  trailing-whitespace scans were empty.  All 44 Lean sources are tracked,
  `git diff --check` passed, and no generated Lake/Lean artifact is tracked.
- An independent requirement-to-evidence audit checked every original user
  deliverable and every BUILD-PLAN/Stage 10 completion criterion.  After this
  fold-back it found no remaining mathematical, API, documentation, build,
  audit, coverage, or release blocker.
