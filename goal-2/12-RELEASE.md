# 12-RELEASE

## Milestone Status

- [x] `12A-CLEAN`
- [ ] `12B-AUDIT`
- [ ] `12C-REPORT`

## Current Facts

- Stages 1--11 are independently closed. The current public tree has 102 Lean
  sources including `QuaternionicComputing.lean`, 1,290 semantic-manifest
  declarations, 169 resolving consumers, 371 direct audit labels, and a
  51-family/936-declaration final classification registry.
- The frozen Goal 1 cohort checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
  The corrected first-1,269 semantic-manifest hash is
  `c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229`;
  the preserved first-1,275 hash is
  `bbea85679b6e8425f398f8ab984736472450a440cad984315d4dbd2c62def45f`.
  The full 1,290-entry hash is
  `3146d7785774b7cff4b0a3bd7335a3fe6e55e220722b1672251edcf506980fa3`.
- The root axiom audit has 557 commands (`554 + 3`), the existing-results
  audit has 15 (`15 + 0`), and the projective-input audit has four (`4 + 0`).
  Their collective axiom unions are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The shared pinned dependency cache was cleaned and the baseline public tree
  rebuilt at `2782/2782`. Before the generic kernel refinement, the default,
  integrated, and exhaustive maintained-audit builds passed at `2775/2775`,
  `2777/2777`, and `2787/2787`; warning-as-error compilation and the root-only
  downstream smoke also passed. Final post-refinement build evidence remains a
  `12B-AUDIT` obligation.
- Goal 3 consumes a 101-row traceability table with status counts
  `23/33/26/16/3`, exactly two `closedByGoal2` ray rows, a 45-row residual
  ledger, and a separate exact assignment of unresolved source families
  `EQC-045`--`EQC-051`.

## Updated Assumptions

- The release audit found an actual hierarchy defect: raw and normalized
  projective action must imply input-column phase, but the public graph omitted
  that covering arrow. Stage 12 adds a narrow nine-theorem stable leaf.
- A second semantic review found a stronger generic kernel: arbitrary
  rectangular real or complex raw projective agreement already forces one
  global sign or phase. No unitarity, nonempty-index, square-matrix, or finite-
  output assumption is needed; only the input type is finite. The normalized
  and circuit consequences add six stable arrows in a second narrow leaf.
- The four-endpoint non-root audit consumes both stable leaves and retains the
  quaternionic boundary: the full unit-quaternion projective kernel is already
  visible in rank one and cannot be replaced by central-sign equality.
- The public root should remain the only import needed by downstream users.
  Audit leaves, generated checks, registry implementation details, and the
  paper's original organization remain non-public implementation evidence.
- A green cached build is insufficient for final release. The pinned toolchain,
  clean default build, explicit audit build, strict compilation, executable
  registries, and root-only smoke all need fresh evidence.
- The seven unresolved registry families and all partially formalized or
  intentionally excluded traceability rows remain explicit Goal 3 boundaries;
  release wording must not convert them into proved claims.

## Big Picture Objective

Publish Goal 2 as a reproducible semantic-comparison library that a later Lean
project can import without knowing the retrofit history. Verify the complete
relation hierarchy, classification registry, cross-model boundaries, metric
boundary, ray closures, public imports, axioms, documentation, and Goal 3
handoff, then record one final evidence-backed release report.

## Detailed Implementation Plan

### `12A-CLEAN` — pinned clean build and downstream surface

- Verify the pinned Lean and mathlib revisions from the actual toolchain and
  lock files.
- Remove only generated build output through the normal Lake clean operation,
  then run the full default build and explicit stable/audit/root targets.
- Strict-compile the public root, root audit, stable Stage 11 leaf, and local
  existing-results audit with warnings as errors.
- Compile a temporary downstream file importing only `QuaternionicComputing`
  and checking representative exact, phase/ray, basis, density/channel,
  hierarchy, cross-model, approximation, and existing-result APIs.

### `12B-AUDIT` — executable release invariants

- Run the complete classification-registry/semantic-manifest validator and its
  generated Lean checks; independently recompute registry counts, hashes,
  audit intersections, and the frozen checksum.
- Parse every selected root/local audit endpoint and verify the documented
  counts and exact collective axiom union.
- Scan all completed Lean modules for proof holes, project axioms, `opaque`,
  `unsafe`, unlimited heartbeats, false `Equivalence` instances, audit imports,
  stale paths, and tracked generated artifacts.
- Check Markdown structure, line length, whitespace, source counts, public
  imports, documentation counts, traceability/correction arithmetic, and
  `git diff --check`.
- Obtain independent semantic-graph/registry, release/build/axiom, and
  Goal-3/documentation reviews. Repair and rerun any affected check before a
  reviewer may return **PASS**.

### `12C-REPORT` — final release and reusable handoff

- Update README and release documentation only where the clean release changes
  evidence or removes a stale “pending” statement.
- Record the stable API layers, principal exported definitions/theorems,
  hierarchy and strictness boundaries, corrections, deliberately unresolved
  claims, project structure, build results, axiom results, and downstream usage
  guidance.
- Fold final counts and evidence into `goal-2/0-plan.md`, `goal-2/0-prompt.md`,
  this report, and the Goal 3 prerequisite wording. Mark Goal 2 complete only
  after all independent reviews and the final post-edit checks pass.

## Build Structure

- `Semantics/Hierarchy/ProjectiveInput.lean` owns the nine missing raw,
  normalized, and circuit projective-to-input covering arrows.
- `Semantics/Hierarchy/ProjectiveKernel.lean` owns six generic real/complex
  raw, normalized, and circuit projective-to-global arrows.
- `Semantics/ProjectiveInputAudit.lean` remains non-root and owns both complete
  consumers plus explicit quaternionic sided-phase and kernel boundaries.
- `QuaternionicComputing/AxiomAudit.lean` and all `*Audit.lean` leaves remain
  proof-side verification and are not imported by the public root.
- Registry generators write only temporary files outside the repository.
- Focused targets: `QuaternionicComputing.Semantics.ExistingResults`,
  `QuaternionicComputing.Semantics.ExistingResultsAudit`,
  `QuaternionicComputing.Semantics.Hierarchy.ProjectiveInput`,
  `QuaternionicComputing.Semantics.Hierarchy.ProjectiveKernel`,
  `QuaternionicComputing.Semantics.ProjectiveInputAudit`,
  `QuaternionicComputing`, and `QuaternionicComputing.AxiomAudit`.
- Adjacent verification includes the default `lake build`, strict direct Lean
  compilation, complete registry-generated checks, and a public-root-only
  downstream smoke.

## Boundary Checks

- Exact, phase/ray, basis/distribution, channel/all-effect, cross-model, and
  metric statements retain their distinct spaces, phase sides, input scopes,
  observations, exactness, and ancilla/marginal policies.
- Algebraic image equivalences, placement identities, schedule enumeration,
  and conditional compiler/resource bounds remain nonbehavioral.
- No source-only, mixed-top, partial-trace, finite-encoding, synthesis,
  accumulated-error, runtime, routing, uniform-family, BQP, or QTM claim is
  promoted by release prose or registry metadata.
- The two ray rows close only through normalized quotient equality and
  descended operations; complex realification still targets the proved orbit
  quotient rather than ordinary real sign rays.
- Generic projective-to-global collapse is specific to commutative real and
  complex scalars. Quaternionic projective action still has the full rank-one
  unit-quaternion exception and does not imply central-sign equality.

## No-Cheating Checks

- No `sorry`, `admit`, `sorryAx`, new axiom, impossible premise, `opaque`,
  `unsafe`, unlimited-heartbeat override, broad false equivalence instance,
  audit import into stable code, checksum rewrite, or tracked generated output.
- No cached-only build evidence, metadata-only classification, uncompiled
  downstream example, or manually asserted axiom count is accepted.
- No unresolved or excluded source claim is silently weakened, relabeled, or
  omitted from the final report and Goal 3 handoff.

## Completion Requirements

- Pinned clean default and explicit audit builds pass; all required stable and
  audit leaves strict-compile; the public-root downstream smoke compiles.
- The full registry validator passes at exactly `51/936/10`, `1290/169/371`,
  and seven axes; hashes, frozen checksum, audit intersections, and source order
  reproduce exactly.
- Root/local audit counts and unions match the documented `557`, `15`, `4`,
  and `{propext, Classical.choice, Quot.sound}` evidence.
- All shortcut, proof-hole, import, artifact, Markdown, whitespace, stale-path,
  and diff checks pass after the final documentation edits.
- Independent semantic, release/audit, Goal 3/documentation, and integrated
  reviews return **PASS**.
- Final documentation contains what was formalized, main exports, project
  structure, material paper corrections, unresolved/omitted material,
  build/axiom evidence, and future-use guidance. Master plan/prompt, release
  report, traceability, corrections, registry guide, and Goal 3 agree.

## Stage Results

- Pinned Lean 4.31.0 and mathlib v4.31.0 at
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` were verified from the actual
  toolchain, manifest, and checkout. Lake's normal clean operation removed the
  shared generated cache, and the public baseline rebuilt at `2782/2782`.
- Independent semantic review found the missing projective-to-input covering
  arrow. Added `Hierarchy/ProjectiveInput.lean` with exactly nine declarations:
  raw, normalized, and evaluator-backed circuit arrows over real, complex, and
  quaternionic scalars. Each proof specializes projective action to a basis
  column and retains the correct phase side.
- Added non-root `ProjectiveInputAudit.lean`. Its column- and row-phased
  all-ones quaternionic matrices prove input/output phase incomparability and
  that neither one-sided relation implies projective action.
- A final generic-kernel review strengthened the real/complex graph. New
  `Hierarchy/ProjectiveKernel.lean` proves that arbitrary rectangular raw
  projective agreement is one global sign or phase, then derives normalized
  and evaluator-backed circuit forms. The proof covers zero matrices and empty
  index types and needs no unitarity. Quaternionic rank one remains the exact
  obstruction to adding the analogous central-sign arrow.
- The public root imports only the two stable leaves. All nine declarations are
  appended after the preserved 1,275-entry semantic-manifest prefix; the six
  generic kernel declarations follow them. All 15 are selected directly by
  the root axiom audit. The current manifest is `1290/169/371` with seven axes
  and full hash
  `3146d7785774b7cff4b0a3bd7335a3fe6e55e220722b1672251edcf506980fa3`.
- Exact audit parsing reports root `554 + 3 = 557`, existing-results `15 + 0`,
  and projective-input `4 + 0`, each with union exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- The first hierarchy repair passed focused, default, integrated, exhaustive,
  strict, validator, and downstream checks. Final post-generic-kernel builds,
  scans, documentation checks, and independent release verdicts remain under
  `12B-AUDIT` and `12C-REPORT`.
