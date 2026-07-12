# 12-RELEASE

## Milestone Status

- [ ] `12A-CLEAN`
- [ ] `12B-AUDIT`
- [ ] `12C-REPORT`

## Current Facts

- Stages 1--11 are independently closed. The current public tree has 99 Lean
  sources including `QuaternionicComputing.lean`, 1,275 semantic-manifest
  declarations, 167 resolving consumers, 356 direct audit labels, and a
  51-family/936-declaration final classification registry.
- The frozen Goal 1 cohort checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
  The corrected first-1,269 semantic-manifest hash is
  `c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229`;
  the full 1,275-entry hash is
  `0e65c11f13e05341558a96d0113a6362f32f5549a4ee39e47bdce8cd13dc5efb`.
- The root axiom audit has 542 commands (`539 + 3`) and the existing-results
  audit has 15 (`15 + 0`). Their collective axiom unions are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The latest combined stable/audit/root/release-audit build passes at
  `2776/2776`; a root-only downstream smoke resolves all six Stage 11 wrappers.
  Stage 12 must still reproduce the release from a clean build directory and
  independently audit the complete published surface.
- Goal 3 consumes a 101-row traceability table with status counts
  `23/33/26/16/3`, exactly two `closedByGoal2` ray rows, a 45-row residual
  ledger, and a separate exact assignment of unresolved source families
  `EQC-045`--`EQC-051`.

## Updated Assumptions

- Stage 12 should not add mathematical API unless a release audit finds an
  actual defect. Its main work is reproducibility, independent cross-checking,
  final documentation, and downstream usability.
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

- No new stable Lean module is planned. Existing semantic leaves remain the
  public implementation; `QuaternionicComputing.lean` is the downstream root.
- `QuaternionicComputing/AxiomAudit.lean` and all `*Audit.lean` leaves remain
  proof-side verification and are not imported by the public root.
- Registry generators write only temporary files outside the repository.
- Focused targets: `QuaternionicComputing.Semantics.ExistingResults`,
  `QuaternionicComputing.Semantics.ExistingResultsAudit`,
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
- The full registry validator passes at exactly `51/936/10`, `1275/167/356`,
  and seven axes; hashes, frozen checksum, audit intersections, and source order
  reproduce exactly.
- Root/local audit counts and unions match the documented `542`, `15`, and
  `{propext, Classical.choice, Quot.sound}` evidence.
- All shortcut, proof-hole, import, artifact, Markdown, whitespace, stale-path,
  and diff checks pass after the final documentation edits.
- Independent semantic, release/audit, Goal 3/documentation, and integrated
  reviews return **PASS**.
- Final documentation contains what was formalized, main exports, project
  structure, material paper corrections, unresolved/omitted material,
  build/axiom evidence, and future-use guidance. Master plan/prompt, release
  report, traceability, corrections, registry guide, and Goal 3 agree.

## Stage Results

- Pending execution.

