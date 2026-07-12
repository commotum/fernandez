# 11-REGISTRY

## Milestone Status

- [x] `11A-EXISTING`
- [x] `11B-REGISTRY`
- [x] `11C-DOCS`

## Current Facts

- Stage 10 remains independently closed. Stage 11 now brings the current tree
  to 99 Lean sources including the public root, 1,275 Goal 2 semantic-manifest
  declarations, 167 resolving consumers, 356 direct manifest audit labels,
  542 root axiom commands, and 15 local existing-result audit commands. The
  combined stable/audit/root/release-audit build passes at `2776/2776`; the
  root, existing-result, and retained approximation audit unions are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- `docs/Goal1ComparisonCohort.json` is the immutable pre-retrofit discovery
  boundary: 51 families and 936 uniquely assigned public declarations. Its
  checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
  The file intentionally retains historical provisional descriptions and must
  not be rewritten by Stage 11.
- The 51 families consist of 42 Goal 1 implementation/release or boundary
  families and nine source-only families. Ten rows have empty declaration
  arrays: the Stage 10 boundary row `EQC-042` plus source-only `EQC-043`--
  `EQC-051`. Earlier Goal 2
  stages already supply proof-bearing exact, phase/ray, basis, density/channel,
  hierarchy, cross-model, and metric overlays. The final Stage 11 registry now
  maps all 936 frozen declarations to their strongest checked classification.
- Twelve frozen families are first-owned by Stage 11 and contain 391
  declarations: `EQC-010` (6), `EQC-015` (26), `EQC-017` (42), `EQC-018`
  (41), `EQC-020` (32), `EQC-021` (12), `EQC-022` (30), `EQC-023` (21),
  `EQC-024` (34), `EQC-029` (35), `EQC-039` (2), and `EQC-041` (110).
  Most are algebraic-image, diagnostic, structural, or resource-support
  families rather than behavioral equivalence relations. Their final
  dispositions must be proof-bearing without relabeling them as behavior.
- The completed Stage 11 inventory divides all 51 families into 27 whose
  strongest checked API is already stable, six where a small reusable wrapper
  is justified (`EQC-001`, `EQC-010`, `EQC-016`, `EQC-027`, `EQC-028`, and
  `EQC-039`), eleven direct nonbehavioral/resource dispositions, and seven
  source-only Goal 3 claims. The six wrappers respectively expose the checked
  normalized left-phase rejection, canonical reduced-outer agreement,
  distribution-equality/ray-inequality boundary, commuting-schedule
  `ExactCircuitEq`, exact one-input/all-pure-input ordering boundary, and
  supplied-compiler `ExactCircuitEq`.
- `docs/EquivalenceClassification.md` now distinguishes the frozen historical
  seed from the authoritative final overlay, renders all 51 family records
  between checked markers, and closes the ambiguity backlog without rewriting
  the frozen artifact.
- `docs/Goal2SemanticAPIManifest.json` is independent of the frozen cohort. It
  now covers all 1,275 Goal 2 semantic exports exactly once and must remain
  an independently validated suffix-growing manifest rather than being merged
  into the 936-declaration final classification registry.

## Updated Assumptions

- A new final overlay such as `docs/Goal2ClassificationRegistry.json` is safer
  than mutating the frozen cohort. It should contain exactly 51 family records
  and 936 declaration entries. All ten zero-declaration families, including
  boundary row `EQC-042`, need explicit family records.
- Every declaration-level entry needs its frozen family ID, seven semantic
  axes, strongest final relation/category, proof-bearing Lean consumer or an
  explicit nonbehavioral/resource/source-only disposition, and audit evidence.
  A family label alone is insufficient.
- Stable semantic wrappers belong in a narrow leaf such as
  `Semantics/ExistingResults.lean`. Exhaustive allocations and concrete
  consumers belong in a non-root `Semantics/ExistingResultsAudit.lean`. Purely
  algebraic/resource declarations should be consumed and classified without
  inventing behavioral predicates merely to give them a wrapper.
- Existing exact theorem statements should remain unchanged. Stage 11 should
  add thin named consequences or aggregate certificates only when the current
  public API lacks a proof-bearing strongest classification.
- Source-only rows stay source-only or Goal 3-owned unless an earlier Goal 2
  result genuinely closes them. Boundary row `EQC-042` and source rows
  `EQC-043` and `EQC-044` have Goal 2
  overlays; `EQC-045`--`EQC-051` retain their exact Goal 3/excluded/unsupported
  dispositions.
- Registry validation must check Lean names and consumers, not just JSON
  shape. It must preserve the frozen cohort checksum and independently recheck
  the complete Goal 2 semantic manifest.

## Big Picture Objective

Give every frozen Goal 1 declaration and every source-only family one final,
checked strongest classification. Close the remaining algebraic,
representative, placement, schedule, compiler, diagnostic, and resource
families without treating support mathematics as behavioral equivalence.
Publish an executable registry checker and remove materially ambiguous
equivalence/simulation wording across the project while leaving Goal 3's
unimplemented models explicit.

## Detailed Implementation Plan

### `11A-EXISTING` — proof-bearing remaining families

- Inventory the 391 declarations in the twelve Stage 11-owned families in
  exact frozen order. Identify the strongest existing theorem or necessary thin
  wrapper for each family and its weaker consequences/boundaries.
- Add `QuaternionicComputing/Semantics/ExistingResults.lean` only for stable
  named classifications that are missing. Keep algebraic image equivalences,
  determinant/group facts, Kronecker/place identities, schedule enumeration,
  exact compiler semantics, and structural resources visibly nonbehavioral.
- Add a non-root `Semantics/ExistingResultsAudit.lean` whose source-order
  aggregates allocate every new stable wrapper and consume every Stage
  11-owned frozen declaration through genuine existing results. Include
  concrete representative, image/nonimage, schedule, compiler, and resource
  boundary checks.

### `11B-REGISTRY` — exact declaration registry and checker

- Create a final registry overlay with exactly 936 declaration entries. Preserve
  the frozen family assignment and checksum; apply the checked Goal 2
  classifications, including the `EQC-001` erratum and `EQC-042` Stage 10
  refinement, only in the overlay.
- Record family, same/cross/source space, subject, input scope, observation
  scope, phase side, exactness, ancilla/marginal policy, strongest relation or
  category, proof-bearing wrapper/consumer, weaker consequences, strictness
  witness, final disposition, and Goal 3 boundary.
- Add a maintained validator that proves exact frozen-declaration set/order,
  unique family assignment, all required nonempty fields, allowed disposition
  vocabulary, resolving Lean declarations/consumers, exact audit-label
  intersection, no audit/public-root boundary violation, and unchanged frozen
  checksum.
- Independently revalidate all 1,275 Goal 2 semantic-manifest declarations,
  167 consumers, 356 direct labels, seven axes, source order, prefix/full hashes,
  and public-root/audit boundaries. Never add final-registry entries to the
  semantic manifest merely because they are metadata.

### `11C-DOCS` — final human classification and Goal 3 rebaseline

- Convert `docs/EquivalenceClassification.md` from a provisional seed plus
  overlays into a final family/declaration registry guide. Resolve every item
  in its ambiguity backlog or record an exact remaining Goal 3/source
  obstruction.
- Repair materially ambiguous uses of “equal,” “equivalent,” “same behavior,”
  “preserves,” and “simulates” in README, docstrings, architecture,
  conventions, traceability, corrections, and release documentation.
- Rebaseline Goal 3 from the actual Stage 11 release counts, final
  classification dispositions, the two `closedByGoal2` ray rows, the metric
  prerequisite, and the immutable residual worklist. Do not claim Goal 2 final
  release until Stage 12 independently passes.

## Build Structure

- `Semantics/ExistingResults.lean`: stable thin classifications only; no audit
  imports and no metadata-only proofs.
- `Semantics/ExistingResultsAudit.lean`: non-root exhaustive allocations and
  concrete boundary consumers.
- `docs/Goal2ClassificationRegistry.json`: final overlay over the frozen
  936-declaration cohort.
- A maintained registry validator and generated Lean name/consumer checks;
  temporary generated Lean artifacts remain untracked.
- `QuaternionicComputing.lean`: imports only the stable wrapper leaf if one is
  required.
- `QuaternionicComputing/AxiomAudit.lean`: selected main wrapper endpoints;
  exhaustive local endpoints stay in the non-root audit.
- Focused builds target each new stable/audit leaf, then existing semantic
  audits, the public root, release audit, generated checks, and a root-only
  downstream classification smoke.

## Boundary Checks

- Algebraic `Equiv`/`MulEquiv` onto an embedding image remains algebraic and
  nonbehavioral. Determinant/group membership is not operational simulation.
- Matrix placement/reindexing is not a physical swap circuit or routing cost.
  Schedule enumeration/counts are structural, not circuit equality.
- Supplied exact compiler semantics prove neither compiler existence nor
  synthesis, approximation, resource bounds without their explicit premises,
  runtime, or uniformity.
- One-input witnesses remain one-input. Basis/distribution equality remains
  weaker than ray/channel equality. Cross-model wrappers retain every map,
  added wire, coefficient/top policy, decoder, and observation scope.
- Source-only rows are never made proof-bearing by a registry label. A Goal
  3-owned claim remains unimplemented unless an actual Lean theorem closes it.
- Final registry entries for Goal 2 declarations remain separate from the
  frozen Goal 1 cohort and do not recursively expand the discovery boundary.

## No-Cheating Checks

- No family-level label substitutes for declaration-level exact-once coverage.
- No empty or generic “classified” theorem is accepted unless its type contains
  the actual strongest relation or it consumes the actual nonbehavioral result.
- No impossible premise, broad `simp`/instance, false `Equivalence`, audit
  import, checksum rewrite, generated tracked artifact, `sorry`, `admit`,
  `sorryAx`, declaration axiom, `opaque`, `unsafe`, or heartbeat override.
- Checker success must include generated Lean resolution of every declaration
  and proof consumer, exact source/cohort set comparison, audit intersection,
  allowed-disposition validation, and frozen checksum verification.

## Completion Requirements

- All 51 families have one final strongest checked family classification; all
  936 frozen declarations have exactly one final registry entry with a real
  proof consumer or justified nonbehavioral/resource disposition.
- Every Stage 11-owned family is proof-bearing at its exact scope. No
  algebraic, diagnostic, structural, or resource fact is mislabeled as
  behavioral equivalence.
- The final registry checker, generated 936-name/consumer checks, independent
  1,275-entry semantic-manifest validator, frozen checksum, and exact audit
  intersections pass.
- Stable imports remain narrow; no stable/public leaf imports either audit.
  Focused, adjacent, combined, default, warning-as-error, downstream smoke,
  source/shortcut/false-equivalence/import/artifact/Markdown/whitespace/diff,
  and axiom-union checks pass.
- README, architecture, conventions, classification, traceability,
  corrections, release/axiom reports, Goal 3, this report, and the master plan
  agree. Independent source, mathematical, registry, documentation, Goal 3,
  and integrated closure reviews return **PASS** before Stage 11 is checked.

## Stage Results

- The exact 51-family inventory is complete. It partitions the frozen cohort
  into 27 already-strong stable families, six families needing reusable thin
  wrappers, eleven direct nonbehavioral/resource dispositions, and seven
  source-only Goal 3 claims. The frozen 51-family/936-declaration file and its
  checksum are unchanged.
- Added `Semantics/ExistingResults.lean` with exactly six stable declarations:
  `normalizedQuaternionLeftPhase_rejection`,
  `realCanonicalColumns_reducedOuterAgreement`,
  `quaternionGroundOutputs_distributionEq_not_rayEq`,
  `scheduledCircuit_exactCircuitEq_of_pairwise_commute`,
  `quaternionOrderingWitness_scopeBoundary`, and
  `ExactGateCompiler.compileCircuit_exactCircuitEq`.
- Added non-root `Semantics/ExistingResultsAudit.lean` with 15 endpoints. Its
  three source-order wrapper consumers and concrete boundary endpoint are
  joined by meaningful family consumers for `EQC-015`, `EQC-017`, `EQC-018`,
  `EQC-020`--`EQC-024`, `EQC-029`, and both structural and conditional-
  compiler portions of `EQC-041`. Algebraic image, determinant, placement,
  scheduling, and resource results remain explicitly nonbehavioral.
- Both new leaves pass direct warning-as-error compilation. Their combined
  focused build passes at `2536/2536`; all 15 local audit endpoints have exact
  axiom union `propext`, `Classical.choice`, and `Quot.sound`. An additional
  stable/audit/public-root/release-audit build passes at `2776/2776` after
  public promotion and six root audit additions.
- The tree now has 99 Lean sources including the public root. The root audit
  has 542 commands and the new local audit has 15. The semantic manifest
  appends the six stable declarations in exact source order. It now has
  1,275 unique declarations, 167 resolving consumers, 356 direct root-audit
  labels, and full structural hash
  `bbea85679b6e8425f398f8ab984736472450a440cad984315d4dbd2c62def45f`.
  Stage 11 corrected two Stage 10 strictness entries that were directly printed
  in the root audit through an opened namespace but mislabeled transitive in
  the manifest. Consequently the corrected first-1,269 structural hash is
  `c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229`;
  the prior `298a...` hash remains only historical Stage 10 checkpoint evidence.
  The maintained input validator and all generated frozen/manifest name and
  consumer checks pass at `51/936/10`, `1275/167/356`, and seven axes.
- Added the closed JSON schema and standard-library Python tooling for the
  final registry. They validate frozen order/checksum, semantic-prefix and
  source order, evidence vocabularies, audit/import boundaries, and temporary
  Lean resolution without writing generated files into the repository.
  The 51-family/936-declaration overlay and full validation are complete.
- The final registry assigns all seven semantic axes at both family and
  declaration level. Its family statuses are 33 `proved`, nine
  `correctedAndProved`, two `partiallyFormalized`, and seven `unresolved`;
  declaration audit evidence divides exactly into 208 direct-root and 728
  local-endpoint assignments.
- README, public-root prose, architecture, conventions, classification,
  traceability, corrections, release, and axiom-audit documentation now agree
  with the machine registry. Goal 3 is rebaselined to 101 traceability rows
  with status counts `23/33/26/16/3`, exactly two `closedByGoal2` ray rows, a
  45-row residual ledger, and a separate exact allocation of source-only
  `EQC-045`--`EQC-051`.
- Final checks pass: both validator modes, generated Lean name/consumer checks,
  direct warning-as-error compilation, a root-only downstream smoke, the
  `2776/2776` combined build, frozen checksum, proof-hole/shortcut/import/
  artifact/Markdown/whitespace/diff scans, and the root/local axiom audits.
  The root audit has `539 + 3 = 542` commands and the local audit has 15; both
  unions are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Independent mathematical/source, registry, documentation, Goal 3, and final
  integrated closure reviews all returned **PASS**. Stage 11 is closed; Stage
  12 remains responsible for the clean release and final report.
