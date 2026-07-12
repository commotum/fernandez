# 9B-WRAPPERS

## Current Facts

- Stage 9B is independently complete. The checkpoint has 88 Lean sources
  including the public root, 1,064 exact semantic-manifest entries, 133
  resolving consumers, 272 direct release-audit labels, 458 root axiom
  commands, and 16 local `SimulationAudit` commands. The exact axiom union is
  `propext`, `Classical.choice`, and `Quot.sound`.
- `Semantics/Simulation.lean` exports the directional relations needed here:
  `ExactOperatorEmbedding`, `StateIntertwining`, and
  `AllTopStateIntertwining`. Their encoders and embeddings remain explicit;
  none is a same-carrier equivalence relation.
- The frozen Goal 1 cohort assigns exactly eleven families to Stage 9B. Their
  comparison content and intended wrappers are fixed as follows:

| Family | Existing strongest evidence | Stage 9B wrapper allocation |
|---|---|---|
| `EQC-008-REAL-COLUMNS-INTERTWINING` | `realify_mulVec_realTopCombination`, subsuming both canonical columns | `realifyMatrix_allCoefficient_stateIntertwining` |
| `EQC-012-COMPLEX-COLUMNS-INTERTWINING` | `complexify_mulVec_complexTopCombination`, subsuming both canonical columns | `complexifyMatrix_allCoefficient_stateIntertwining` |
| `EQC-019-DIRECT-REALIFY-REINDEX` | `directRealify_eq_reindex` | `directRealify_exactOperatorEmbedding` |
| `EQC-025-WIRE-EMBED-PLACEMENT` | `realifyPlacedGate_denote`, `complexifyPlacedGate_denote` | two placed-gate operator wrappers |
| `EQC-030-C2R-OPERATOR` | `eval_realifyCircuit` | `realifyCircuit_exactOperatorEmbedding` |
| `EQC-031-C2R-STATE` | `eval_realifyCircuit_mulVec_wireRealTopCombination` | `realifyCircuit_allCoefficient_stateIntertwining` |
| `EQC-033-Q2C-OPERATOR` | `eval_complexifyCircuit` | `complexifyCircuit_exactOperatorEmbedding` |
| `EQC-034-Q2C-STATE` | `eval_complexifyCircuit_mulVec_wireComplexTopCombination` | `complexifyCircuit_allCoefficient_stateIntertwining` |
| `EQC-036-SCHEDULED-Q2C` | fixed-schedule operator embedding and injective preservation of an operator gap | three scheduled wrappers |
| `EQC-037-Q2R-COMPOSED` | `eval_quaternionToRealCircuit` and nested state intertwining | two composed wrappers |
| `EQC-040-COMPILED-IMAGE-SEMANTICS` | `eval_compile_realifyCircuit`, `eval_compile_complexifyCircuit` under supplied compiler data | two conditional compiler wrappers |

- A read-only prototype at `/private/tmp/Stage9BWrapperProbe.lean` strict-
  compiles the exact proposed 16 declarations, a nonvacuous unequal-schedule
  consumer, and an inhabitable identity-compiler consumer. All 16 prototype
  axiom endpoints use exactly the standard three-item union. The prototype is
  evidence for the signatures, not a substitute for repository implementation
  or audit coverage.
- The source theorems already preserve arbitrary coefficient pairs, which is
  strictly more general at the amplitude level than normalized `Rebit` or
  `Qubit` coefficients. The wrappers should therefore quantify `ℝ × ℝ`,
  `ℂ × ℂ`, or nested `(ℂ × ℂ) × (ℝ × ℝ)` coefficient data and must not call
  those pairs pure states or product subsystems.
- Stage 9C still owns all decoded basis probabilities, normalized
  distributions, events, and deterministic postprocessing. Stage 9B must not
  finalize any of those five families merely because their source theorems are
  imported.

## Updated Assumptions

- One wrapper per strongest family conclusion is preferable to wrapping both
  canonical columns separately when one arbitrary-coefficient theorem
  constructively specializes to `(1,0)` and `(0,1)`. The audit must perform
  those specializations so the canonical evidence is not merely implicit.
- Equation 63 is exactly a row/column reindexing of the composed matrix
  embedding. It is not a second wire-facing circuit translator and receives no
  `ExactCircuitEq` wrapper.
- A supplied legal schedule determines one chronological source circuit. Its
  wrapper may preserve both the mapped operator and arbitrary-coefficient state
  action. The existing injectivity theorem may also expose a concrete
  non-independence boundary, but no theorem chooses a schedule or identifies
  distinct schedules.
- `ExactGateCompiler` is explicit input data. Wrapping its exact evaluator is
  conditional and does not prove compiler existence, a finite primitive set,
  synthesis, approximation, gate-count complexity, or runtime.
- Placement support, local arity, gate count, width, and depth remain separate
  algebraic/resource facts. An operator-embedding wrapper must not bundle them
  into its semantic relation.

## Big Picture Objective

Give every existing operator-, state-, reindex-, schedule-, and conditional-
compiler comparison assigned to Stage 9B a strongest proof-bearing directional
wrapper. Keep every scalar/index change, added-wire map, coefficient policy,
schedule, and compiler premise visible, so none of these exact simulations can
be confused with same-space equality or an observational/channel theorem.

## Detailed Implementation Plan

- Add `QuaternionicComputing/Semantics/SimulationWrappers.lean` with exactly
  these 16 stable public declarations in source/logical order:
  1. `realifyMatrix_allCoefficient_stateIntertwining`;
  2. `complexifyMatrix_allCoefficient_stateIntertwining`;
  3. `directRealify_exactOperatorEmbedding`;
  4. `realifyPlacedGate_exactOperatorEmbedding`;
  5. `complexifyPlacedGate_exactOperatorEmbedding`;
  6. `realifyCircuit_exactOperatorEmbedding`;
  7. `complexifyCircuit_exactOperatorEmbedding`;
  8. `realifyCircuit_allCoefficient_stateIntertwining`;
  9. `complexifyCircuit_allCoefficient_stateIntertwining`;
  10. `scheduledComplexifyCircuit_exactOperatorEmbedding`;
  11. `scheduledComplexifyCircuit_allCoefficient_stateIntertwining`;
  12. `scheduledComplexifyCircuit_eval_ne_of_source_ne`;
  13. `quaternionToRealCircuit_exactOperatorEmbedding`;
  14. `quaternionToRealCircuit_allCoefficient_stateIntertwining`;
  15. `compileRealifyCircuit_exactOperatorEmbedding`;
  16. `compileComplexifyCircuit_exactOperatorEmbedding`.
- Use only the exact source theorems and transparent relation constructors. Do
  not restate or reprove source matrix algebra in the wrapper leaf.
- Extend the non-root `Semantics/SimulationAudit.lean` with six disjoint
  aggregate consumers allocating the 16 declarations exactly as
  `2 + 3 + 4 + 3 + 2 + 2`:
  `matrixStateIntertwining_wrappers_api`,
  `reindexPlacement_wrappers_api`,
  `primaryCircuit_wrappers_api`,
  `scheduledCircuit_wrappers_api`,
  `composedCircuit_wrappers_api`, and
  `compiledCircuit_wrappers_api`.
- In the audit, specialize arbitrary coefficients to both canonical pairs,
  exercise rectangular matrix input, use the existing ordering witness for a
  real unequal-schedule consumer, construct a local identity compiler to show
  the conditional premise is inhabitable, and check raw empty/zero-wire cases
  without manufacturing normalized empty states.
- Promote only the stable wrapper leaf through `QuaternionicComputing.lean`.
  Add all 16 stable declarations as direct root axiom-audit endpoints and the
  six aggregate consumers as local diagnostic endpoints.
- Append the 16 declarations exactly once to the semantic API manifest with all
  seven axes and named aggregate consumers. Preserve the first-1,048 hash and
  the frozen Goal 1 cohort checksum. The resulting checkpoint has 1,064
  manifest entries, 133 consumers, 272 direct labels, and 458 root axiom
  commands.
- Fold the exact classifications into public documentation, traceability,
  corrections only if a paper issue is discovered, Goal 3 prerequisites, this
  report, and `goal-2/0-plan.md`. Keep Stage 9C and the umbrella Stage 9 open.

## Build Structure

- `QuaternionicComputing/Semantics/SimulationWrappers.lean`: stable high leaf
  containing only the 16 proof-bearing wrappers. It may public-import the
  generic relation leaf, Equation 63 matrix representation, composed
  simulation, scheduled simulation, and conditional compiled-resource leaves.
  It must not import the public root, any audit, outcome/postprocessing leaf,
  hierarchy audit, or ordering witness.
- `QuaternionicComputing/Semantics/SimulationAudit.lean`: non-root diagnostic
  allocation and concrete consumers. It may additionally import the stable
  wrapper and the existing ordering witness; no stable module imports it.
- `QuaternionicComputing.lean`: public re-export of the stable wrapper only.
- `QuaternionicComputing/AxiomAudit.lean`: direct endpoints for all 16 wrappers.
- High-fanout matrix, state, circuit, simulation-source, relation-core,
  channel, hierarchy, and outcome leaves remain unchanged.
- Focused command:
  `lake build QuaternionicComputing.Semantics.SimulationWrappers`.
- Adjacent commands:
  `lake build QuaternionicComputing.Semantics.SimulationAudit
  QuaternionicComputing QuaternionicComputing.AxiomAudit` plus warning-as-error
  direct source checks.

## Boundary Checks

- `ExactOperatorEmbedding` always states target operator equals a named image
  of the source; changed scalar and wire types remain in the signature.
- `AllTopStateIntertwining` uses raw coefficient pairs and all raw source
  columns. It asserts exact amplitude action, not normalization, a top/bottom
  tensor factor, ray equality, basis probabilities, density evolution, or a
  channel.
- The composed quaternion-to-real coefficient order is inner complex pair then
  outer real pair. Encoder composition order must be visible in the theorem.
- Equation 63 uses its named row and column equivalences and is never described
  as literal equality to the composed matrix without reindexing.
- Scheduled wrappers quantify one supplied `LegalSchedule`; the negative
  theorem demonstrates that translation preserves a source operator gap. No
  schedule selection, quotient, or independence is inferred.
- Compiler wrappers require a supplied `ExactGateCompiler`; no existence,
  primitive finiteness, synthesis, approximation, count bound, or runtime is
  inferred.
- Stage 9C outcomes and all same-space ray/channel/all-effect relations remain
  absent from the wrapper signatures.

## No-Cheating Checks

- No wrapper is defined as a tautological self-embedding when an existing
  mapped/reindexed theorem supplies a more informative embedding function.
- No use of `ExactOperatorEq`, `ExactCircuitEq`, `ChannelEq`,
  `AllMeasurementEq`, `BasisMeasurementEq`, or ray equality appears in the
  stable wrapper conclusions.
- No `Equivalence`, reflexivity, symmetry, transitivity, or global simplifier
  declaration is added for a directional certificate.
- The schedule inequality consumer uses the existing explicit two-schedule
  witness, not a hypothetical inequality premise alone.
- The compiler consumer supplies an actual locally defined compiler value but
  is documented only as premise inhabitation, not generic synthesis.
- No `sorry`, `admit`, `sorryAx`, declaration axiom, `opaque`, `unsafe`,
  heartbeat override, impossible normalized empty value, public audit import,
  tracked generated artifact, or frozen-cohort edit.

## Completion Requirements

- All 16 stable wrappers strict-compile and each of the eleven assigned cohort
  families has its strongest checked directional classification.
- Six non-root aggregates allocate all 16 wrappers exactly once and exercise
  canonical, rectangular, schedule-gap, conditional-compiler, and empty/
  zero-wire boundaries through real values.
- The stable leaf has only the five justified narrow public imports; no audit,
  outcome, channel, hierarchy, or root import leaks into it.
- Public root, all existing simulation examples, the extended audit, and a
  root-only downstream smoke compile with warnings as errors.
- The semantic manifest has exact source order, seven nonempty axes, exact
  consumer allocation, exact direct-audit intersection, preserved first-1,048
  hash, and unchanged frozen Goal 1 checksum. Generated names and consumers
  strict-compile from a freshly rerun generator.
- Root and local axiom parsers cover every emitted block and contain exactly the
  permitted standard union, with no unknown identifier or `sorryAx`.
- Hole/shortcut/false-equivalence/import-boundary/artifact/whitespace/Markdown/
  stale-wording/diff scans pass, and exact results are folded into all affected
  documentation and Goal 3.
- Independent integrated review returns PASS before `9B-WRAPPERS` is marked
  complete. Stage 9C and `9-CROSSMODEL` remain open.

## Stage Results

- Added the stable public leaf
  `QuaternionicComputing/Semantics/SimulationWrappers.lean` with exactly the 16
  planned declarations. All eleven frozen families now have proof-bearing
  directional wrappers at their strongest justified operator, state,
  reindexing, supplied-schedule, or conditional-compiler scope.
- The wrapper leaf has exactly the five authorized public imports. It does not
  import an audit, outcome, channel, hierarchy, or public-root module, and the
  public root exports only the stable leaf.
- Extended the non-root `SimulationAudit` with exactly six disjoint aggregate
  consumers, allocating the wrappers as `2 + 3 + 4 + 3 + 2 + 2`. The consumers
  exercise rectangular and empty matrix inputs, both canonical coefficient
  pairs at matrix and circuit level, actual placed gates, the existing
  unequal-schedule witness, nested quaternion-to-real coefficients, an
  inhabitable identity compiler, and the zero-wire circuit boundary.
- Preserved every material boundary in the theorem types: arbitrary raw
  coefficient pairs are not normalized/product claims; Equation 63 is a named
  row/column reindexing rather than a circuit translator; schedules are
  supplied rather than chosen or quotient-independent; and compiler results
  require explicit `ExactGateCompiler` data without proving synthesis,
  approximation, gate counts, or runtime. No outcome, ray, density, channel,
  all-effect, mixed-top, or partial-trace result was inferred.
- The first audit draft exposed a definitional mismatch when canonical
  coefficient specializations were simplified directly to the named column
  maps. The repaired consumer states the literal specializations supplied by
  the all-coefficient wrapper, and a second review strengthened the circuit
  aggregate to cover all four canonical specializations explicitly.
- Focused builds pass at `2369` for the stable wrapper and `2381` for the audit.
  The combined stable/audit/public-root/release-audit build passes at
  `2767/2767`, and the cached default build completes `2765` jobs. All stable,
  audit, root, release-audit, and root-only downstream files strict-compile with
  warnings as errors.
- The semantic manifest contains 1,064 unique declarations, 133 consumers, and
  272 direct audit labels. Its first-1,048 hash remains
  `3094cfd9a97646f24dbbb58002eacdddbe5dad746c80c920087059760638b7b5`,
  and its full hash is
  `ece77e3bd826d5f2db8cc63d14a6733910c5563cb473c5f518111eaccdfcade4`.
  Generated name and consumer checks pass; the frozen Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- Axiom parsing covers all 458 root blocks as `455 + 3` and all 16 local blocks
  as `15 + 1`; both unions are exactly `propext`, `Classical.choice`, and
  `Quot.sound`, with no `sorryAx` or unknown declaration. Hole, shortcut,
  false-equivalence, import-boundary, artifact, Markdown, whitespace, stale-
  wording, and diff checks pass.
- README, public docstring, architecture/conventions/API notes,
  classification, release and axiom reports, traceability, corrections, and
  Goal 3 prerequisites all record the exact Stage 9B result. No new paper
  correction was required.
- Independent source, semantic, manifest, documentation, and integrated closure
  reviews returned **PASS**. Stage 9B is complete; Stage 9C and the umbrella
  Stage 9 remain open.

## Completion Status

- [x] Stage 9B is complete. Stage 9 remains open for 9C.
