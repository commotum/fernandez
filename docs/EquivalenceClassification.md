# Semantic Equivalence Classification

## Status and purpose

This document is the human-readable guide to Goal 2's completed semantic
classification registry. The Stage 1 table below remains a historical rendering
of the pre-retrofit discovery seed: its wording records what was known then and
is not the final classification. The machine-readable seed is the immutable
`Goal1ComparisonCohort.json`; the final checked overlay is
`Goal2ClassificationRegistry.json`. The latter assigns every frozen declaration
exactly once and is authoritative for final statuses, semantic classes, evidence
modes, proof declarations, audit endpoints, seven-axis classifications,
dispositions, and Goal 3 boundaries.

The catalog freezes the membership of 51 family-level rows. The first 42 come
from the completed
library and its release evidence.  The final nine are source-paper comparison
families that are absent, partial, external, or deliberately assigned to later
work. Freezing these rows prevented later Goal 2 declarations from making the
Goal 1 inventory grow recursively. The final overlay contains the same 51
families and all 936 frozen declarations; it does not mutate that historical
boundary.

## Scope policy

- A **seed family row** groups declarations that appeared to express one
  mathematical comparison at discovery time. It is stable enough for historical
  review and ownership, but its prose is neither final nor
  declaration-authoritative.
- Exact declaration names, source references, aliases, wrapper theorems, and
  audit endpoints belong in the machine-readable `Goal1ComparisonCohort` JSON.
  Its array fields are authoritative for declaration-level coverage and its
  checksum must remain unchanged after the cohort is frozen.
- New public relations, hierarchy theorems, counterexamples, wrappers, and
  metrics created by Goal 2 belong in the separate `Goal2SemanticAPIManifest`
  JSON.  They do not become new rows in this table or alter the frozen cohort
  checksum.
- Final classifications belong in `Goal2ClassificationRegistry.json`. It
  covers the 936 frozen declarations, whereas the independent semantic API
  manifest covers the 1,290 declarations introduced by Goal 2. Neither file is
  a substitute for the proof declaration and audit endpoint named by its rows.
- “Same space” means the compared objects have the same scalar and index type.
  “Cross space” includes scalar change, dimension change, reindexing, encoding,
  decoding, or marginalization.  “Source only” records a paper claim for which
  Goal 1 has no completed public comparison theorem.
- Exact representative equality, ray equality, mapped-operator equality,
  state intertwining, basis-distribution agreement, channel equality, and
  algebraic equivalence onto an image are different classifications.
- Fixed-input, basis-input, all-pure-input, mixed-input, all-effect, and
  algorithm-family quantifiers are never interchangeable.
- Quaternionic state phase and input-column phase act on the right.
  Quaternionic output-row phase acts on the left. Goal 2 Stage 3C proves that
  the genuine projective operator kernel in square unitary dimension at least
  two is exactly a central real sign, and proves the one-dimensional full-unit-
  quaternion exception. An arbitrary unit quaternion is therefore never
  treated as matrix-wide operator global phase.
- Over the real and complex scalars, the final arbitrary-rectangular kernel is
  stronger: raw projective action, normalized projective action, and one
  matrix-wide sign/phase are equivalent for every finite input type. This
  includes zero matrices, empty input or output types, and rank-one matrices;
  it requires no unitarity, squareness, rank, or output-finiteness hypothesis.
- An `Eq`, `Equiv`, `MulEquiv`, group-image theorem, resource equality, or green
  build is not behavioral evidence unless a theorem explicitly inhabits the
  relevant behavioral relation.
- Approximate closeness is an error-budget relation, not an equivalence
  relation. Exact algebraic simulation does not itself supply a metric. Goal 2
  Stage 10 supplies a separate semantic metric layer, but no finite encoder,
  rounding algorithm, accumulated circuit-error theorem, approximate compiler,
  or runtime result.

## Frozen historical family seed

Abbreviations in the owner column are Goal 2 (`G2`) and Goal 3 (`G3`) stages.
“Existing” in a disposition means only that representative Goal 1 declarations
existed at discovery time; it does not describe the final Stage 11 state.
Each owner cell has exactly one primary owner: the leftmost stage. Any later
comma- or semicolon-separated stages are consumers or downstream extensions,
not co-owners. The JSON records these separately as `primaryOwner` and
`consumerStages` so uniqueness does not depend on prose interpretation.

| ID | Evidence / representative declarations | Space | Subject | Input scope | Observation scope | Phase side | Exactness | Ancilla / marginal policy | Provisional disposition | Primary owner; consumer stages |
|---|---|---|---|---|---|---|---|---|---|---|
| `EQC-001-Q-LEFT-PHASE-FAILURE` | `LeftPhaseEquivalent`, `not_leftPhaseEquivalent_gate_i_input`, `fixed_left_phase_not_natural`; `Corrections.md:90-116` | same | state columns and one evolution | one explicit raw unnormalized pair of weight `2`; the Stage 3A overlay supplies a normalized replacement | ray preservation failure | quaternion left, deliberately rejected | exact counterexample | none | Existing diagnostic; classify as a failed convention, never physical ray equality | G2 `3A-STATEPHASE`, `8B-WITNESSES` |
| `EQC-002-Q-RIGHT-RAY` | `Quaternion.RightPhaseEquivalent`, `rightPhaseEquivalent_equivalence`, `rightPhaseEquivalent_mulVec`; `Architecture.md:111-119` | same | quaternionic state columns | arbitrary compatible columns; normalized wrappers where probabilities are claimed | ray, basis weight, total weight, evolution | quaternion right | exact | none | Historical seed: Goal 2 later proved normalized relation, quotient, observable, and unitary/circuit descent APIs | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-003-C-RIGHT-RAY` | `Complex.RightPhaseEquivalent`, `rightPhaseEquivalent_complex_mulVec`; `Traceability.md:53` | same | complex state columns | arbitrary compatible columns; normalized wrappers | ray, basis weight, total weight, evolution | complex right, equal to left by commutativity | exact | none | Historical seed: Goal 2 later proved normalized relation, quotient, observable, and unitary/circuit descent APIs | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-004-NORMALIZED-BASIS-DIST` | `FiniteDistribution.ofNormalizedState`, `FiniteDistribution.ext`; `Architecture.md:132-136` | same | normalized state and finite distribution | one normalized state or two distributions | full computational-basis distribution | none | exact | none | Existing distribution construction/extensionality; classify independently of state-ray equality | G2 `2-CORE` |
| `EQC-005-EVENT-PUSHFORWARD-CONGRUENCE` | `eventWeight_eq_of_weight_eq`, `pushforward_eq_of_weight_eq`; `Conventions.md:131-136` | same | finite distributions | one pair of pointwise-equal distributions | finite events and deterministic finite postprocessing | none | exact | deterministic map supplies classical marginal/decoder | Existing finite consequence family; not channel or randomized-machine equality | G2 `2-CORE`, `9C-OUTCOMES` |
| `EQC-006-UNITARY-EVOLUTION-NORM` | `star_dotProduct_mulVec_of_mem_unitary`, `*TotalWeight_mulVec`, `*State.evolveUnitary`; `Architecture.md:238-242` | same | matrix action on state | every compatible state under a supplied unitary | norm, total weight, normalization | none | exact | none | Existing forward preservation family; does not include converse norm-preserver classification | G2 `2-CORE`, `8A-ARROWS` |
| `EQC-007-REAL-COLUMNS-REPRESENTATIVE` | `realColumn0`, `realColumn1`, reconstruction, injectivity, `realColumns_orthogonal`, `realColumns_equal_norm`; `goal-1/4-STATES.md:167-182` | cross | complex representative to doubled real representative | arbitrary finite column | amplitudes, reconstruction, norm and inner product | none | exact after encoding | one explicit top sector; no marginal | Existing algebraic state-encoding family; nonbehavioral until connected to an observation relation | G2 `9A-RELATIONS`, `11B-CERTIFICATES` |
| `EQC-008-REAL-COLUMNS-INTERTWINING` | `realifyMatrix_allCoefficient_stateIntertwining`; canonical specializations in `SimulationAudit.matrixStateIntertwining_wrappers_api` | cross | rectangular matrix action and encoded raw column | every raw complex source column and every raw coefficient pair `ℝ × ℝ` | exact evolved amplitudes | none; representatives are exact | `AllTopStateIntertwining` | doubled sum coordinates; no normalized/product-top claim | Stage 9B proof-bearing directional wrapper | G2 `9B-WRAPPERS` |
| `EQC-009-REAL-COLUMNS-MEASUREMENT` | `realTopCombination_allRebit_raw_decodedBasisWeightAgreement` | cross | encoded raw complex column | every raw source column and normalized `Rebit` coefficient | exact decoded computational-basis weights | none | `AllTopDecodedBasisWeightAgreement` | explicit false/true sector sum; no product/mixed-top claim | Stage 9C proof-bearing representative-weight wrapper; raw weights are not called probabilities | G2 `9C-OUTCOMES`; G3 `3-DENSITY` for mixed extension |
| `EQC-010-REAL-REDUCED-OUTER` | `reducedRealOuter_realColumns`, `reducedRealOuter_diagonal`; `Traceability.md:41,84` | cross | rank-one outer matrices | every source pure column; two canonical encodings | reduced matrix and its computational diagonal | none | exact | explicit two-sector diagonal-block sum, not generic partial trace | Existing rank-one equality; generic density/partial trace absent | G2 `11B-CERTIFICATES`; G3 `3-DENSITY` |
| `EQC-011-COMPLEX-COLUMNS-REPRESENTATIVE` | `complexColumn0`, `complexColumn1`, reconstruction, injectivity, `complexColumns_orthogonal`; `goal-1/4-STATES.md:199-212` | cross | quaternionic representative to doubled complex representative | arbitrary finite column | amplitudes, reconstruction, norm and inner product | source quaternion state phase remains right-sided | exact after encoding | one explicit top sector; no marginal | Existing algebraic state-encoding family | G2 `9A-RELATIONS`, `11B-CERTIFICATES` |
| `EQC-012-COMPLEX-COLUMNS-INTERTWINING` | `complexifyMatrix_allCoefficient_stateIntertwining`; canonical specializations in `SimulationAudit.matrixStateIntertwining_wrappers_api` | cross | rectangular matrix action and encoded raw column | every raw quaternionic source column and every raw coefficient pair `ℂ × ℂ` | exact evolved amplitudes | none; no right-phase quotient | `AllTopStateIntertwining` | doubled sum coordinates; no normalized/product-top claim | Stage 9B proof-bearing directional wrapper | G2 `9B-WRAPPERS` |
| `EQC-013-COMPLEX-COLUMNS-MEASUREMENT` | `complexTopCombination_allQubit_raw_decodedBasisWeightAgreement` | cross | encoded raw quaternionic column | every raw source column and normalized `Qubit` coefficient | exact decoded computational-basis weights | none | `AllTopDecodedBasisWeightAgreement` | explicit false/true sector sum; no product/mixed-top claim | Stage 9C proof-bearing representative-weight wrapper; no reduced-density conclusion | G2 `9C-OUTCOMES`; G3 `3-DENSITY` for mixed extension |
| `EQC-014-BASIS-PREPARATION` | `basisPreparationGate_mulVec_ground`, `eval_prepend_basisPreparation_mulVec_ground`; `Corrections.md:583-593` | same | basis state and circuit | one known computational-basis assignment | exact output column | none | exact | no ancilla; full-support XOR gate | Historical seed: Goal 2 later certified the full all-basis-input XOR permutation; no unknown-state or uniform synthesis claim | G2 `5-BASIS`, `11B-CERTIFICATES` |
| `EQC-015-NONPRODUCT-WITNESS` | `encodedState_not_pureTopBottomProduct`; `Architecture.md:269-274` | cross | one encoded pure state | one normalized rational source state | pure factorization obstruction | none | exact negation | explicit added wire; no density marginal | Existing structural witness; not entanglement, channel, or signaling classification | G2 `11-REGISTRY`; G3 `16C-WITNESS` for operational consumers |
| `EQC-016-PRODUCT-ORDER-RAY-WITNESS` | `ground_outputs_not_rightPhaseEquivalent`, `ground_outputs_basis_weights_eq`; `Corrections.md:378-393` | same | two scheduled quaternionic outputs | one normalized pointwise-product ground input | state ray and complete basis-weight family | quaternion state phase right | exact inequality plus exact equality | none | Existing strictness witness: basis weights do not determine quaternionic ray | G2 `8B-WITNESSES` |
| `EQC-017-REALIFY-ALGEBRA` | `realify_mul`, `realify_conjTranspose`, `realify_injective`; `goal-1/3-MATRICES.md:126-144` | cross | matrix embedding | arbitrary compatible matrices | full matrix entries and algebraic operations | none | exact mapped algebra | doubled sum indices | Existing algebraic identity family; classify as nonbehavioral support | G2 `11-REGISTRY` |
| `EQC-018-COMPLEXIFY-ALGEBRA` | `complexify_mul`, `complexify_conjTranspose`, `complexify_injective`; `goal-1/3-MATRICES.md:146-165` | cross | matrix embedding | arbitrary compatible quaternionic matrices | full matrix entries and algebraic operations | multiplication order explicit | exact mapped algebra | doubled sum indices | Existing algebraic identity family; classify as nonbehavioral support | G2 `11-REGISTRY` |
| `EQC-019-DIRECT-REALIFY-REINDEX` | `directRealify_exactOperatorEmbedding`; `directRealify_eq_reindex` | cross | two rectangular matrix representations | every quaternionic matrix | full target matrix after named row/column reindexing | none | exact `ExactOperatorEmbedding` after reindex | four sectors ordered `[Re,ImI,ImK,ImJ]`; no circuit translator | Stage 9B proof-bearing reindexing wrapper; not unreindexed or circuit equality | G2 `9B-WRAPPERS`, `11-REGISTRY` |
| `EQC-020-UNITARY-IMAGE-EQUIVS` | `realifyUnitaryEquivImage`, `complexifyUnitaryEquivImage`, `directRealifyUnitaryEquivImage`; `ReleaseReport.md:45-56` | cross | unitary groups and homomorphism ranges | every unitary matrix in source group | algebraic multiplication and image membership | none | exact algebraic equivalence onto range | changed scalar/dimension; no state decoder | Existing `MulEquiv`-onto-image family; explicitly nonbehavioral | G2 `11-REGISTRY` |
| `EQC-021-DETERMINANT-IMAGE` | `realify_det`, `realify_mem_specialOrthogonal`, quaternion determinant alternatives, `directRealify_mem_specialOrthogonal`; `Architecture.md:319-336` | cross | matrix/group image | every source matrix or unitary under stated hypotheses | determinant and target group membership | none | exact | changed scalar/dimension | Existing algebraic group facts; quaternion-to-complex positive sign remains outside this completed family | G2 `11-REGISTRY`; G3 `5-DETERMINANT` |
| `EQC-022-PROPER-IMAGE-WITNESSES` | `realWitness_specialOrthogonal_not_realify`, `complexWitness_specialUnitary_not_complexify`, `directWitness_specialOrthogonal_not_directRealify`; `Traceability.md:141` | cross | target matrix versus embedding image | explicit low-dimensional matrices | nonmembership in algebraic image | none | exact counterexamples | no encoder/decoder or operational observation | Existing proper-image diagnostics; no operational lower bound | G2 `11-REGISTRY` |
| `EQC-023-KRONECKER-INTERCHANGE` | `kronecker_mul_kronecker_of_entrywiseCommute`, success/failure examples; `goal-1/7-ORDERING.md:151-162` | same | matrix products | arbitrary compatible matrices under explicit crossing commutation; explicit examples | full matrix equality or inequality | none | exact | tensor-factor indices only | Existing algebraic condition and witnesses; no necessity theorem | G2 `11-REGISTRY`, `8B-WITNESSES` |
| `EQC-024-PLACE-ALGEBRA` | `place_mul`, `place_conjTranspose`, `place_injective`, `place_mem_unitary`; `goal-1/5-CIRCUITS.md:146-159` | cross | local versus contextual matrix | every local matrix and explicit split/support | full contextual operator | none | exact after reindex/padding | semantic complement; no physical swaps | Existing placement algebra; nonbehavioral support until consumed by a circuit comparison | G2 `11-REGISTRY` |
| `EQC-025-WIRE-EMBED-PLACEMENT` | `realifyPlacedGate_exactOperatorEmbedding`, `complexifyPlacedGate_exactOperatorEmbedding` | cross | placed source gate and translated placed gate | every placed gate on a finite wire type | exact mapped full denotation | none | exact `ExactOperatorEmbedding` | one explicit `AddedWire`; no prepared/product ancilla | Stage 9B proof-bearing denotation wrappers; support/resources remain separate | G2 `9B-WRAPPERS` |
| `EQC-026-ORDERED-EVAL` | `OrderedCircuit.eval`, `eval_cons`, `eval_append`; `Traceability.md:30,72` | same | ordered circuits | every chronological list | exact operator denotation | none | exact | none | Historical seed: Goal 2 later proved the evaluator-backed `ExactCircuitEq` characterization and append congruence | G2 `2-CORE`, `11B-CERTIFICATES` |
| `EQC-027-SCHEDULE-INDEPENDENCE` | `LegalSchedule.scheduledEval_eq_of_pairwise_commute`; `Architecture.md:199-206` | same | two legal schedules of one occurrence family | all supplied schedules under pairwise-commuting global denotations | exact evaluated operator | none | exact | no schedule selection; same finite occurrence family | Existing sufficient equality theorem; no converse or generic disjoint-support implication | G2 `8A-ARROWS`, `8B-WITNESSES` |
| `EQC-028-ORDER-DISTINCTION-WITNESS` | `scheduled_operators_ne`, `output_basis00_weight_ne`, translated analogues; `goal-1/7-ORDERING.md:174-186` | same and cross translation | two legal schedules | one explicit source input; one basis outcome | operator inequality and selected basis-weight inequality | none | exact counterexample | translated version uses one fixed canonical sector encoding, with no product-state claim | Existing existential witness; not all-input or all-measurement inequivalence | G2 `8B-WITNESSES`, `9B-WRAPPERS` |
| `EQC-029-SCHEDULE-ENUMERATION` | `allChronologicalOrders`, exact length and legality theorems; `Architecture.md:223-228` | same | finite lists/schedules | finite identifier type; empty or general precedence as stated | structural membership/count, not circuit behavior | none | exact | none | Existing combinatorial equalities; classify as nonbehavioral resource/support | G2 `11-REGISTRY` |
| `EQC-030-C2R-OPERATOR` | `realifyCircuit_exactOperatorEmbedding` | cross | source and translated circuit evaluators | every finite ordered complex circuit | full operator after `wireRealify` | none | exact `ExactOperatorEmbedding` | one explicit `AddedWire`; no prepared/product ancilla | Stage 9B proof-bearing operator wrapper; not same-space circuit equality | G2 `9B-WRAPPERS` |
| `EQC-031-C2R-STATE` | `realifyCircuit_allCoefficient_stateIntertwining` | cross | circuit evolution on encoded raw state | every raw source column and every raw coefficient pair `ℝ × ℝ` | exact target amplitude column | none | exact `AllTopStateIntertwining` | one explicit coordinate sector; coefficients are not normalized/product-top certificates | Stage 9B proof-bearing state wrapper; outcomes are separately classified by completed Stage 9C | G2 `9B-WRAPPERS` |
| `EQC-032-C2R-OBSERVABLE` | `realifyCircuit_allRebit_raw_decodedBasisWeightAgreement`, `realifyCircuit_allRebit_decodedDistributionAgreement`, decoded event/pushforward wrappers | cross | raw or normalized circuit output at the named level | raw point weights need no unitarity; distributions/events/pushforwards use locally unitary circuits and normalized sources | decoded point weights, full distribution, finite events, deterministic pushforwards | none | exact decoded agreement at four separate levels | full `AddedWire` target retained until explicit decoder; no product/mixed/partial-trace claim | Stage 9C proof-bearing four-level outcome family | G2 `9C-OUTCOMES`; G3 `3-DENSITY` |
| `EQC-033-Q2C-OPERATOR` | `complexifyCircuit_exactOperatorEmbedding` | cross | source and translated circuit evaluators | every finite ordered quaternionic circuit | full operator after `wireComplexify` | none | exact `ExactOperatorEmbedding` | one explicit `AddedWire`; no prepared/product ancilla | Stage 9B proof-bearing operator wrapper; not same-space circuit equality | G2 `9B-WRAPPERS` |
| `EQC-034-Q2C-STATE` | `complexifyCircuit_allCoefficient_stateIntertwining` | cross | circuit evolution on encoded raw state | every raw source column and every raw coefficient pair `ℂ × ℂ` | exact target amplitude column | none; no right-phase quotient | exact `AllTopStateIntertwining` | one explicit coordinate sector; coefficients are not normalized/product-top certificates | Stage 9B proof-bearing state wrapper; outcomes are separately classified by completed Stage 9C | G2 `9B-WRAPPERS` |
| `EQC-035-Q2C-OBSERVABLE` | `complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`, `complexifyCircuit_allQubit_decodedDistributionAgreement`, decoded event/pushforward wrappers | cross | raw or normalized circuit output at the named level | raw point weights need no unitarity; distributions/events/pushforwards use locally unitary circuits and normalized sources | decoded point weights, full distribution, finite events, deterministic pushforwards | none | exact decoded agreement at four separate levels | full `AddedWire` target retained until explicit decoder; no product/mixed/partial-trace claim | Stage 9C proof-bearing four-level outcome family | G2 `9C-OUTCOMES`; G3 `3-DENSITY` |
| `EQC-036-SCHEDULED-Q2C` | Stage 9B operator/state wrappers plus four `scheduledComplexifyCircuit_*` Stage 9C outcome wrappers | cross | one supplied schedule and translated circuit | raw point weights need only the supplied schedule/gates; normalized levels add pointwise local unitarity and normalized sources | operator/state action, operator-gap preservation, decoded weights/distribution/events/deterministic pushforwards | none | exact per supplied schedule | no schedule choice, quotient, independence, product/mixed-top, channel, or resource claim | Proof-bearing operator/state and outcome slices complete at their distinct scopes | G2 `9B-WRAPPERS`, `9C-OUTCOMES` |
| `EQC-037-Q2R-COMPOSED` | Stage 9B composed wrappers plus four `quaternionToRealCircuit_*` Stage 9C outcome wrappers | cross | quaternionic circuit and composed real translation | raw point weights need no unitarity; normalized levels use locally unitary circuits, normalized sources, and supplied `Qubit × Rebit` coefficients | exact operator/state action and decoded weights/distribution/events/deterministic pushforwards | none | exact mapped/decoded agreement at separate levels | decode outer realification wire then inner complexification wire; no product/mixed/partial-trace claim | Proof-bearing composed family; Equation 63 is not a circuit translator | G2 `9B-WRAPPERS`, `9C-OUTCOMES` |
| `EQC-038-POSTPROCESSING-SIMULATION` | primary, scheduled, and composed decoded-distribution/event/pushforward wrappers | cross | source and full target output distributions | locally unitary circuits, normalized sources, supplied normalized coefficient parameters, and supplied schedule where applicable | full finite distribution, all finite events, deterministic pushforwards | none | exact `DecodedDistributionAgreement` and named consequences | explicit one/two-wire decoder; deterministic map only | Stage 9C proof-bearing observational closure; not randomized postprocessing or channel equality | G2 `9C-OUTCOMES` |
| `EQC-039-EXACT-COMPILER-SEMANTICS` | `ExactGateCompiler.eval_compileCircuit`; `Architecture.md:307-315` | same | source circuit and supplied expansion circuit | every circuit under a supplied exact compiler certificate | exact evaluated operator | none | exact | compiler is ancilla-free on same wires unless separately stated | Existing conditional semantic preservation; no compiler existence | G2 `11-REGISTRY`; G3 `10-SYNTHESIS` for construction |
| `EQC-040-COMPILED-IMAGE-SEMANTICS` | `compileRealifyCircuit_exactOperatorEmbedding`, `compileComplexifyCircuit_exactOperatorEmbedding` | cross then same-target compilation | source evaluator and supplied compiler output | every source circuit under explicit `ExactGateCompiler` data | same embedded operator after compilation | none | conditional exact `ExactOperatorEmbedding` | same translated target wires; no compiler-created ancilla claim | Stage 9B proof-bearing conditional wrappers; no compiler existence, synthesis, approximation, count, or runtime | G2 `9B-WRAPPERS`, `11-REGISTRY` |
| `EQC-041-STRUCTURAL-RESOURCE-EQUALITIES` | gate count, width, arity, depth, dense-slot, and schedule-count theorems; `Architecture.md:283-315` | same and cross structural | finite circuit/resource certificates | every circuit under each theorem's nonempty/common-wire/bound premise | counts and bounds only | none | exact equality or stated inequality | shared-wire policy explicit; no observable decoder | Existing nonbehavioral resource family; JSON must split heterogeneous declaration arrays | G2 `11-REGISTRY` |
| `EQC-042-EXACT-VS-APPROX-BOUNDARY` | three `*exactSimulation` families, `ExactGateCompiler.eval_compileCircuit`, and the six `Semantics/Approximation` leaves; C-024 | same-space and directional mapped semantic boundary | exact mathematical operators, normalized pure-state representatives, and finite distributions | every finite matrix/normalized state/distribution at the named scalar and phase scope; no encoded circuit family | Euclidean L2 operator and output-column error, right-ray error, half-L1 distribution error, finite events, and deterministic pushforwards | real/complex one global phase, quaternion operator central sign only, and complex/quaternion state phase on the right | nonnegative error budgets with zero iff the corresponding exact relation; composition adds budgets | mapped comparisons retain the explicit map; no hidden ancilla, encoding, rounding, or marginal | Stage 10 proof-bearing metric boundary with exact nontransitivity witnesses; finite encoding, circuit-error accumulation, approximate compilation/synthesis, and runtime remain Goal 3 | G2 `10-APPROX`; G3 `9-APPROX` for encoded finite precision |
| `EQC-043-REAL-SIGN-RAY` | Paper Equations 5-6, `fernandez-2003.md:101-114`; `Traceability.md:27` | source only | normalized real state rays | every normalized real state representative | ray equality modulo sign | real right/left sign, central | exact relation requested, quotient absent | none | Historical seed: Goal 2 later proved normalized sign equivalence, `RealRay` equality, observables, and evolution descent | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-044-BASIS-CLASSICAL-BEHAVIOR` | Paper `fernandez-2003.md:40-48,119-128,395-407,812`; basis-preparation declarations are only one consumer | same and cross | certified computational-basis action | every basis input for a certified basis-classical operator | induced classical basis permutation, deliberately forgetting general quantum action | input-column phase may be forgotten only under certificate | exact behavior relation unimplemented | top-labelled target basis for the embedding examples | Historical seed: Goal 2 later implemented certified `SameBasisBehavior`; the raw transition biconditional remains rejected | G2 `5-BASIS` |
| `EQC-045-NORM-PRESERVER-CONVERSES` | Paper `fernandez-2003.md:50,69,818,1288`; `Traceability.md:55,60` | source only | linear maps and unitary/orthogonal classes | every finite linear map under scalar/linearity hypotheses | preservation of full norm/inner product | none | exact classification requested | none | Background converse family absent or partial; antiunitary and scalar assumptions must remain explicit | G3 `4-FOUNDATIONS` |
| `EQC-046-MIXED-TOP-OBSERVATIONAL` | Paper `fernandez-2003.md:661,1075`; `Traceability.md:85,112` | source only cross | mixed product top state and encoded bottom system | every product/no-correlation mixed top density and source density or pure state under a future explicit joint-state model | decoded bottom basis distribution | none | exact claim unimplemented | actual product-density hypothesis and added-subsystem partial trace required; entangled inputs excluded | Source mixed-state extension; current `Rebit`/`Qubit` coefficient results do not implement it | G3 `3-DENSITY` |
| `EQC-047-QUATERNION-REDUCED-SEPARATION` | Paper Lemma 10 and explicit contrast, `fernandez-2003.md:1077-1083,1136-1171` | source only cross | two complex reduced density matrices from quaternionic encodings | every source quaternionic pure state | reduced matrices may differ while computational diagonals agree | none | exact equality/inequality boundary unimplemented as density API | trace added top qubit | Source separation family; current library proves direct weights only | G3 `3-DENSITY` |
| `EQC-048-COMPUTATIONAL-MODEL-EQUIVALENCE` | Paper `fernandez-2003.md:18-22,146-169,1239-1241,1291`; traceability algorithm/universality rows | source only | encoded circuit/QTM/algorithm families | every encoded input and uniformly generated family | acceptance/output distribution and complexity class | phase irrelevant unless approximation quotient chosen | exact or approximate as source theorem specifies; no implementation | model-specific input/output ancillas and postprocessing must be costed | Source computational-power family; finite per-circuit simulation is insufficient | G3 `12-UNIFORMITY`, `13-REALQTM` |
| `EQC-049-PHYSICAL-SWAP-SIMULATION` | Paper `fernandez-2003.md:57,359,1289`; `Traceability.md:57,74,83` | source only same model | noncontiguous semantic gate versus emitted contiguous/swap circuit | every finite support under a declared architecture | exact operator/circuit behavior plus routing resource cost | none | exact semantic equivalence requested; construction absent | physical swap gates and any routing ancillas must be emitted/countable | Source routing comparison; Goal 1 provides semantic reindexing only | G3 `6-ROUTING` |
| `EQC-050-TOP-WIRE-PHASE-TRACKING` | Paper `fernandez-2003.md:683-687,1202,1293`; `Traceability.md:92,134` | source only cross | encoded invariant sectors and added top wire | arbitrary source states; pure versus maximally mixed top distinguished | structural phase/orbit evolution, not merely final basis probabilities | complex/quaternion state phase convention-sensitive | heuristic claim; exact replacement not yet selected | one added top wire; mixed-top phase-kickback exception | Source interpretive family requiring invariant-subspace/orbit formulation | G3 `14-STRUCTURE` |
| `EQC-051-OPERATIONAL-CONVERSE-SIMULATION` | Paper `fernandez-2003.md:1251`; algebraic witnesses in `Traceability.md:141` | source only | target circuit/model versus smaller source model | all target circuits only after a simulation relation and allowed encoders are fixed | ray, basis measurement, channel, or computational behavior must be chosen explicitly | model-specific | source inference unsupported; only algebraic nonimage is implemented | allowed ancillas/decoders unspecified in source | Source operational converse family; matrix non-surjectivity alone is insufficient | G3 `14-STRUCTURE`, `16-CHANNELS` |

## Stage 2 proof-bearing realization

The frozen row IDs and membership above remain unchanged as inventory data;
their human-readable wording may incorporate checked errata. The following
Goal 2 Stage 2 results are checked classifications rather than provisional
names.

| Frozen row | Strongest checked classification | Proof-bearing API | Excluded upgrade |
|---|---|---|---|
| `EQC-004-NORMALIZED-BASIS-DIST` | Pointwise computational-basis weights of two normalized states are equivalent to equality of their packaged finite distributions. | `BasisWeightEq`, `NormalizedDistributionEq`, `basisWeightEq_iff_normalizedDistributionEq` | No vector, ray, all-pure-input, or channel equality follows. |
| `EQC-005-EVENT-PUSHFORWARD-CONGRUENCE` | Pointwise normalized-state weight equality implies equality of every finite event and every deterministic finite pushforward, including each pushed-forward weight. | `BasisWeightEq.eventWeight_eq`, `BasisWeightEq.pushforward_eq`, `BasisWeightEq.pushforward_weight_eq` | This is finite classical outcome closure, not a quantum partial trace, randomized postprocessor, or channel theorem. |
| `EQC-006-UNITARY-EVOLUTION-NORM` | The existing unitary evolution family is normalization-preserving support: it preserves total weight and constructs normalized output states. It is not an equivalence between the input and output basis distributions, which a unitary may change. | `star_dotProduct_mulVec_of_mem_unitary`, `complexTotalWeight_mulVec_of_mem_unitary`, `quaternionTotalWeight_mulVec_of_mem_unitary`, and the three `evolveUnitary` constructors | No `BasisWeightEq`, `BasisMeasurementEq`, or outcome-distribution equality between a state and its evolved state is claimed. |
| `EQC-026-ORDERED-EVAL` | Two ordered circuits are exactly equal precisely when their chronological evaluators are literally equal. Gatewise denotation equality and append preserve this relation. | `ExactCircuitEq`, `ExactCircuitEq.iff_eval_eq`, `ExactCircuitEq.of_gatewise`, `ExactCircuitEq.append` | Gate-list equality is sufficient but unnecessary; resources, phase, schedule certificates, and cross-model embeddings are outside the relation. |

Stage 2 also exports `OutputWeightEqAt`, `BasisMeasurementEq`, and
`PureInputBasisMeasurementEq` with distinct one-input, all-basis-input, and
all-normalized-pure-input quantifiers. The implication from the last to the
second requires explicit normalization of every basis ket for the supplied
weight function. Exact operator and circuit equality imply all three, but no
converse is published at this stage.

## Immutable cohort erratum: `EQC-001`

The frozen `Goal1ComparisonCohort` JSON and its SHA-256 sidecar preserve the
Stage 1 discovery boundary byte-for-byte. Its `EQC-001.classification.inputScope`
field says `one explicit normalized two-coordinate input pair`. That field is
factually wrong: `Quaternion.phaseWitnessInput = (1,1)` has quaternionic total
weight exactly `2`, proved by
`StatePhaseAudit.phaseWitnessInput_totalWeight`. The original no-go theorem is
still a valid raw-column counterexample, so the family membership and its
declarations remain correct.

The JSON is intentionally not rewritten because doing so would destroy the
immutable pre-retrofit checksum. The corrected human rendering appears in the
seed table above, and Stage 3A supplies a separate normalized `(3/5,4/5)` pair,
its left-`i` mate, and both evolved outputs as actual `QuaternionState Bool`
values. Stage 11's final classifier must apply this explicit erratum and the
proof-bearing overlay rather than treating the frozen prose field as final
semantic authority.

## Stage 3A proof-bearing realization

At Stage 3A these were relations only on normalized representatives; quotient
values and descended operations were still deferred to Stage 4.

| Frozen row | Strongest checked Stage 3A classification | Proof-bearing API | Excluded upgrade |
|---|---|---|---|
| `EQC-001-Q-LEFT-PHASE-FAILURE` | Same-space exact rejection certificate: a normalized Bool-indexed pair related by unit left `i` phase is separated by the norm-preserving `diag(1,j)` endomap. | `StatePhaseAudit.normalizedWitness_all_totalWeights`, `normalized_leftPhaseEquivalent_i_input`, `normalized_not_leftPhaseEquivalent_gate_i_input` | Not failure of right phase, not a universal restricted-operator theorem, and not circuit/channel inequivalence. |
| `EQC-002-Q-RIGHT-RAY` | Exact same-space unit-right-phase equivalence on normalized quaternionic representatives for arbitrary finite index types; preserved by basis distributions, raw matrices/circuits, and normalized unitary evolution. | `QuaternionStatePhaseEq` and its `equivalence`, `of_exact`, `basisWeightEq`, `normalizedDistributionEq`, `raw_mulVec`, `raw_eval`, and `evolveUnitary` theorems | Not quotient equality, arbitrary quaternion operator phase, channel equality, or a converse from basis distributions. |
| `EQC-003-C-RIGHT-RAY` | Exact same-space unit-phase equivalence on normalized complex representatives, written on the right and central by commutativity, with the same distribution and evolution guarantees. | `ComplexStatePhaseEq` and its corresponding theorem family | Not quotient or channel equality; no converse from basis distributions. |
| `EQC-043-REAL-SIGN-RAY` | Exact same-space sign equivalence on normalized real representatives. The unit condition is exactly `s=1 ∨ s=-1`, and the raw relation is exactly equality or pointwise negation. | `Real.SignEquivalent`, `sign_sq_eq_one_iff`, `signEquivalent_iff_eq_or_eq_neg`, and `RealStatePhaseEq` with its distribution and evolution theorem family | Not quotient equality, not realification of arbitrary complex phase, and no distribution converse. |

`ExactStateEq` separately names literal equality of normalized representatives
and implies each scalar-specific phase relation. No Stage 3A result upgrades
`FER03-D01-REBIT` or `FER03-FND-COMPLEX-STATE-RAY` to a completed quotient
result.

## Stage 3B proof-bearing realization

Stage 3B introduced the same-space real and complex operator/circuit phase
vocabulary. Stage 12 later completed its generic projective kernel; the table
below gives the final checked meaning. Neither stage enlarges the frozen Goal 1
cohort. Every new stable declaration is instead recorded in the separate Goal
2 semantic API manifest.

| Relation family | Checked meaning | Valid checked consequences | Deliberately excluded upgrade |
|---|---|---|---|
| `RealGlobalSignEq` / `ComplexGlobalPhaseEq` | `V = η • U` for one matrix-wide unit sign/phase | Equivalent to raw and normalized projective action; implies input-column phase, output-row phase, and simultaneous unitary membership | Not literal equality, channel equality for arbitrary rectangular matrices, or cross-model equality |
| `RealInputBasisSignEq` / `ComplexInputBasisPhaseEq` | One right phase per computational-basis input column | `BasisMeasurementEq`; preservation by a common later operator/circuit | Not all-pure-input agreement or projective action |
| `RealOutputBasisSignEq` / `ComplexOutputBasisPhaseEq` | One left phase per output row | `BasisMeasurementEq`, `PureInputBasisMeasurementEq`, and preservation by a common earlier operator/circuit | Not projective action or channel equality |
| `RealProjectiveActionEq` / `ComplexProjectiveActionEq` | Output rays agree for every normalized pure input | Equivalent to raw projective action and one global sign/phase; hence input-column phase, `PureInputBasisMeasurementEq`, and output-row phase | No output-normalization claim and no channel theorem for arbitrary rectangular matrices |
| Eight `*Circuit*Eq` wrappers | The corresponding relation on `OrderedCircuit.eval` | Equivalence laws, exact-to-global lifts, and chronology-correct congruences | No gate-list, resource, schedule, embedding, or compiler equality |

The final checked shape is therefore not one total chain:

```text
ExactOperatorEq
       |
       v
real/complex global phase <-> raw projective <-> normalized projective
                                      /                 \
                                     v                   v
                              input phase   PureInputBasisMeasurementEq
                                     \                   <-> output phase
                                      v                         v
                                        BasisMeasurementEq
```

`OperatorPhase.ComplexRealAudit.real_unitary_strictness` and
`complex_unitary_strictness` use the unitary rotation
`[[3/5,4/5],[-4/5,3/5]]`. They prove exact equality is strictly stronger than
global phase; global phase/projective action is strictly stronger than either
basis-sided phase; input and output phase are incomparable; input phase can
change a superposed-input basis distribution; and output phase can preserve
every pure-input basis distribution while failing projective action. The
zero-wire `-1` and `I` circuit witnesses separately prove nontrivial circuit
global phase without exact circuit equality.

Projective action is meaningful without assuming the operator preserves
normalization. On an empty input type the normalized quantifier is vacuous,
but the raw relation is true on the unique zero input and every matrix has no
columns; both therefore agree with global sign/phase. An empty output type and
rank-one matrices are covered without special hypotheses as well. Only the
later channel characterization needs an inhabited square space and unitarity.
Circuit projective action is nonvacuous because `BitBasis W` is inhabited and
admits normalized basis states even for zero wires. Stage 3C supplies the
separate noncommutative classification below.

## Stage 3C proof-bearing realization

Stage 3C adds a same-space quaternionic operator/circuit layer without
changing the frozen Goal 1 cohort. It keeps multiplication side, input scope,
and the dimension-sensitive kernel explicit.

| Relation family | Checked meaning | Valid checked consequences | Deliberately excluded upgrade |
|---|---|---|---|
| `QuaternionCentralSignEq` | `V = s • U` for one real scalar with `s*s=1`; this is central `±1`, not arbitrary unit-quaternion phase | Input-right phase, output-left phase, raw and normalized projective action, and simultaneous unitary membership | Not literal equality, arbitrary quaternionic global phase, channel equality, or cross-model equality |
| `QuaternionInputRightPhaseEq` | One unit quaternion multiplies each input column on the right | `BasisMeasurementEq`; preservation by a common later operator/circuit | Not output-left phase, all-pure-input agreement, projective action, or channel equality |
| `QuaternionOutputLeftPhaseEq` | One unit quaternion multiplies each output row on the left | `BasisMeasurementEq`, `PureInputBasisMeasurementEq`, and preservation by a common earlier operator/circuit | Not input-right phase, projective action, or channel equality |
| `QuaternionRawProjectiveActionEq` | Raw output columns lie on the same right ray for every raw input column | Input-right phase; equivalent to normalized projective action for every finite input type; arbitrary compatible common evolution on either side | No output-normalization or channel claim |
| `QuaternionProjectiveActionEq` | Raw output columns lie on the same right ray for every normalized pure input | Input-right phase, `PureInputBasisMeasurementEq`, and hence output-left phase; common-later preservation; common-earlier preservation under unitarity | No output-normalization, channel, or all-effect theorem |
| Four `QuaternionCircuit*Eq` wrappers | Central sign, input-right phase, output-left phase, or normalized projective action on `OrderedCircuit.eval` | Equivalence laws, exact-to-central-sign lift, and chronology-correct congruences | No raw-projective wrapper and no gate-list, resource, schedule, embedding, or compiler equality |

The checked forward shape is:

```text
ExactOperatorEq
       |
       v
QuaternionCentralSignEq
              |
              v
 raw projective <-> normalized projective
          /                   \
         v                     v
  input-right      PureInputBasisMeasurementEq <-> output-left
         \                     /
          v                   v
             BasisMeasurementEq
```

The raw/normalized bridge needs only a finite input type. If that type is
empty, the normalized quantifier is vacuous while the raw relation sees only
the unique zero column and is trivially true. In contrast,
`QuaternionCircuitProjectiveActionEq` quantifies over `BitBasis W`, which is
always inhabited and admits normalized basis states even when `W` is empty.

The kernel converse is deliberately isolated in
`OperatorPhase/QuaternionKernel.lean`. For square matrices, explicit
`1 < Fintype.card I`, `[DecidableEq I]`, and only
`U ∈ unitary (Matrix I I ℍ[ℝ])`, both raw and normalized projective
action are equivalent to `QuaternionCentralSignEq U V`; `V` need not be
assumed unitary. The dimension premise is sharp. For `Matrix Unit Unit ℍ[ℝ]`,
projective triviality of `quaternionRankOneScalar q` is equivalent to
`Quaternion.normSq q = 1` and to its unitarity. The checked `q = j` instance is
unitary and projectively trivial but not central-sign equivalent.

`QuaternionAudit.lean` is non-root and consumes all three original public
leaves. Its
order-sensitive composition checks, generic bridge consumer, dimension-two
kernel consumer, rank-one family, and `j` witness are diagnostics rather than
additional public semantics. The generic public bridge proof, not a separate
audit specialization, covers the empty-input zero-column boundary. The later
`ProjectiveInputAudit.lean` supplies explicit all-ones column/row twists:
input-right and output-left phase are incomparable, and neither one-sided
relation implies projective action, while the new public arrows prove the
reverse projective-to-input implication. Stage 3C
adds no channel or all-measurement relation; those remain owned by later Goal
2 stages.

## Stage 4A proof-bearing realization

Stage 4A turns the three normalized representative relations into literal
quotient equality without changing the frozen Goal 1 cohort.

| Quotient family | Checked equality | Available interface | Still excluded |
|---|---|---|---|
| `RealRay I` | `RealRay.mk a = RealRay.mk b` iff `Real.SignEquivalent a b`, equivalently literal column equality or pointwise negation | `mk`, `exists_rep`, `inductionOn`, invariant `lift`, `lift_mk`, and `function_ext` | No canonical representative, descended evolution/outcomes, or complex-to-real target-ray map |
| `ComplexRay I` | Constructor equality iff `Complex.RightPhaseEquivalent` with one unit complex phase on the right | The same representative-existence, induction, lift, and extensionality interface | Not equality of representatives, basis distributions, channels, or canonical real encodings |
| `QuaternionRay I` | Constructor equality iff `Quaternion.RightPhaseEquivalent` with one unit quaternion strictly on the right | The same representative-existence, induction, lift, and extensionality interface | No left-phase quotient, arbitrary operator phase, channel conclusion, or canonical complex encoding |

`RebitRay`, `QubitRay`, and `QuaterbitRay` are the `Bool`-indexed aliases. The
boundary at dimension zero is exact rather than hidden by an instance:
`realRay_nonempty_iff`, `complexRay_nonempty_iff`, and
`quaternionRay_nonempty_iff` identify ray inhabitation with index inhabitation,
and the three explicit `IsEmpty` instances rule out normalized rays on
`Empty`.

This milestone implements quotient equality only. It does not yet descend
unitary/circuit evolution, basis distributions, finite events, or deterministic
pushforwards, and it does not settle how embedding phases act on the doubled
target columns. Consequently `FER03-D01-REBIT` and
`FER03-FND-COMPLEX-STATE-RAY` remain partially formalized until Stages 4B and
4C complete their required consumers and boundary theorems.

## Stage 4B proof-bearing realization

Stage 4B discharges the descent half of that historical Stage 4A boundary for
all three scalar systems. It adds no new family row to the frozen Goal 1
cohort.

| Descended family | Checked meaning | Exact laws | Deliberately excluded upgrade |
|---|---|---|---|
| `RealRay.distribution` / `ComplexRay.distribution` / `QuaternionRay.distribution` | The normalized computational-basis distribution is independent of the chosen normalized representative | `distribution_mk`, pointwise `basisWeight_mk`, and `distribution_weight` for each scalar | Distribution equality is not used as ray equality and does not imply a channel or arbitrary-effect theorem |
| ray `eventWeight` and `pushforward` | Every finite basis event and every deterministic map to another finite outcome type acts on the descended distribution | Representative computation; pushforward by `id`; first `f`, then `g`, equals pushforward by `g ∘ f` | No randomized postprocessor, encoding, runtime, or approximation claim |
| ray `evolveUnitary` | A supplied unitary square matrix sends a normalized ray to a normalized ray | Representative computation; identity action; first `U`, then `V`, is exactly `V * U` | No action of arbitrary matrices and no claim about channels or all effects |
| ray `evolveCircuit` | An explicitly locally-unitary chronological circuit acts through its unitary evaluator | Representative computation; empty circuit identity; `C ++ D` acts first by `C`, then by `D` | No action of an uncertified circuit, no resource conclusion, and no schedule independence |
| `RealStatePhaseEq.iff_realRay_mk_eq` and complex/quaternion analogues | The normalized representative phase predicates are exactly quotient-constructor equality | One bridge for each scalar, with quaternion phase strictly on the right | Not representative equality, operator global phase, or cross-model equality |

The matrix action requires `[Fintype I]`, `[DecidableEq I]`, and a supplied
unitarity proof. Circuit action requires `[Fintype W]` and a supplied
`IsLocallyUnitary` proof. `BitBasis Empty` has one basis assignment, so the
zero-wire circuit laws are nonvacuous even though `RealRay Empty`,
`ComplexRay Empty`, and `QuaternionRay Empty` themselves are empty. The
descent API does not select representatives and proof arguments do not become
physical data.

Stage 4B does not assert arbitrary-matrix ray evolution, density/effect/channel
semantics, or that either canonical embedding column descends to an ordinary
target-ray map. Therefore `FER03-D01-REBIT` and
`FER03-FND-COMPLEX-STATE-RAY` remain **partially formalized** and are not
`closedByGoal2`; only the Stage 4C embedding-orbit boundary remains for those
transferred rows.

## Stage 4C proof-bearing realization

Stage 4C closes that historical boundary without collapsing cross-space
representation, ordinary real-ray equality, and decoded observation equality.
Its 84 stable declarations are split `66 + 10 + 8` across the orbit core,
bottom-observable descent, and exact ordinary-real-ray boundary.

| Family | Checked meaning | Valid checked consequences | Deliberately excluded upgrade |
|---|---|---|---|
| `RealSectorPhaseEquivalent` / `RealSectorOrbit` | Two normalized doubled-real representatives differ by one common unit-complex sector action `(x,y) ↦ (re(η)x+im(η)y,-im(η)x+re(η)y)` | Independently proved equivalence laws; exact decoder characterization by `Complex.RightPhaseEquivalent`; standard quotient interface | Not `Real.SignEquivalent`, ordinary `RealRay`, operator/circuit equality, or channel equality |
| `complexRayEquivRealSectorOrbit` | `ComplexRay I` is canonically equivalent to the correctly quotiented doubled-real representation space | Both canonical columns and every normalized pure `realTopState` give the same orbit; encoder is injective and bijective | A representation equivalence, not a claim that representative columns are equal or that complex and real computational models are identical |
| `RealSectorOrbit.bottomDistribution` | Sum the two target-sector weights over each source basis index | Equals `ComplexRay.distribution` under `ComplexRay.realificationOrbit`, hence existing finite-event and deterministic-pushforward consequences apply | The full doubled-real basis distribution does not descend and no density/all-effect/channel conclusion follows |
| canonical-column `RealRay` boundary | For either column, applying unit phase `eta` preserves its ordinary target real ray iff `eta = 1 ∨ eta = -1` | Phase `I` gives an explicit source-ray equality/target-real-ray inequality; a representative-compatible column lift exists iff `IsEmpty I` | Not a claim that no arbitrary function exists between the quotient types; the obstruction concerns the canonical representative equation |

This realizes correction C-027. The paper defines physical values as rays
before later applying `h₀` and `h₁` to representative vectors. Those maps
remain injective and continue to intertwine matrices exactly, but neither is a
well-defined map into ordinary `RealRay` on a nonempty source space. The
correct phase-invariant codomain is `RealSectorOrbit`, while decoded bottom
outcomes remain invariant. With Stage 4A quotient equality and Stage 4B
operation descent already present, `FER03-D01-REBIT` and
`FER03-FND-COMPLEX-STATE-RAY` are now **proved as stated** and recorded
`closedByGoal2`. This does not close mixed-top, phase-kickback, density,
channel, or all-effect claims.

## Stage 5 proof-bearing realization

Stage 5 replaces the paper-facing idea of “same classical basis action” with
an explicit, nonvacuous certificate. It updates the proof-bearing
classifications of frozen rows `EQC-014` and `EQC-044` without changing the
frozen Goal 1 cohort.

| Frozen row | Strongest checked Stage 5 classification | Proof-bearing API | Deliberately excluded upgrade |
|---|---|---|---|
| `EQC-014-BASIS-PREPARATION` | For every finite wire type and known basis assignment `b`, the existing permutation matrix, full-support gate, and singleton circuit implement the all-input permutation `x ↦ x XOR b`; the matrix and circuit are unitary through their actual certificates. The original ground-column and prepended-circuit statements remain one-known-input consequences. | `basisPreparationMatrixImplementation`, `basisPreparationOperator`, `basisPreparationGateImplementation`, `basisPreparationCircuit`, `basisPreparationCircuit_basisTransition`, `basisPreparationCircuit_eval_entry`, `basisPreparationCircuit_mulVec_ground` | No unknown-state preparation, primitive synthesis, uniform compiler, runtime, or arbitrary-input-state reduction is claimed. |
| `EQC-044-BASIS-CLASSICAL-BEHAVIOR` | A matrix has certified classical reversible behavior only after supplying an explicit `Equiv.Perm I` and an all-input proof that each column is a unit-phased basis ket at the permuted output. `SameBasisBehavior` compares two such certificates by equality of the certified permutations. On the certified real, complex, and quaternionic classes it is equivalent to the appropriate input phase, output phase, and `BasisMeasurementEq`; evaluator-backed circuit wrappers state the same facts through `OrderedCircuit.eval`. | `BasisPermutationImplementation`, `BasisClassicalUnitaryOperator`, `SameBasisBehavior`, the nine `sameBasisBehavior_iff_*` theorems, `BasisClassicalCircuit`, `SameCircuitBasisBehavior`, and its nine scalar iff wrappers | No relation on arbitrary matrices, no inference from a raw transition biconditional, and no generic exact, global-phase, projective, channel, or all-effect equality. Quaternionic input phases remain on the right and output phases on the left. |

`BasisTransition` and `BasisTransitionRelationEq` remain useful diagnostics, but
they are deliberately not the certified behavior relation. The non-root audit
uses the exact real rotations
`[[3/5,4/5],[-4/5,3/5]]` and
`[[5/13,12/13],[-12/13,5/13]]`. Both matrices are unitary and every entry is
nonzero, yet neither has any phased basis transition or certified permutation.
Their empty raw transition relations are equal while their
`false → false` basis weights differ. Thus the unrestricted transition
biconditional is vacuous even on physically relevant unitary examples.

Exact operator/circuit equality and real/complex global phase or quaternionic
central sign preserve certified behavior when certificates are supplied. The
converses are not asserted. Equal certified permutations may use different
input-dependent phases, so Stage 5 does not infer one global phase, general
projective action, a channel, or equality under all physical effects.

## Stage 6 proof-bearing realization

Stage 6 adds the physical state/effect foundation for later channel
classification. It does not add another circuit-equivalence relation and does
not alter the frozen Goal 1 cohort. The core is theorem-generic over
`RCLike 𝕜`, with explicit real and complex density/effect aliases; it is
not a quaternionic positivity model.

| Compared objects | Exact checked statement | Proof-bearing API | Deliberately excluded upgrade |
|---|---|---|---|
| Two finite densities `ρ` and `σ` on one scalar/index space | Literal bundled density equality is equivalent to equal real Born values for every genuine physical effect `E` on that same space. The reverse direction holds for arbitrary densities, not only pure ones, and uses normalized rank-one projector effects. | `DensityMatrix.eq_iff_forall_effect_bornValue_eq`, `DensityMatrix.eq_of_forall_effect_bornValue_eq`, `posSemidef_eq_of_forall_effect_trace_re_eq`, `Effect.trace_rankOneProjector_mul_eq_inner`, `quadratic_eq_of_unit_sphere` | This fixed-pair extensionality theorem is not `ChannelEq` or `AllMeasurementEq`: it does not compare two operators after acting on every density input. |
| One density `ρ` and one effect `E` | `Effect.bornValue E ρ` is the real part of `trace (E * ρ)` and lies in `[0,1]`; zero, identity, complement, rank-one, pure, and basis formulas are exact. | `Effect.bornScalar`, `Effect.bornValue`, `Effect.bornScalar_im_eq_zero`, `Effect.bornValue_mem_Icc`, `Effect.bornValue_complement`, `Effect.bornValue_basis_pure` | A basis effect is only one physical observation. Basis-effect agreement is not all-effect agreement, ray equality, or channel equality. |
| One unitary `U` and one density `ρ` | Mixed-state evolution is literal conjugation `U * ρ * Uᴴ`; first `U`, then `V`, is conjugation by `V * U`. Pure evolution agrees with ket evolution. | `DensityMatrix.unitaryConjugate`, `unitaryConjugate_comp`, `unitaryConjugate_pure` | The construction of an induced state map does not by itself define equality between two channels or a circuit channel wrapper. |

The empty-index boundary is explicit: `DensityMatrix.nonempty_iff` proves that
a finite density exists exactly when the index type is nonempty. The separation
theorem requires no fake global nonemptiness premise; if the index is empty,
its density arguments cannot exist. Conversely, effects may exist on an empty
index, so no nonvacuous channel claim is extracted from effect quantification
alone.

Stage 6 exports no `ChannelEq`, `AllMeasurementEq`, partial trace, Kraus map,
instrument, quaternionic density/effect positivity, or cross-model mixed-top
simulation. Those omissions are semantic boundaries, not failed converses.
Stage 7 owns the operator/channel quantifiers and the theorem connecting them
through this physical-effect separation result.

## Stage 7 proof-bearing realization

Stage 7 supplies the same-space real/complex unitary-channel classification
without changing the frozen Goal 1 cohort or any paper-row disposition. Stage
12 later strengthens its projective/global row for arbitrary rectangular
matrices. A `UnitaryOperator` bundles the unitary proof required for physical
evolution; the channel relations do not accept arbitrary square matrices.

| Relation or object | Exact checked meaning | Proved equivalences and implications | Deliberately excluded upgrade |
|---|---|---|---|
| `ChannelEq U V` | For every density input `ρ`, the complete outputs `U.evolve ρ` and `V.evolve ρ` are equal as density matrices. | Equivalence relation; exact bundled/matrix equality implies it; chronological composition is congruent. | Not equality only on pure states, basis inputs, diagonal entries, or decoded cross-model outcomes. |
| `AllMeasurementEq U V` | For every density input `ρ` and every genuine `Effect`, all Born values after `U` and `V` agree. | `ChannelEq U V ↔ AllMeasurementEq U V`, with the converse proved through physical-effect separation for each output pair. | The quantifier is not restricted to basis effects and does not range over arbitrary trace-test matrices. |
| `RealRawProjectiveActionEq` / `ComplexRawProjectiveActionEq` | Every raw input column produces outputs on the same correctly sided real-sign/complex-right-phase ray. | For arbitrary rectangular matrices with finite input type, equivalent to normalized projective action and one global sign/phase, including zero, empty, and rank-one cases. | Not a channel relation for arbitrary nonunitary or rectangular matrices. |
| Real/complex global phase on bundled unitaries | `V = η • U` for one matrix-wide real sign or complex unit phase. | Global phase implies `ChannelEq` in every finite dimension. On an inhabited square unitary space, the already unconditional projective/global kernel is additionally equivalent to `ChannelEq` and `AllMeasurementEq`. | Input-column and output-row phase families remain outside this kernel and are not upgraded. No determinant or dimension-at-least-two premise is used. |
| `CircuitChannelEq` / `CircuitAllMeasurementEq` | Apply the corresponding operator relation to `OrderedCircuit.eval` after storing a local-unitarity certificate in `UnitaryCircuit`. | Exact evaluator equality, global phase, projective action, and chronological append lift. The two circuit relations are equivalent and each is an equivalence relation. | No gate-list, schedule, resource, compilation, cross-model, or decoded-marginal equality. |

The arbitrary-rectangular projective kernel is unconditional:

```text
global sign/phase ⇔ raw projective action ⇔ normalized projective action
```

For inhabited real and complex square unitary spaces, the same node is also
equivalent to `ChannelEq` and `AllMeasurementEq`. Only this channel extension
requires `Nonempty I`; no density matrix exists on an empty index, so the two
channel relations are physically vacuous there. The projective/global theorem
itself covers the unique empty square matrices without a separate premise. For
circuits, `BitBasis W = W → Bool` is canonically inhabited even when `W` is
empty, so the evaluator characterizations remain nonvacuous at zero wires.

Stage 7 introduces no quaternionic density/effect/channel theory, arbitrary
trace-test semantics, partial trace, Kraus channel, instrument, cross-model
channel relation, decoded marginal, mixed-top theorem, or capacity claim.
Those omissions are scope boundaries rather than failed converses.

## Stage 8 proof-bearing realization

Stage 8 closed the then-known implication graph without changing the frozen
Goal 1 cohort or a paper-row disposition. Its 49 stable declarations add
covering arrows and finite-observation converses; Stage 12 later supplies the
projective-input and generic projective-kernel completion. The non-root audit
owns the counterexamples and consumes the certified-classical layer.

| Comparison | Strongest checked result | Exact boundary |
|---|---|---|
| Output-row phase versus all-pure basis measurement | For arbitrary rectangular matrices with `[Fintype I]`, `RealOutputBasisSignEq`, `ComplexOutputBasisPhaseEq`, and `QuaternionOutputLeftPhaseEq` are each iff the corresponding `PureInputBasisMeasurementEq`. | No output finiteness, decidable equality, nonempty type, unitarity, or nonzero-row premise. Quaternion phases multiply on the left. This is still basis-output behavior, not projective or channel equality. |
| Finite distributions versus events | Distribution equality is iff equality of every singleton event and iff equality of every finite event. | Empty outcome types admit no finite distribution; the audit proves `IsEmpty` rather than assuming an impossible value. |
| Finite distributions versus deterministic postprocessing | Distribution equality is iff equality of every pushforward to a finite target in the same universe. | The converse uses the identity target. Forward preservation remains universe-polymorphic. No randomized postprocessor or runtime claim is included. |
| Rays versus basis outcomes | Exact representatives imply equal ray constructors, and ray-constructor equality implies basis-weight equality for real, complex, and quaternionic normalized states. | Equal weights, distributions, events, and pushforwards do not imply ray equality. Rational complex and existing quaternionic witnesses prove the failure. |
| Real/complex projective and unitary kernels | On every finite-input rectangular space, raw projective action, normalized projective action, and global sign/phase are equivalent. On inhabited square unitary spaces, that common relation is also equivalent to `ChannelEq` and `AllMeasurementEq`. | The input-column and output-row branches are weaker and incomparable with each other; neither implies projective action. Only the channel extension needs inhabitedness and unitarity. |
| Certified classical behavior | The nine matrix and nine circuit `SameBasisBehavior` iff theorems are consumed unchanged. | Every result requires supplied permutation certificates. Raw basis-transition equivalence remains vacuous on explicit nonmonomial unitaries. |

The checked complex-unitary graph is therefore

```text
ExactOperatorEq
        |
        v
ComplexGlobalPhaseEq <-> RawProjectiveActionEq <-> ProjectiveActionEq
                                                    /       \
                                                   v         v
                                   InputBasisPhaseEq         PureInputBasisMeasurementEq
                                             \               <-> OutputBasisPhaseEq
                                              v                       v
                                               BasisMeasurementEq

On inhabited square unitaries, the top line is also
              <-> ChannelEq <-> AllMeasurementEq
```

The real graph replaces complex phase by a sign. The output-row/all-pure iff
also holds over quaternions with output phases on the left, but Stage 8 draws
no quaternionic channel edge.

Every rejected branch converse in this diagram has checked evidence. Rational
unitary input and output twists prove the two phase branches incomparable,
show that input-column phase can change a superposition's output weights, and show that
output-row/all-pure agreement can fail channel and all-effect equality. They
also give both failures from `BasisMeasurementEq` to a coherent input/output
phase branch. A rational complex coordinate-phase pair and the normalized
quaternionic product-ordering outputs have equal complete distributions but
unequal rays. The scheduled quaternionic example is separately packaged as
`OutputWeightEqAt` on the ground input while another normalized input proves
failure of `PureInputBasisMeasurementEq`; it is not all-input evidence.

For certified basis-permutation implementations only, the existing input,
output, and basis-measurement relations collapse to equality of the certified
permutations. No such equivalence is published for generic unitaries.

## Stage 9A proof-bearing realization

Stage 9A adds a directional cross-model vocabulary and proves the strongest
representative-coordinate results for the four canonical state columns. It did
not change the frozen cohort or by itself finalize the circuit and outcome
families then owned by Stages 9B and 9C. The stable allocation is 58
declarations: 38 generic relations and laws plus 20 concrete encoding
declarations.

| Frozen family or policy | Strongest checked Stage 9A result | Exact boundary |
|---|---|---|
| Generic directional relations | `ExactStateEncoding`, `LosslessStateEncoding`, `ExactOperatorEmbedding`, `StateIntertwining`, decoded basis-weight/distribution agreement, and their explicit-top variants retain source, target, encoder, decoder, and observation policy. | These are oriented predicates, not same-space equivalence relations. `ExactStateEncoding` is only a left-inverse certificate on the encoder image. No ray, channel, circuit, product, mixed-state, partial-trace, or all-effect consequence is built in. |
| `EQC-007-REAL-COLUMNS-REPRESENTATIVE` | Both canonical complex-to-doubled-real raw columns have explicit two-sided decoders and are `ℝ`-linear equivalences. Their restrictions are equivalences between normalized representative carriers. | This is exact coordinate bijectivity, not complex linearity, ordinary `RealRay` equivalence, or behavioral equivalence. Complex phase still descends to `RealSectorOrbit`, not through a canonical column to `RealRay`. |
| `EQC-011-COMPLEX-COLUMNS-REPRESENTATIVE` | Both canonical quaternion-to-doubled-complex raw columns have explicit two-sided decoders and are `ℝ`-linear equivalences. Their restrictions are equivalences between normalized representative carriers. | This is not quaternionic or complex linearity, a right-phase quotient theorem, circuit equality, channel equality, or measurement equality. |
| Explicit top-sector policies | The generic `AllTop...` predicates quantify arbitrary supplied `Top` and `Input` types. The non-root audit instantiates them with normalized `Rebit` and `Qubit` coefficient types to check their intended pure-state use. | A coefficient selects a linear combination of canonical columns; it is not a target-product-factor certificate. `NonProductWitness.encodedState_not_pureTopBottomProduct` refutes that reading. Mixed joint densities and partial trace remain Goal 3 work. |

The preliminary Stage 9A draft briefly described the canonical coordinate maps
as merely injective. Checking both displayed decoders exposed that each is also
surjective, so the implementation and manifest were strengthened to the
`LinearEquiv` and normalized-representative `Equiv` results before release.
This was an internal draft correction, not a newly discovered error in the
paper, and it adds no correction-log entry.

## Stage 9B proof-bearing realization

Stage 9B adds 16 stable declarations in `Semantics/SimulationWrappers.lean` and
gives all eleven frozen operator/state/reindex/schedule/compiler families their
strongest current directional wrappers. It changes no frozen cohort row or
status; it supplies proof-bearing evidence for the existing classifications.

| Frozen families | Strongest checked Stage 9B result | Exact boundary |
|---|---|---|
| `EQC-008`, `EQC-012` | Rectangular matrix realification and complexification satisfy `AllTopStateIntertwining` for every raw coefficient pair and raw source column. | Raw coordinate pairs are not normalized pure states, product ancillas, rays, densities, or decoded outcomes. |
| `EQC-019`, `EQC-025` | Equation 63 has an `ExactOperatorEmbedding` through its named row/column reindexings; both translated placed gates have exact full-denotation embeddings. | Equation 63 is not unreindexed literal equality or a second circuit translator. Placement support and resources are not bundled into operator equality. |
| `EQC-030`, `EQC-031`, `EQC-033`, `EQC-034` | Both primary circuit evaluators have exact operator embeddings and all-raw-coefficient state intertwinings. | These are evaluator and amplitude claims, not same-space circuit equality, normalization, outcomes, channels, or all effects. |
| `EQC-036` | One supplied legal schedule has exact operator/state wrappers, and injective complexification preserves the explicit unequal-schedule operator witness. | No schedule is chosen, quotient-identified, or proved independent; decoded schedule outcomes are classified separately below. |
| `EQC-037` | The composed quaternion-to-real evaluator has an exact composed embedding and nested inner-complex/outer-real coefficient intertwining. | Both coordinate layers remain explicit; no product-state, marginal, or Equation 63 circuit-translation claim follows. |
| `EQC-040` | Supplied real and complex `ExactGateCompiler` data give conditional exact compiled evaluator embeddings. | No compiler existence, finite primitive basis, synthesis, approximation, count/depth bound, runtime, or complexity result is inferred. |

The non-root audit allocates these wrappers exactly as
`2 + 3 + 4 + 3 + 2 + 2`, exercises the canonical coefficient pairs, raw-empty
and zero-wire boundaries, the concrete schedule gap, and an inhabitable local
identity compiler. Stage 9C separately owns the decoded outcome families.
Stage 9B exposes no cross-model ray, density, channel, or all-effect theorem and
adds no paper correction.

## Stage 9C proof-bearing realization

Stage 9C adds explicit one- and two-added-wire decoder infrastructure, full
target distributions, and exactly 18 semantic wrappers. It closes the five
Stage 9C-owned families `EQC-009`, `EQC-013`, `EQC-032`, `EQC-035`, and
`EQC-038`, and adds the outcome slices of `EQC-036` and `EQC-037` without
changing their Stage 9B operator/state classifications.

| Touchpoints | Strongest checked Stage 9C result | Exact boundary |
|---|---|---|
| `EQC-009`, `EQC-013` | Every normalized `Rebit`/`Qubit` coefficient gives `DecodedBasisWeightAgreement` for every raw source column. | No unitarity or source normalization is required; these are raw weights, not necessarily probabilities, densities, or partial traces. |
| `EQC-032`, `EQC-035` | Each primary simulation has separate raw point-weight, normalized full-target distribution, finite-event, and deterministic-pushforward wrappers. | Only the normalized three levels require local unitarity. The target carrier is decoded explicitly rather than hidden behind an already-marginalized `id`. |
| Outcome slice of `EQC-036` | The same four outcome levels hold for one supplied legal schedule. | Point weights need no local unitarity or arity premise; normalized levels need pointwise local unitarity. No schedule choice or independence follows. |
| Outcome slice of `EQC-037` | The composed simulation has raw point weights and normalized distribution/event/pushforward agreement after a two-wire decoder. | Decoding removes the outer realification wire before the inner complexification wire. `Qubit × Rebit` is coefficient data, not product structure. |
| `EQC-038` | Primary, supplied-schedule, and composed decoded distributions are closed under every finite event and deterministic finite pushforward. | Deterministic postprocessing is not randomized processing, channel equality, all-effect behavior, or a resource theorem. |

The semantic wrappers are allocated exactly as `2 + 4 + 4 + 4 + 4`.
Two additional audit aggregates allocate all ten decoder declarations and the
eight new full-distribution/concrete postprocessing declarations. One-wire
distribution decoding is proved equal to `pushforward tailBits`; two-wire
decoding is its ordered composition. No new paper correction is required.

## Stage 10 proof-bearing realization

Stage 10 separates exact semantics from metric approximation without adding a
finite computational representation. The six stable approximation leaves
export 169 declarations; the non-root audit and semantic manifest allocate
their exact source-order surface separately from the frozen Goal 1 cohort.

| Scope | Strongest checked Stage 10 result | Exact boundary |
|---|---|---|
| Raw real/complex operators | `operatorDistance` is the explicitly scoped Euclidean induced L2 norm, `OperatorClose 0` is `ExactOperatorEq`, multiplication and normalized-input output-column bounds compile, and directional `MappedOperatorClose` retains its map. | Fixed-budget closeness has no `Equivalence` instance or fixed-budget transitivity; additive composition changes the budget. |
| Quaternionic operators | `quaternionOperatorDistance` is the norm of the underlying-real continuous linear action and equals the L2 norm after canonical complexification. `QuaternionCentralSignClose` permits only a real central sign. | No matrix `Norm`/`Metric` instance and no arbitrary unit-quaternion operator phase are introduced. |
| Phase and state rays | `RealGlobalSignClose`, `ComplexGlobalPhaseClose`, and all three normalized `*StateRayClose` predicates have zero-budget bridges to their exact relations. State phases act on the right, and quaternionic composition uses the checked order `theta * eta`. | These are predicates on normalized representatives, not descended metrics on quotient ray values. |
| Finite distributions | `totalVariationDistance` is exactly half L1, bounds every finite event, is at most one, and contracts under deterministic pushforward. | It is not trace distance, channel distance, randomized processing, or runtime semantics. |
| Strictness | Exact real, complex-unitary, raw-phase-sensitive, and Boolean-distribution examples refute fixed positive-budget transitivity and separate raw from phase-aware distance. | Approximation is not added to the exact implication hierarchy as another equivalence relation. |

The frozen `Goal1ComparisonCohort.json` deliberately retains `EQC-042`'s
historical statement that Goal 1 had no approximation relation. Its checksum
is immutable. The human row above and the separate Goal 2 semantic manifest
record the Stage 10 refinement; neither rewrites the pre-retrofit discovery
boundary. Finite scalar encoding, rounding, code-to-value error, accumulated
circuit budgets, approximate compiler/synthesis construction, runtime, and
uniformity remain Goal 3 work under C-024.

## Stage 12 hierarchy completion

The final semantic review first found a missing valid covering arrow: equality
of operator action on every ray necessarily fixes each computational-basis
column up to its own correctly sided phase. The stable
`Semantics/Hierarchy/ProjectiveInput.lean` leaf proves nine such arrows at all
three API levels:

- raw real, complex, and quaternionic projective action implies the matching
  input-column sign/right-phase relation;
- normalized projective action implies the same result through the already
  proved raw/normalized bridge; and
- all three chronological-circuit projective wrappers imply the corresponding
  evaluator input-column relation.

The proof specializes raw projective action to `Pi.single x 1`, symmetrizes the
state phase witness, and reads off the complete `x`th output column. It needs
only a finite input type: no unitarity, nonempty index, channel, schedule,
resource, or cross-model assumption is used.

The same review then exposed a stronger scalar split. The six declarations in
`Semantics/Hierarchy/ProjectiveKernel.lean` prove that, over `ℝ` and `ℂ`,
raw projective action already determines one matrix-wide sign or unit phase.
Via the existing raw/normalized bridge and the evaluator wrappers, this holds
at the raw, normalized, and circuit levels. The matrix result is arbitrary
rectangular and needs only finite input: zero matrices, empty input or output
types, and rank-one matrices are all included, with no unitarity, squareness,
rank, nonempty-index, or output-finiteness premise.

The proof combines the input-column and output-row phase witnesses. Over a
commutative field, overlapping supports force their phases to agree; disjoint
nonzero columns are compared by applying projective agreement to the sum of
two basis columns. The zero matrix is handled separately. This commutative
argument is deliberately unavailable over quaternions.

The scalar-split final hierarchy is therefore:

```text
ℝ / ℂ:
ExactOperatorEq -> global sign/phase <-> raw projective <-> normalized projective
                                             /                  \
                                            v                    v
                                  input-column      PureInputBasisMeasurementEq
                                            \                    <-> output-row
                                             v                          v
                                                BasisMeasurementEq

ℍ:
ExactOperatorEq -> central sign -> raw projective <-> normalized projective
                                         /                  \
                                        v                    v
                              input-right       PureInputBasisMeasurementEq
                                        \                    <-> output-left
                                         v                          v
                                            BasisMeasurementEq
```

`ChannelEq` and `AllMeasurementEq` are intentionally absent from this
arbitrary-matrix diagram. They apply only to bundled square unitaries; on an
inhabited real or complex space they are equivalent to the common top-line
global/projective relation. No quaternionic channel API is inferred.

Quaternionic projective action retains only the displayed one-way arrow from
central sign. The unitary rank-one matrix `quaternionRankOneScalar j` is
projectively trivial but not central-sign equivalent, so even unitarity does
not recover the converse in dimension one. In square unitary dimension at
least two, the separate `QuaternionKernel.lean` theorem does recover exactly
the central-sign kernel.

The non-root `ProjectiveInputAudit.lean` is the proof-term consumer for all
nine projective-to-input arrows and all six real/complex kernel declarations.
Its explicit `Bool × Bool` quaternionic column and row twists also prove that
input-column and output-row phase remain incomparable and that each one-sided
relation is strictly weaker than projective action. The audit exports four
selected local axiom endpoints. These repairs change no paper-row disposition
and do not alter the frozen Goal 1 cohort.

## Final checked registry overlay

`Goal2ClassificationRegistry.json` is the authoritative Stage 11 overlay. It
classifies the immutable cohort's 936 declarations exactly once across the same
51 families. Its family totals are 33 `proved`, nine `correctedAndProved`, two
`partiallyFormalized`, and seven `unresolved` source-only claims. Every one of
the 44 non-unresolved families names proof-bearing evidence or an explicit
nonbehavioral/resource/support disposition; the seven unresolved rows
have no invented Lean proof. The overlay also records all seven classification
axes on every family and declaration, including the ten empty families, plus
208 declaration-level direct-root audit assignments and 728 non-root local-
endpoint assignments.

The table below is a mechanically rendered family summary. Within each row,
proof declarations retain JSON order and are joined by `<br>`; `—` means that
the source-only obstruction intentionally has no proof declaration. Final
dispositions, per-declaration axes, consumers, weaker results, witnesses,
obstructions, and audit assignments remain in the JSON.

<!-- GOAL2-REGISTRY-TABLE:START -->
| ID | Final status | Semantic class | Evidence mode | Strongest checked result | Goal 3 boundary |
|---|---|---|---|---|---|
| `EQC-001-Q-LEFT-PHASE-FAILURE` | `correctedAndProved` | `diagnosticCounterexample` | `counterexample` | `QuaternionicComputing.Semantics.normalizedQuaternionLeftPhase_rejection` | No Goal 3 upgrade is licensed: this is not a rejection of right phase and not circuit or channel inequivalence. |
| `EQC-002-Q-RIGHT-RAY` | `proved` | `representativeOrRay` | `proofBearingRelation` | `QuaternionicComputing.Semantics.QuaternionStatePhaseEq.equivalence`<br>`QuaternionicComputing.Semantics.QuaternionStatePhaseEq.raw_eval`<br>`QuaternionicComputing.Semantics.QuaternionStatePhaseEq.evolveUnitary` | No arbitrary quaternion operator phase or channel equality is inferred. |
| `EQC-003-C-RIGHT-RAY` | `proved` | `representativeOrRay` | `proofBearingRelation` | `QuaternionicComputing.Semantics.ComplexStatePhaseEq.equivalence`<br>`QuaternionicComputing.Semantics.ComplexStatePhaseEq.raw_eval`<br>`QuaternionicComputing.Semantics.ComplexStatePhaseEq.evolveUnitary` | No channel converse follows from equality of basis distributions. |
| `EQC-004-NORMALIZED-BASIS-DIST` | `proved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Semantics.basisWeightEq_iff_normalizedDistributionEq` | Vector, ray, all-pure-input, and channel equality remain strictly stronger or incomparable claims. |
| `EQC-005-EVENT-PUSHFORWARD-CONGRUENCE` | `proved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Semantics.BasisWeightEq.eventWeight_eq`<br>`QuaternionicComputing.Semantics.BasisWeightEq.pushforward_eq` | Randomized postprocessing, quantum partial trace, and channel equality are outside this family. |
| `EQC-006-UNITARY-EVOLUTION-NORM` | `proved` | `structuralSupport` | `supportDisposition` | `QuaternionicComputing.State.star_dotProduct_mulVec_of_mem_unitary`<br>`QuaternionicComputing.State.complexTotalWeight_mulVec_of_mem_unitary`<br>`QuaternionicComputing.State.quaternionTotalWeight_mulVec_of_mem_unitary` | Converse classifications of norm preservers remain in EQC-045 and Goal 3. |
| `EQC-007-REAL-COLUMNS-REPRESENTATIVE` | `proved` | `representativeOrRay` | `proofBearingCertificate` | `QuaternionicComputing.Semantics.realColumn0StateEquiv`<br>`QuaternionicComputing.Semantics.realColumn1StateEquiv` | Complex phase descends through RealSectorOrbit, not through a canonical column as ordinary RealRay equality. |
| `EQC-008-REAL-COLUMNS-INTERTWINING` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyMatrix_allCoefficient_stateIntertwining` | Raw coordinate coefficients are not normalized product ancillas, rays, densities, or decoded outcomes. |
| `EQC-009-REAL-COLUMNS-MEASUREMENT` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realTopCombination_allRebit_raw_decodedBasisWeightAgreement` | A mixed-top density/partial-trace extension remains Goal 3 work. |
| `EQC-010-REAL-REDUCED-OUTER` | `correctedAndProved` | `crossModelSemantics` | `proofBearingEquality` | `QuaternionicComputing.Semantics.realCanonicalColumns_reducedOuterAgreement` | Generic density matrices and a generic partial-trace theorem remain Goal 3 work. |
| `EQC-011-COMPLEX-COLUMNS-REPRESENTATIVE` | `proved` | `representativeOrRay` | `proofBearingCertificate` | `QuaternionicComputing.Semantics.complexColumn0StateEquiv`<br>`QuaternionicComputing.Semantics.complexColumn1StateEquiv` | No quaternionic/complex linearity, phase quotient, channel equality, or measurement equality is inferred. |
| `EQC-012-COMPLEX-COLUMNS-INTERTWINING` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.complexifyMatrix_allCoefficient_stateIntertwining` | No right-phase quotient, normalized product-top state, density, or decoded outcome is bundled. |
| `EQC-013-COMPLEX-COLUMNS-MEASUREMENT` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.complexTopCombination_allQubit_raw_decodedBasisWeightAgreement` | No reduced-density conclusion or mixed-top extension is claimed; those remain Goal 3 work. |
| `EQC-014-BASIS-PREPARATION` | `correctedAndProved` | `sameSpaceBehavior` | `proofBearingCertificate` | `QuaternionicComputing.Semantics.basisPreparationMatrixImplementation`<br>`QuaternionicComputing.Semantics.basisPreparationGateImplementation`<br>`QuaternionicComputing.Semantics.basisPreparationCircuit` | Unknown-state preparation, primitive synthesis, uniform compilation, and runtime claims remain outside this family. |
| `EQC-015-NONPRODUCT-WITNESS` | `correctedAndProved` | `diagnosticCounterexample` | `counterexample` | `QuaternionicComputing.Simulation.NonProductWitness.encodedState_not_pureTopBottomProduct` | Operational entanglement, mixed-state, channel, and signaling consequences require Goal 3 machinery. |
| `EQC-016-PRODUCT-ORDER-RAY-WITNESS` | `correctedAndProved` | `diagnosticCounterexample` | `counterexample` | `QuaternionicComputing.Semantics.quaternionGroundOutputs_distributionEq_not_rayEq` | This one-input strictness witness is not channel or all-measurement inequivalence. |
| `EQC-017-REALIFY-ALGEBRA` | `proved` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Matrix.realify_mul`<br>`QuaternionicComputing.Matrix.realify_conjTranspose`<br>`QuaternionicComputing.Matrix.realify_injective` | No additional behavioral or Goal 3 conclusion follows from the algebra alone. |
| `EQC-018-COMPLEXIFY-ALGEBRA` | `proved` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Quaternion.complexify_mul`<br>`QuaternionicComputing.Quaternion.complexify_conjTranspose`<br>`QuaternionicComputing.Quaternion.complexify_injective` | No phase, circuit, observation, or channel relation is inferred from the block algebra. |
| `EQC-019-DIRECT-REALIFY-REINDEX` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.directRealify_exactOperatorEmbedding` | It is not unreindexed literal matrix equality and does not define a second circuit translator. |
| `EQC-020-UNITARY-IMAGE-EQUIVS` | `proved` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Matrix.realifyUnitaryEquivImage`<br>`QuaternionicComputing.Quaternion.complexifyUnitaryEquivImage`<br>`QuaternionicComputing.Quaternion.directRealifyUnitaryEquivImage` | Ambient surjectivity and computational-model equivalence are not consequences. |
| `EQC-021-DETERMINANT-IMAGE` | `partiallyFormalized` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Matrix.realify_mem_specialOrthogonal`<br>`QuaternionicComputing.Quaternion.complexify_det_eq_one_or_neg_one_of_mem_unitary`<br>`QuaternionicComputing.Quaternion.directRealify_mem_specialOrthogonal` | The positive-sign quaternion-to-complex determinant theorem remains Goal 3 work. |
| `EQC-022-PROPER-IMAGE-WITNESSES` | `proved` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Matrix.ProperImage.realWitness_specialOrthogonal_not_realify`<br>`QuaternionicComputing.Matrix.ProperImage.complexWitness_specialUnitary_not_complexify`<br>`QuaternionicComputing.Matrix.ProperImage.directWitness_specialOrthogonal_not_directRealify` | Operational lower bounds or converse simulation separations remain Goal 3 work. |
| `EQC-023-KRONECKER-INTERCHANGE` | `partiallyFormalized` | `algebraicComparison` | `nonbehavioralDisposition` | `QuaternionicComputing.Matrix.kronecker_mul_kronecker_of_entrywiseCommute`<br>`QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_without_zeroOne`<br>`QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_i_j_failure` | No necessity theorem for the sufficient commutation condition is proved. |
| `EQC-024-PLACE-ALGEBRA` | `proved` | `structuralSupport` | `supportDisposition` | `QuaternionicComputing.Circuit.place_mul`<br>`QuaternionicComputing.Circuit.place_conjTranspose`<br>`QuaternionicComputing.Circuit.place_injective`<br>`QuaternionicComputing.Circuit.place_mem_unitary` | Physical swaps, routing circuits, and routing cost remain Goal 3 work. |
| `EQC-025-WIRE-EMBED-PLACEMENT` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyPlacedGate_exactOperatorEmbedding`<br>`QuaternionicComputing.Semantics.complexifyPlacedGate_exactOperatorEmbedding` | No prepared/product ancilla, physical routing circuit, or resource claim is bundled. |
| `EQC-026-ORDERED-EVAL` | `proved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Semantics.ExactCircuitEq.iff_eval_eq`<br>`QuaternionicComputing.Semantics.ExactCircuitEq.append` | Gate-list equality is sufficient but unnecessary; phase, resources, schedules, and cross-model maps remain separate. |
| `EQC-027-SCHEDULE-INDEPENDENCE` | `proved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Semantics.scheduledCircuit_exactCircuitEq_of_pairwise_commute` | No converse and no generic disjoint-support implication without scalar commutation are claimed. |
| `EQC-028-ORDER-DISTINCTION-WITNESS` | `correctedAndProved` | `diagnosticCounterexample` | `counterexample` | `QuaternionicComputing.Semantics.quaternionOrderingWitness_scopeBoundary` | This does not assert channel, all-effect, or every-input inequivalence. |
| `EQC-029-SCHEDULE-ENUMERATION` | `proved` | `structuralSupport` | `supportDisposition` | `QuaternionicComputing.Circuit.length_allChronologicalOrders`<br>`QuaternionicComputing.Circuit.LegalSchedule.order_mem_allChronologicalOrders`<br>`QuaternionicComputing.Circuit.ScheduleCount.BoolChain.reverseOrder_not_legal` | These combinatorial counts are not schedule independence or circuit behavior. |
| `EQC-030-C2R-OPERATOR` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyCircuit_exactOperatorEmbedding` | This is directional mapped equality with an explicit added wire, not same-space circuit equality. |
| `EQC-031-C2R-STATE` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyCircuit_allCoefficient_stateIntertwining` | Coefficients are not normalized product-top certificates; outcomes are classified separately. |
| `EQC-032-C2R-OBSERVABLE` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyCircuit_allRebit_raw_decodedBasisWeightAgreement`<br>`QuaternionicComputing.Semantics.realifyCircuit_allRebit_decodedDistributionAgreement` | Mixed top states, randomized postprocessing, partial trace, and channel equality remain outside this result. |
| `EQC-033-Q2C-OPERATOR` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.complexifyCircuit_exactOperatorEmbedding` | This is directional mapped equality with an explicit added wire, not same-space circuit equality. |
| `EQC-034-Q2C-STATE` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.complexifyCircuit_allCoefficient_stateIntertwining` | No right-phase quotient, normalized product-top certificate, outcome, or channel result is bundled. |
| `EQC-035-Q2C-OBSERVABLE` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement`<br>`QuaternionicComputing.Semantics.complexifyCircuit_allQubit_decodedDistributionAgreement` | Mixed top states, partial trace, and channel equality remain outside this result. |
| `EQC-036-SCHEDULED-Q2C` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.scheduledComplexifyCircuit_exactOperatorEmbedding`<br>`QuaternionicComputing.Semantics.scheduledComplexifyCircuit_allCoefficient_stateIntertwining`<br>`QuaternionicComputing.Semantics.scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement` | No schedule selection, schedule independence, quotient, mixed-top, channel, or resource theorem follows. |
| `EQC-037-Q2R-COMPOSED` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.quaternionToRealCircuit_exactOperatorEmbedding`<br>`QuaternionicComputing.Semantics.quaternionToRealCircuit_allCoefficient_stateIntertwining`<br>`QuaternionicComputing.Semantics.quaternionToRealCircuit_allPureTop_decodedDistributionAgreement` | Both coordinate layers remain explicit; Equation 63 is not a second circuit translator and no mixed-top/channel claim follows. |
| `EQC-038-POSTPROCESSING-SIMULATION` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.realifyCircuit_allRebit_decodedDistributionAgreement`<br>`QuaternionicComputing.Semantics.complexifyCircuit_allQubit_decodedDistributionAgreement`<br>`QuaternionicComputing.Semantics.quaternionToRealCircuit_allPureTop_decodedDistributionAgreement` | Randomized postprocessing, channel equality, and resource accounting are not included. |
| `EQC-039-EXACT-COMPILER-SEMANTICS` | `correctedAndProved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Circuit.ExactGateCompiler.compileCircuit_exactCircuitEq` | Compiler existence, synthesis, approximation, primitive-count guarantees, and runtime remain Goal 3 work. |
| `EQC-040-COMPILED-IMAGE-SEMANTICS` | `proved` | `crossModelSemantics` | `proofBearingRelation` | `QuaternionicComputing.Semantics.compileRealifyCircuit_exactOperatorEmbedding`<br>`QuaternionicComputing.Semantics.compileComplexifyCircuit_exactOperatorEmbedding` | No compiler existence, synthesis, approximation, gate-count bound, or runtime is inferred. |
| `EQC-041-STRUCTURAL-RESOURCE-EQUALITIES` | `proved` | `resourceClaim` | `resourceDisposition` | `QuaternionicComputing.Semantics.ExistingResultsAudit.translationResources_family`<br>`QuaternionicComputing.Semantics.ExistingResultsAudit.compiledResourceBounds_family` | Uniform synthesis, physical routing cost, runtime, and bit complexity remain Goal 3 work. |
| `EQC-042-EXACT-VS-APPROX-BOUNDARY` | `proved` | `approximationBoundary` | `proofBearingRelation` | `QuaternionicComputing.Semantics.operatorClose_zero_iff_exactOperatorEq`<br>`QuaternionicComputing.Semantics.complexStateRayClose_zero_iff_complexStatePhaseEq`<br>`QuaternionicComputing.Semantics.distributionClose_zero_iff` | Finite scalar encoding, circuit-error accumulation, approximate compilation/synthesis, and runtime remain Goal 3 work. |
| `EQC-043-REAL-SIGN-RAY` | `correctedAndProved` | `representativeOrRay` | `proofBearingRelation` | `QuaternionicComputing.Semantics.RealStatePhaseEq.equivalence`<br>`QuaternionicComputing.Semantics.RealStatePhaseEq.iff_realRay_mk_eq` | No converse from basis distributions and no arbitrary complex-phase realification are claimed. |
| `EQC-044-BASIS-CLASSICAL-BEHAVIOR` | `correctedAndProved` | `sameSpaceBehavior` | `proofBearingRelation` | `QuaternionicComputing.Semantics.sameBasisBehavior_iff_realBasisMeasurementEq`<br>`QuaternionicComputing.Semantics.sameBasisBehavior_iff_complexBasisMeasurementEq`<br>`QuaternionicComputing.Semantics.sameBasisBehavior_iff_quaternionBasisMeasurementEq` | No raw transition biconditional or arbitrary-matrix behavior relation is accepted. |
| `EQC-045-NORM-PRESERVER-CONVERSES` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/4-FOUNDATIONS must state and prove the scalar-specific converse classifications. |
| `EQC-046-MIXED-TOP-OBSERVATIONAL` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/3-DENSITY must define joint mixed states, product/no-correlation hypotheses, and the decoded marginal theorem. |
| `EQC-047-QUATERNION-REDUCED-SEPARATION` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/3-DENSITY must formalize the two reduced matrices, diagonal agreement, and matrix inequality. |
| `EQC-048-COMPUTATIONAL-MODEL-EQUIVALENCE` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/12-UNIFORMITY and 13-REALQTM must supply the uniform computational models and resource accounting. |
| `EQC-049-PHYSICAL-SWAP-SIMULATION` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/6-ROUTING must define the architecture, synthesize swap circuits, and prove denotation and cost. |
| `EQC-050-TOP-WIRE-PHASE-TRACKING` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/14-STRUCTURE must select and prove a convention-correct invariant-subspace/orbit replacement. |
| `EQC-051-OPERATIONAL-CONVERSE-SIMULATION` | `unresolved` | `sourceOnlyClaim` | `sourceOnlyObstruction` | — | Goal 3/14-STRUCTURE and 16-CHANNELS must define an operational simulation relation before any converse separation. |
<!-- GOAL2-REGISTRY-TABLE:END -->

## Ambiguity closure ledger

All wording issues found during the retrofit now have an explicit disposition.
“Closed” means the current public documentation and registry state the checked
scope. Historical Goal 1 plans remain untouched as evidence of the discovery
state. “Bounded” means the source claim is still absent or partial, but the
registry names the exact obstruction and Goal 3 boundary rather than silently
choosing an interpretation.

1. **Resolved in Stage 3A:** `docs/ReleaseReport.md` now says quaternionic
   state/ray phase acts on the right, not unqualified “global phase.”
2. **Resolved in Stage 3A:** correction C-006 is now titled “Quaternionic
   state/ray phase is on the wrong side” and distinguishes raw from normalized
   evidence.
3. **Resolved in Stages 3A and 3C:** `docs/Conventions.md` explicitly tags
   right phase as state/ray representative phase, while the operator layer
   separately restricts matrix-wide global phase to a central real sign and
   records the rank-one projective exception.
4. **Closed in Stages 9B-9C:** the type-confused historical Goal 1 phrase is
   classified as equality of the source and explicitly decoded target basis
   weights/distributions, never equality of a probability with a state output.
5. **Closed in Stage 11:** “symplectic image/group isomorphism” is classified as
   a `MulEquiv` onto `complexifyUnitaryImage` plus one-way symplectic-form
   membership, not equality with the ambient compact symplectic group.
6. **Closed in Stage 11:** traceability uses the same one-way image-membership
   qualification and records the missing converse.
7. **Closed in Stage 11:** every “equivalent to its image” reference is explicitly
   algebraic `MulEquiv`-onto-range, never ray, circuit, channel, observational,
   or computational-model equivalence.
8. **Closed in Stage 9C:** “normalized output equality” is rendered as equality
   of decoded finite distributions, then finite events and deterministic
   pushforwards. The historical Goal 1 plan remains discovery evidence.
9. **Closed in Stages 9B-9C:** scheduled simulation is split into mapped operator
   equality and the exactly scoped decoded observation theorems; the concrete
   distinction is a one-input basis-weight inequality.
10. **Closed in Stages 8 and 11:** the ordering witness is explicitly one-input;
    the same outcome label has unequal weight. The registry forbids promotion
    to every-input, channel, or all-effect inequivalence.
11. **Closed in Stages 9B-9C:** the standalone theorems quantify every source
    state and every named normalized `Rebit`/`Qubit` coefficient at the stated
    observation level.
12. **Closed in Stages 7-8:** basis-weight and matrix-evolution invariance are
    not called channel or all-measurement laws. Those notions now have separate
    same-space real/complex APIs.
13. **Closed in Stage 9C:** “all marginals” is restricted to finite events and
    deterministic maps of the decoded classical outcome distribution; no
    generic quantum partial trace is inferred.
14. **Closed in Stage 9C:** “deterministic” modifies the postprocessing map, not
    the finite probability distribution.
15. **Closed in Stage 11:** occurrence-list permutation data is structural
    support, not semantic circuit equivalence; exact schedule equality requires
    the proved commutation hypothesis.
16. **Closed in Stages 9B-9C:** scheduled normalized results require local
    unitarity of every gate occurrence; “pointwise” never means equality of
    state actions.
17. **Closed in Stage 9B:** Equation 63 agrees with the composed embedding only
    after named simultaneous row/column reindexing and is not a second circuit
    translator.
18. **Closed by the final axes:** the paper's three uses of “simulation” are
    separately classified as structural resource statements, directional
    operator embeddings, and decoded classical-outcome agreement.
19. **Closed by C-018 and Stage 11:** order dependence is existential, schedule
    equality has a sufficient commutation theorem, and the factorial count is
    confined to empty precedence.
20. **Bounded as `EQC-048`:** “same computational power” is a source-only
    uniform-model claim, not equality between the two path operators, rays,
    distributions, or channels.
21. **Bounded as `EQC-046`:** mixed-top observation requires a joint density,
    product/no-correlation hypothesis, and partial trace. Normalized coefficient
    parameters do not certify factorization.
22. **Bounded as `EQC-047`:** quaternionic reduced-matrix separation remains a
    source-only density claim distinct from the corrected real two-sector outer
    equality in `EQC-010`.
23. **Closed for current results and bounded for synthesis:** literal image-gate
    counts are structural resource equalities; primitive decomposition and
    runtime remain outside `EQC-041`.
24. **Closed by C-024 and `EQC-042`:** exact algebraic relations and budgeted
    exact-object approximation are distinct. Finite encodings, accumulated
    circuit error, approximate synthesis, and runtime remain Goal 3 work.
25. **Bounded as `EQC-051`:** algebraic non-surjectivity is not an operational
    converse separation without a chosen simulation relation, encoders,
    decoders, ancilla policy, and observation scope.
26. **Resolved in Stage 4C / C-027:** the paper defines source states as rays
    before applying `h₀` or `h₁` to representatives. Neither column map
    descends to ordinary `RealRay` on a nonempty space. Complex phase descends
    as `RealSectorOrbit` rotation, while representative intertwining and the
    decoded bottom distribution remain exact.
27. **Resolved in Stage 5:** equality of the raw predicate “input `x` reaches
    basis output `y` up to phase” is not classical reversible behavior. Two
    nonmonomial unitaries can make both raw relations empty. The implemented
    relation therefore requires explicit permutation certificates before
    `SameBasisBehavior` can be formed.

## Completed Stage 11 validation evidence

The final-registry validator passes all ten rule groups. It proves that the
frozen checksum is still
`65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`,
the family IDs are unchanged and ordered, every one of the 936 frozen
declarations occurs exactly once, all seven classification axes are populated
on every family and declaration, and proof, witness, consumer, audit, and
source-only-obstruction policies are consistent. Generated Lean checks resolve
all 936 declaration names and all
named proof/consumer/audit targets. The family summary between the marker
comments is checked against the JSON rather than maintained independently.

Stage 11 adds six stable `Semantics/ExistingResults.lean` wrappers and 15
non-root `ExistingResultsAudit` endpoints. The independent Goal 2 semantic API
manifest preserves its corrected first-1,269 structural hash
`c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229`
and contains 1,275 unique declarations, 167 distinct consumers, and 356 direct
root-audit labels; its full structural hash is
`bbea85679b6e8425f398f8ab984736472450a440cad984315d4dbd2c62def45f`.
The two-label difference from the Stage 10 closure snapshot is an audit-metadata
repair: two strictness declarations already had genuine root `#print axioms`
commands and are now labeled direct instead of transitive. It changes neither
theorem/proof code nor the selected endpoints or 542-command root-audit count;
the two long targets now sit in their exact namespace scope for qualified
parsing without a long-line warning.
The combined Stage 11 build completes 2,776 jobs.

The executable public-root audit contains 542 commands: 539 report nonempty
axiom sets and three are axiom-free. All 15 `ExistingResultsAudit` commands are
nonempty. Both exact unions are `{propext, Classical.choice, Quot.sound}`; no
project-specific axiom was introduced. The source tree contains 99 Lean files
including the public root. Stage 12's clean release, downstream, scan, and
independent-review gates remain pending, so these results close the registry
stage rather than Goal 2 as a whole.

## Stage 12 release evidence

Stage 12 preserves the complete 1,275-entry Stage 11 manifest prefix at
`bbea85679b6e8425f398f8ab984736472450a440cad984315d4dbd2c62def45f`
and appends the nine `Hierarchy.ProjectiveInput` declarations followed by the
six `Hierarchy.ProjectiveKernel` declarations, each in exact source order. The
intermediate first-1,284 prefix has structural hash
`a372726bee9bf0dff73bc2100db4196f501395491ba7b5e2e95e19efbcaed983`.
The complete manifest now has 1,290 declarations, 169 distinct consumers, 371
direct root-audit labels, and structural hash
`3146d7785774b7cff4b0a3bd7335a3fe6e55e220722b1672251edcf506980fa3`.
The frozen 51-family/936-declaration registry and its checksum are unchanged.

The executable validator passes at `51/936/10`, `1290/169/371`, and seven
axes, including generated Lean resolution of every declaration and consumer.
The source tree has 102 Lean files including the public root. The root audit
has 557 commands (`554 + 3`), `ExistingResultsAudit` has 15, and
`ProjectiveInputAudit` has four; every exact collective union is
`{propext, Classical.choice, Quot.sound}`. The new
`realComplexProjectiveKernel_arrows_api` endpoint consumes all six generic
kernel declarations as proof terms; the public root directly audits each one.

After the shared pinned dependency cache was cleaned, the baseline public tree
rebuilt successfully in 2,782 jobs. Before the final generic-kernel refinement,
the promoted tree passed the 2,775-job default build, the 2,777-job integrated
root/audit build, and the 2,787-job exhaustive maintained-audit build, together
with warning-as-error direct compilation and a public-root-only downstream
smoke. Final post-refinement builds, static scans, and independent release
reviews were then rerun; only the independent release verdicts remain as
closure gates in `goal-2/12-RELEASE.md`.
