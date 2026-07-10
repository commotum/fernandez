# Semantic Equivalence Classification

## Status and purpose

This document is the human-readable Stage 1 seed for Goal 2's semantic
classification retrofit.  It records the comparison families visible in the
completed Goal 1 public surface and in the source paper.  Every classification
below is **provisional**: a row is an inventory hypothesis, not a proof that the
named declarations inhabit a future relation and not evidence that a relation
planned by Goal 2 has already been implemented.

The table freezes 51 family-level rows.  The first 42 come from the completed
library and its release evidence.  The final nine are source-paper comparison
families that are absent, partial, external, or deliberately assigned to later
work.  Freezing these rows prevents later Goal 2 declarations from making the
Goal 1 inventory grow recursively.

## Scope policy

- A **family row** groups declarations that express one mathematical comparison
  at one semantic level.  It is stable enough for review, documentation, and
  ownership, but is not declaration-complete.
- Exact declaration names, source references, aliases, wrapper theorems, and
  audit endpoints belong in the machine-readable `Goal1ComparisonCohort` JSON.
  Its array fields are authoritative for declaration-level coverage and its
  checksum must remain unchanged after the cohort is frozen.
- New public relations, hierarchy theorems, counterexamples, wrappers, and
  metrics created by Goal 2 belong in the separate `Goal2SemanticAPIManifest`
  JSON.  They do not become new rows in this table or alter the frozen cohort
  checksum.
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
  Quaternionic output-row phase acts on the left. Goal 2 Stage 3C must
  characterize the genuine quaternionic projective operator kernel and state
  the one-dimensional exception explicitly; until that proof exists, no
  arbitrary unit quaternion or presumed central kernel is provisionally
  treated as operator global phase.
- An `Eq`, `Equiv`, `MulEquiv`, group-image theorem, resource equality, or green
  build is not behavioral evidence unless a theorem explicitly inhabits the
  relevant behavioral relation.
- Approximate closeness is an error-budget relation, not an equivalence
  relation.  Exact algebraic simulation does not supply a metric, encoder,
  approximation algorithm, or accumulated-error theorem.

## Frozen family seed

Abbreviations in the owner column are Goal 2 (`G2`) and Goal 3 (`G3`) stages.
“Existing” in a disposition means only that representative Goal 1 declarations
exist; the proposed Goal 2 classification wrapper is still unimplemented.
Each owner cell has exactly one primary owner: the leftmost stage. Any later
comma- or semicolon-separated stages are consumers or downstream extensions,
not co-owners. The JSON records these separately as `primaryOwner` and
`consumerStages` so uniqueness does not depend on prose interpretation.

| ID | Evidence / representative declarations | Space | Subject | Input scope | Observation scope | Phase side | Exactness | Ancilla / marginal policy | Provisional disposition | Primary owner; consumer stages |
|---|---|---|---|---|---|---|---|---|---|---|
| `EQC-001-Q-LEFT-PHASE-FAILURE` | `LeftPhaseEquivalent`, `not_leftPhaseEquivalent_gate_i_input`, `fixed_left_phase_not_natural`; `Corrections.md:90-116` | same | state columns and one evolution | one explicit raw unnormalized pair of weight `2`; the Stage 3A overlay supplies a normalized replacement | ray preservation failure | quaternion left, deliberately rejected | exact counterexample | none | Existing diagnostic; classify as a failed convention, never physical ray equality | G2 `3A-STATEPHASE`, `8B-WITNESSES` |
| `EQC-002-Q-RIGHT-RAY` | `Quaternion.RightPhaseEquivalent`, `rightPhaseEquivalent_equivalence`, `rightPhaseEquivalent_mulVec`; `Architecture.md:111-119` | same | quaternionic state columns | arbitrary compatible columns; normalized wrappers where probabilities are claimed | ray, basis weight, total weight, evolution | quaternion right | exact | none | Existing state-ray API; relation-valued wrappers and normalized quotient remain future work | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-003-C-RIGHT-RAY` | `Complex.RightPhaseEquivalent`, `rightPhaseEquivalent_complex_mulVec`; `Traceability.md:53` | same | complex state columns | arbitrary compatible columns; normalized wrappers | ray, basis weight, total weight, evolution | complex right, equal to left by commutativity | exact | none | Existing state-ray API; quotient and hierarchy classification unimplemented | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-004-NORMALIZED-BASIS-DIST` | `FiniteDistribution.ofNormalizedState`, `FiniteDistribution.ext`; `Architecture.md:132-136` | same | normalized state and finite distribution | one normalized state or two distributions | full computational-basis distribution | none | exact | none | Existing distribution construction/extensionality; classify independently of state-ray equality | G2 `2-CORE` |
| `EQC-005-EVENT-PUSHFORWARD-CONGRUENCE` | `eventWeight_eq_of_weight_eq`, `pushforward_eq_of_weight_eq`; `Conventions.md:131-136` | same | finite distributions | one pair of pointwise-equal distributions | finite events and deterministic finite postprocessing | none | exact | deterministic map supplies classical marginal/decoder | Existing finite consequence family; not channel or randomized-machine equality | G2 `2-CORE`, `9C-OUTCOMES` |
| `EQC-006-UNITARY-EVOLUTION-NORM` | `star_dotProduct_mulVec_of_mem_unitary`, `*TotalWeight_mulVec`, `*State.evolveUnitary`; `Architecture.md:238-242` | same | matrix action on state | every compatible state under a supplied unitary | norm, total weight, normalization | none | exact | none | Existing forward preservation family; does not include converse norm-preserver classification | G2 `2-CORE`, `8A-ARROWS` |
| `EQC-007-REAL-COLUMNS-REPRESENTATIVE` | `realColumn0`, `realColumn1`, reconstruction, injectivity, `realColumns_orthogonal`, `realColumns_equal_norm`; `goal-1/4-STATES.md:167-182` | cross | complex representative to doubled real representative | arbitrary finite column | amplitudes, reconstruction, norm and inner product | none | exact after encoding | one explicit top sector; no marginal | Existing algebraic state-encoding family; nonbehavioral until connected to an observation relation | G2 `9A-RELATIONS`, `11B-CERTIFICATES` |
| `EQC-008-REAL-COLUMNS-INTERTWINING` | `realify_mulVec_realColumn0`, `realify_mulVec_realColumn1`, top-combination theorem; `Traceability.md:40` | cross | operator action and encoded state | every compatible source column | exact evolved amplitudes | none | exact intertwining | canonical or arbitrary real top-sector combination | Existing cross-space state intertwining | G2 `9B-WRAPPERS` |
| `EQC-009-REAL-COLUMNS-MEASUREMENT` | `realColumn0_bottomWeight`, `realColumn1_bottomWeight`, `realTopCombination_bottomWeight_of_rebit`; `goal-1/4-STATES.md:183-187` | cross | encoded pure state | every source pure state and every normalized pure top rebit | decoded computational-basis weights | none | exact decoded agreement | sum false/true added-wire sectors; pure uncorrelated top | Existing pure-input decoded observation family; mixed top excluded | G2 `9C-OUTCOMES`; G3 `3-DENSITY` for mixed extension |
| `EQC-010-REAL-REDUCED-OUTER` | `reducedRealOuter_realColumns`, `reducedRealOuter_diagonal`; `Traceability.md:41,84` | cross | rank-one outer matrices | every source pure column; two canonical encodings | reduced matrix and its computational diagonal | none | exact | explicit two-sector diagonal-block sum, not generic partial trace | Existing rank-one equality; generic density/partial trace absent | G2 `11B-CERTIFICATES`; G3 `3-DENSITY` |
| `EQC-011-COMPLEX-COLUMNS-REPRESENTATIVE` | `complexColumn0`, `complexColumn1`, reconstruction, injectivity, `complexColumns_orthogonal`; `goal-1/4-STATES.md:199-212` | cross | quaternionic representative to doubled complex representative | arbitrary finite column | amplitudes, reconstruction, norm and inner product | source quaternion state phase remains right-sided | exact after encoding | one explicit top sector; no marginal | Existing algebraic state-encoding family | G2 `9A-RELATIONS`, `11B-CERTIFICATES` |
| `EQC-012-COMPLEX-COLUMNS-INTERTWINING` | `complexify_mulVec_complexColumn0`, `complexify_mulVec_complexColumn1`, top-combination theorem; `Traceability.md:45` | cross | operator action and encoded state | every compatible quaternionic column | exact evolved amplitudes | source quaternion state phase right-sided | exact intertwining | canonical or arbitrary complex top-sector combination | Existing cross-space state intertwining | G2 `9B-WRAPPERS` |
| `EQC-013-COMPLEX-COLUMNS-MEASUREMENT` | `complexColumn0_bottomWeight`, `complexColumn1_bottomWeight`, `complexTopCombination_bottomWeight_of_qubit`; `Traceability.md:46,112` | cross | encoded pure state | every source pure state and every normalized pure top qubit | decoded computational-basis weights | none | exact decoded agreement | sum false/true added-wire sectors; pure uncorrelated top | Existing pure-input observation family; no reduced-matrix equality is claimed | G2 `9C-OUTCOMES`; G3 `3-DENSITY` for mixed extension |
| `EQC-014-BASIS-PREPARATION` | `basisPreparationGate_mulVec_ground`, `eval_prepend_basisPreparation_mulVec_ground`; `Corrections.md:583-593` | same | basis state and circuit | one known computational-basis assignment | exact output column | none | exact | no ancilla; full-support XOR gate | Existing basis-preparation behavior; not arbitrary-state preparation or uniform synthesis | G2 `5-BASIS`, `11B-CERTIFICATES` |
| `EQC-015-NONPRODUCT-WITNESS` | `encodedState_not_pureTopBottomProduct`; `Architecture.md:269-274` | cross | one encoded pure state | one normalized rational source state | pure factorization obstruction | none | exact negation | explicit added wire; no density marginal | Existing structural witness; not entanglement, channel, or signaling classification | G2 `11-REGISTRY`; G3 `16C-WITNESS` for operational consumers |
| `EQC-016-PRODUCT-ORDER-RAY-WITNESS` | `ground_outputs_not_rightPhaseEquivalent`, `ground_outputs_basis_weights_eq`; `Corrections.md:378-393` | same | two scheduled quaternionic outputs | one normalized pointwise-product ground input | state ray and complete basis-weight family | quaternion state phase right | exact inequality plus exact equality | none | Existing strictness witness: basis weights do not determine quaternionic ray | G2 `8B-WITNESSES` |
| `EQC-017-REALIFY-ALGEBRA` | `realify_mul`, `realify_conjTranspose`, `realify_injective`; `goal-1/3-MATRICES.md:126-144` | cross | matrix embedding | arbitrary compatible matrices | full matrix entries and algebraic operations | none | exact mapped algebra | doubled sum indices | Existing algebraic identity family; classify as nonbehavioral support | G2 `11-REGISTRY` |
| `EQC-018-COMPLEXIFY-ALGEBRA` | `complexify_mul`, `complexify_conjTranspose`, `complexify_injective`; `goal-1/3-MATRICES.md:146-165` | cross | matrix embedding | arbitrary compatible quaternionic matrices | full matrix entries and algebraic operations | multiplication order explicit | exact mapped algebra | doubled sum indices | Existing algebraic identity family; classify as nonbehavioral support | G2 `11-REGISTRY` |
| `EQC-019-DIRECT-REALIFY-REINDEX` | `directRealify_eq_reindex`; `Architecture.md:86-90`; `Corrections.md:544-560` | cross | two matrix representations | every compatible quaternionic matrix | full matrix after named row/column reindexing | none | exact after reindex | four sectors ordered `[Re,ImI,ImK,ImJ]`; no circuit translator | Existing reindexed matrix equality; not literal circuit equality | G2 `9B-WRAPPERS`, `11-REGISTRY` |
| `EQC-020-UNITARY-IMAGE-EQUIVS` | `realifyUnitaryEquivImage`, `complexifyUnitaryEquivImage`, `directRealifyUnitaryEquivImage`; `ReleaseReport.md:45-56` | cross | unitary groups and homomorphism ranges | every unitary matrix in source group | algebraic multiplication and image membership | none | exact algebraic equivalence onto range | changed scalar/dimension; no state decoder | Existing `MulEquiv`-onto-image family; explicitly nonbehavioral | G2 `11-REGISTRY` |
| `EQC-021-DETERMINANT-IMAGE` | `realify_det`, `realify_mem_specialOrthogonal`, quaternion determinant alternatives, `directRealify_mem_specialOrthogonal`; `Architecture.md:319-336` | cross | matrix/group image | every source matrix or unitary under stated hypotheses | determinant and target group membership | none | exact | changed scalar/dimension | Existing algebraic group facts; quaternion-to-complex positive sign remains outside this completed family | G2 `11-REGISTRY`; G3 `5-DETERMINANT` |
| `EQC-022-PROPER-IMAGE-WITNESSES` | `realWitness_specialOrthogonal_not_realify`, `complexWitness_specialUnitary_not_complexify`, `directWitness_specialOrthogonal_not_directRealify`; `Traceability.md:141` | cross | target matrix versus embedding image | explicit low-dimensional matrices | nonmembership in algebraic image | none | exact counterexamples | no encoder/decoder or operational observation | Existing proper-image diagnostics; no operational lower bound | G2 `11-REGISTRY` |
| `EQC-023-KRONECKER-INTERCHANGE` | `kronecker_mul_kronecker_of_entrywiseCommute`, success/failure examples; `goal-1/7-ORDERING.md:151-162` | same | matrix products | arbitrary compatible matrices under explicit crossing commutation; explicit examples | full matrix equality or inequality | none | exact | tensor-factor indices only | Existing algebraic condition and witnesses; no necessity theorem | G2 `11-REGISTRY`, `8B-WITNESSES` |
| `EQC-024-PLACE-ALGEBRA` | `place_mul`, `place_conjTranspose`, `place_injective`, `place_mem_unitary`; `goal-1/5-CIRCUITS.md:146-159` | cross | local versus contextual matrix | every local matrix and explicit split/support | full contextual operator | none | exact after reindex/padding | semantic complement; no physical swaps | Existing placement algebra; nonbehavioral support until consumed by a circuit comparison | G2 `11-REGISTRY` |
| `EQC-025-WIRE-EMBED-PLACEMENT` | `wireRealify_place`, `wireComplexify_place`, translated-gate denotation theorems; `Corrections.md:472-481` | cross | placed source gate and translated placed gate | every locality-certified gate | exact mapped denotation and support data | none | exact operator embedding | one shared added top wire; same complement | Existing one-gate cross-model naturality | G2 `9B-WRAPPERS` |
| `EQC-026-ORDERED-EVAL` | `OrderedCircuit.eval`, `eval_cons`, `eval_append`; `Traceability.md:30,72` | same | ordered circuits | every chronological list | exact operator denotation | none | exact | none | Existing semantics equality family; future `ExactCircuitEq` wrapper unimplemented | G2 `2-CORE`, `11B-CERTIFICATES` |
| `EQC-027-SCHEDULE-INDEPENDENCE` | `LegalSchedule.scheduledEval_eq_of_pairwise_commute`; `Architecture.md:199-206` | same | two legal schedules of one occurrence family | all supplied schedules under pairwise-commuting global denotations | exact evaluated operator | none | exact | no schedule selection; same finite occurrence family | Existing sufficient equality theorem; no converse or generic disjoint-support implication | G2 `8A-ARROWS`, `8B-WITNESSES` |
| `EQC-028-ORDER-DISTINCTION-WITNESS` | `scheduled_operators_ne`, `output_basis00_weight_ne`, translated analogues; `goal-1/7-ORDERING.md:174-186` | same and cross translation | two legal schedules | one explicit source input; one basis outcome | operator inequality and selected basis-weight inequality | none | exact counterexample | translated version has one fixed top state | Existing existential witness; not all-input or all-measurement inequivalence | G2 `8B-WITNESSES`, `9B-WRAPPERS` |
| `EQC-029-SCHEDULE-ENUMERATION` | `allChronologicalOrders`, exact length and legality theorems; `Architecture.md:223-228` | same | finite lists/schedules | finite identifier type; empty or general precedence as stated | structural membership/count, not circuit behavior | none | exact | none | Existing combinatorial equalities; classify as nonbehavioral resource/support | G2 `11-REGISTRY` |
| `EQC-030-C2R-OPERATOR` | `eval_realifyCircuit`, operator projection of `complexToReal_exactSimulation`; `Corrections.md:181-206` | cross | source and translated circuit operators | every finite ordered complex circuit | full operator after `wireRealify` | none | exact mapped-operator equality | one shared added rebit in target type | Existing cross-model operator certificate; not same-space equality | G2 `9B-WRAPPERS` |
| `EQC-031-C2R-STATE` | `eval_realifyCircuit_mulVec_wireReal*`; `Architecture.md:244-251` | cross | circuit evolution on encoded state | every source column; canonical and arbitrary top combinations where stated | exact target amplitude column | none | exact intertwining | one shared pure top-sector encoding | Existing cross-model state certificate | G2 `9B-WRAPPERS` |
| `EQC-032-C2R-OBSERVABLE` | `realifyCircuitOutput_bottomProbability`; `Traceability.md:33,85` | cross | normalized circuit outputs | every normalized source pure input and every normalized pure top rebit | complete decoded bottom basis probabilities | none | exact decoded agreement | sum over shared top rebit; no mixed or entangled top | Existing pure-input observation certificate | G2 `9C-OUTCOMES`; G3 `3-DENSITY` |
| `EQC-033-Q2C-OPERATOR` | `eval_complexifyCircuit`, operator projection of `quaternionToComplex_exactSimulation`; `Corrections.md:181-206` | cross | source and translated circuit operators | every finite ordered quaternionic circuit | full operator after `wireComplexify` | none | exact mapped-operator equality | one shared added qubit in target type | Existing cross-model operator certificate | G2 `9B-WRAPPERS` |
| `EQC-034-Q2C-STATE` | `eval_complexifyCircuit_mulVec_wireComplex*`; `Architecture.md:244-259` | cross | circuit evolution on encoded state | every source column; canonical and arbitrary top combinations where stated | exact target amplitude column | quaternion source state phase remains right-sided | exact intertwining | one shared pure top-sector encoding | Existing cross-model state certificate | G2 `9B-WRAPPERS` |
| `EQC-035-Q2C-OBSERVABLE` | `complexifyCircuitOutput_bottomProbability`; `Traceability.md:35,46,112` | cross | normalized circuit outputs | every normalized quaternionic source pure input and every normalized pure top qubit | complete decoded bottom basis probabilities | none | exact decoded agreement | sum over shared top qubit; no mixed or entangled top | Existing pure-input observation certificate | G2 `9C-OUTCOMES`; G3 `3-DENSITY` |
| `EQC-036-SCHEDULED-Q2C` | `scheduledQuaternionToComplex_exactSimulation`; `goal-1/7-ORDERING.md:169-173` | cross | one supplied scheduled source circuit and translated circuit | every supplied legal schedule; pure state/top arguments as in primary theorem | operator, state, decoded basis probabilities, and resources remain separate | none | exact per schedule | no schedule choice, quotient, or independence | Existing directional per-schedule certificate family | G2 `9B-WRAPPERS`, `9C-OUTCOMES` |
| `EQC-037-Q2R-COMPOSED` | `eval_quaternionToRealCircuit`, nested state theorem, `wireQuaternionToRealBottomWeight`; `Architecture.md:261-267` | cross | quaternionic circuit and composed real translation | every ordered source circuit; normalized pure state/top arguments | operator, nested state, four-sector bottom probabilities | none | exact mapped/decoded agreement | two shared added wires; sum four assignments | Existing compositional certificate; direct Equation 63 is not a second circuit translator | G2 `9B-WRAPPERS`, `9C-OUTCOMES` |
| `EQC-038-POSTPROCESSING-SIMULATION` | `realifyCircuitBottomDistribution_eq`, `complexifyCircuitBottomDistribution_eq`, event/pushforward theorems; `Architecture.md:276-280` | cross | source output and decoded target output distributions | every normalized pure input/top covered by primary simulations | full finite distribution, all finite events, deterministic pushforwards | none | exact decoded agreement | added wire marginalized before comparison | Existing finite observational closure; not randomized or channel equality | G2 `9C-OUTCOMES` |
| `EQC-039-EXACT-COMPILER-SEMANTICS` | `ExactGateCompiler.eval_compileCircuit`; `Architecture.md:307-315` | same | source circuit and supplied expansion circuit | every circuit under a supplied exact compiler certificate | exact evaluated operator | none | exact | compiler is ancilla-free on same wires unless separately stated | Existing conditional semantic preservation; no compiler existence | G2 `11-REGISTRY`; G3 `10-SYNTHESIS` for construction |
| `EQC-040-COMPILED-IMAGE-SEMANTICS` | `eval_compile_realifyCircuit`, `eval_compile_complexifyCircuit`; `goal-1/8-RESOURCES.md:217-220` | cross then same-target compilation | image circuit and supplied compiled target | every source circuit under supplied compiler data | same embedded operator after compilation | none | exact | same target wires; no extra compiler ancilla in present interface | Existing conditional wrapper family; no synthesis or approximation | G2 `9B-WRAPPERS`, `11-REGISTRY` |
| `EQC-041-STRUCTURAL-RESOURCE-EQUALITIES` | gate count, width, arity, depth, dense-slot, and schedule-count theorems; `Architecture.md:283-315` | same and cross structural | finite circuit/resource certificates | every circuit under each theorem's nonempty/common-wire/bound premise | counts and bounds only | none | exact equality or stated inequality | shared-wire policy explicit; no observable decoder | Existing nonbehavioral resource family; JSON must split heterogeneous declaration arrays | G2 `11-REGISTRY` |
| `EQC-042-EXACT-VS-APPROX-BOUNDARY` | three `*exactSimulation` families and `ExactGateCompiler.eval_compileCircuit`; absence recorded in `Corrections.md:508-529` | source only boundary | exact versus encoded approximate circuit models | exact mathematical matrices only | no implemented error metric or approximate observation bound | phase-aware approximation not implemented | exact side only | none | Boundary row: no Goal 1 approximation relation exists | G2 `10-APPROX`; G3 `9-APPROX` for finite precision |
| `EQC-043-REAL-SIGN-RAY` | Paper Equations 5-6, `fernandez-2003.md:101-114`; `Traceability.md:27` | source only | normalized real state rays | every normalized real state representative | ray equality modulo sign | real right/left sign, central | exact relation requested, quotient absent | none | Source family partially represented by concrete `Rebit`; relation/quotient unimplemented | G2 `3A-STATEPHASE`, `4-RAYS` |
| `EQC-044-BASIS-CLASSICAL-BEHAVIOR` | Paper `fernandez-2003.md:40-48,119-128,395-407,812`; basis-preparation declarations are only one consumer | same and cross | certified computational-basis action | every basis input for a certified basis-classical operator | induced classical basis permutation, deliberately forgetting general quantum action | input-column phase may be forgotten only under certificate | exact behavior relation unimplemented | top-labelled target basis for the embedding examples | Source anchor for nonvacuous `SameBasisBehavior`; generic biconditional forbidden | G2 `5-BASIS` |
| `EQC-045-NORM-PRESERVER-CONVERSES` | Paper `fernandez-2003.md:50,69,818,1288`; `Traceability.md:55,60` | source only | linear maps and unitary/orthogonal classes | every finite linear map under scalar/linearity hypotheses | preservation of full norm/inner product | none | exact classification requested | none | Background converse family absent or partial; antiunitary and scalar assumptions must remain explicit | G3 `4-FOUNDATIONS` |
| `EQC-046-MIXED-TOP-OBSERVATIONAL` | Paper `fernandez-2003.md:661,1075`; `Traceability.md:85,112` | source only cross | mixed product top state and encoded bottom system | every uncorrelated mixed top rebit/qubit and source density/pure state as formalized | decoded bottom basis distribution | none | exact claim unimplemented | product/uncorrelated top; added wire marginalized; entangled top excluded | Source mixed-state extension; Goal 1 proves only pure-top cases | G3 `3-DENSITY` |
| `EQC-047-QUATERNION-REDUCED-SEPARATION` | Paper Lemma 10 and explicit contrast, `fernandez-2003.md:1077-1083,1136-1171` | source only cross | two complex reduced density matrices from quaternionic encodings | every source quaternionic pure state | reduced matrices may differ while computational diagonals agree | none | exact equality/inequality boundary unimplemented as density API | trace added top qubit | Source separation family; current library proves direct weights only | G3 `3-DENSITY` |
| `EQC-048-COMPUTATIONAL-MODEL-EQUIVALENCE` | Paper `fernandez-2003.md:18-22,146-169,1239-1241,1291`; traceability algorithm/universality rows | source only | encoded circuit/QTM/algorithm families | every encoded input and uniformly generated family | acceptance/output distribution and complexity class | phase irrelevant unless approximation quotient chosen | exact or approximate as source theorem specifies; no implementation | model-specific input/output ancillas and postprocessing must be costed | Source computational-power family; finite per-circuit simulation is insufficient | G3 `12-UNIFORMITY`, `13-REALQTM` |
| `EQC-049-PHYSICAL-SWAP-SIMULATION` | Paper `fernandez-2003.md:57,359,1289`; `Traceability.md:57,74,83` | source only same model | noncontiguous semantic gate versus emitted contiguous/swap circuit | every finite support under a declared architecture | exact operator/circuit behavior plus routing resource cost | none | exact semantic equivalence requested; construction absent | physical swap gates and any routing ancillas must be emitted/countable | Source routing comparison; Goal 1 provides semantic reindexing only | G3 `6-ROUTING` |
| `EQC-050-TOP-WIRE-PHASE-TRACKING` | Paper `fernandez-2003.md:683-687,1202,1293`; `Traceability.md:92,134` | source only cross | encoded invariant sectors and added top wire | arbitrary source states; pure versus maximally mixed top distinguished | structural phase/orbit evolution, not merely final basis probabilities | complex/quaternion state phase convention-sensitive | heuristic claim; exact replacement not yet selected | one added top wire; mixed-top phase-kickback exception | Source interpretive family requiring invariant-subspace/orbit formulation | G3 `14-STRUCTURE` |
| `EQC-051-OPERATIONAL-CONVERSE-SIMULATION` | Paper `fernandez-2003.md:1251`; algebraic witnesses in `Traceability.md:141` | source only | target circuit/model versus smaller source model | all target circuits only after a simulation relation and allowed encoders are fixed | ray, basis measurement, channel, or computational behavior must be chosen explicitly | model-specific | source inference unsupported; only algebraic nonimage is implemented | allowed ancillas/decoders unspecified in source | Source operational converse family; matrix non-surjectivity alone is insufficient | G3 `14-STRUCTURE`, `16-CHANNELS` |

## Stage 2 proof-bearing realization

The frozen rows above remain unchanged as inventory data. The following Goal 2
Stage 2 results are now checked classifications rather than provisional names.

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

These are relations on normalized representatives. They do not yet identify
quotient values; quotient equality and descended operations remain Stage 4.

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

Stage 3B adds same-space real and complex operator/circuit phase vocabulary.
It does not enlarge the frozen Goal 1 cohort. Every new stable declaration is
instead recorded in the separate Goal 2 semantic API manifest.

| Relation family | Checked meaning | Valid checked consequences | Deliberately excluded upgrade |
|---|---|---|---|
| `RealGlobalSignEq` / `ComplexGlobalPhaseEq` | `V = η • U` for one matrix-wide unit sign/phase | Input-column phase, output-row phase, projective action, and simultaneous unitary membership | Not literal equality, channel equality, or cross-model equality |
| `RealInputBasisSignEq` / `ComplexInputBasisPhaseEq` | One right phase per computational-basis input column | `BasisMeasurementEq`; preservation by a common later operator/circuit | Not all-pure-input agreement or projective action |
| `RealOutputBasisSignEq` / `ComplexOutputBasisPhaseEq` | One left phase per output row | `BasisMeasurementEq`, `PureInputBasisMeasurementEq`, and preservation by a common earlier operator/circuit | Not projective action or channel equality |
| `RealProjectiveActionEq` / `ComplexProjectiveActionEq` | Raw output rays agree for every normalized pure input | `PureInputBasisMeasurementEq`; common-later preservation; common-earlier preservation under unitarity | No output-normalization claim and no channel theorem |
| Eight `*Circuit*Eq` wrappers | The corresponding relation on `OrderedCircuit.eval` | Equivalence laws, exact-to-global lifts, and chronology-correct congruences | No gate-list, resource, schedule, embedding, or compiler equality |

The checked forward shape is therefore not one total chain:

```text
ExactOperatorEq
       |
       v
real/complex global phase
   /          |           \
  v           v            v
input phase  output phase  projective action
  |           |                 |
  v           v                 v
BasisMeasurementEq     PureInputBasisMeasurementEq
```

`OperatorPhase.ComplexRealAudit.real_unitary_strictness` and
`complex_unitary_strictness` use the unitary rotation
`[[3/5,4/5],[-4/5,3/5]]`. They prove exact equality is strictly stronger than
global phase; global phase is strictly stronger than either basis-sided phase;
input and output phase are incomparable; input phase can change a
superposed-input basis distribution; and output phase can preserve every
pure-input basis distribution while failing projective action. The zero-wire
`-1` and `I` circuit witnesses separately prove nontrivial circuit global phase
without exact circuit equality.

Projective action is meaningful without assuming the operator preserves
normalization, but the rectangular operator relation is vacuous on an empty
input index because there is no normalized input. Later converse and kernel
characterizations must state positive-cardinality/nonempty and unitarity
hypotheses explicitly. Circuit projective action is not vacuous: `BitBasis W`
is inhabited and admits normalized basis states even for zero wires. Stage 3B
publishes no quaternionic operator phase; Stage 3C owns the central-sign kernel
and the rank-one exception.

## Ambiguous wording backlog

The following prose must be adjudicated during the retrofit.  A registry label
must not silently choose one reading.

1. **Resolved in Stage 3A:** `docs/ReleaseReport.md` now says quaternionic
   state/ray phase acts on the right, not unqualified “global phase.”
2. **Resolved in Stage 3A:** correction C-006 is now titled “Quaternionic
   state/ray phase is on the wrong side” and distinguishes raw from normalized
   evidence.
3. **Resolved in Stage 3A:** `docs/Conventions.md` explicitly tags the relation
   as state/ray representative phase and excludes arbitrary operator phase.
4. `goal-1/6-SIMULATION.md:203` says a real probability equals a quaternionic
   output.  The intended comparison is with the source output basis
   probability/weight.  `goal-1/0-plan.md:129-132` has the same type-confused
   wording.
5. `goal-1/3-MATRICES.md:214-216` says “symplectic image/group isomorphism.”
   Goal 1 proves equivalence onto `complexifyUnitaryImage` plus symplectic-form
   membership, not equality with the entire symplectic group.
6. `docs/Traceability.md:104` requires the same image-membership qualification;
   it is not a converse characterization of the compact symplectic group.
7. `README.md:81`, `docs/ReleaseReport.md:56,202`,
   `docs/Architecture.md:92,329`, and `docs/Corrections.md:550` use
   “equivalent to its image.”  This is algebraic `MulEquiv`-onto-range, not
   circuit, ray, channel, or observational equivalence.
8. `README.md:143-144` says “normalized output equality.”  The implemented
   relation is equality of decoded bottom finite distributions, followed by
   event and deterministic-pushforward equality.  `goal-1/0-plan.md:164-167`
   similarly says “normalized simulation equality.”
9. `README.md:139-142` says a scheduled bridge applies “the same exact theorem”
   and remains “observably distinct.”  The actual axes are a mapped operator
   theorem and one-input computational-basis weight separation.
10. `README.md:103-105` omits the one-input scope of its unequal output-weight
    witness.  `docs/ReleaseReport.md:89-91` supplies the input scope but calls
    unequal weights “distinct normalized measurement outcomes”; the outcome
    label is the same and its probability differs.
11. `docs/ReleaseReport.md:68-69` omits the standalone quantifier: arbitrary
    source pure state and every normalized pure top state.
12. `README.md:88-90` calls basis-weight and matrix-evolution invariance
    “operational laws.”  No channel or all-measurement theorem exists in Goal 1.
13. `docs/Traceability.md:90` says “all marginals.”  The implemented result is
    finite events and deterministic maps of the bottom classical outcome
    distribution, not generic quantum partial trace.
14. `docs/Traceability.md:91` says “the same deterministic finite output
    distribution.”  Deterministic modifies the supported postprocessing map,
    not the probability distribution.
15. `docs/Architecture.md:199` calls occurrence lists
    “permutation-equivalent.”  This is list/permutation data, not semantic
    circuit equivalence.
16. `docs/Architecture.md:255` says scheduled simulation preserves “pointwise
    unitarity.”  It means local unitarity of each gate occurrence, not equality
    of pointwise state actions.
17. `README.md:79-80`, `docs/Architecture.md:88-90`, and
    `docs/Traceability.md:47,113` call Equation 63 “the same embedding.”  The
    theorem is equality only after the named simultaneous row/column reindexing
    and does not construct a second circuit translator.
18. Paper Theorem 2 at `Fernandez/fernandez-2003.md:169`, Theorem 4 at
    `Fernandez/fernandez-2003.md:855`, and the oracle criterion at
    `Fernandez/fernandez-2003.md:142` use “simulation” at different levels:
    structural gate overhead, operator embedding, and equality of classical
    outcome probabilities.
19. Paper `Fernandez/fernandez-2003.md:835,839` overstates quaternionic order
    dependence and path counts.  Goal 1 has only an existential distinguishing
    example, a sufficient commutation theorem, and an exact factorial count for
    empty precedence.
20. Paper `Fernandez/fernandez-2003.md:1239` says paths have the same
    computational power.  This means each path is claimed separately
    simulable; it does not imply that two paths have equal operators, rays,
    basis distributions, or channels.
21. Paper `Fernandez/fernandez-2003.md:661` requires a mixed top state to be
    unentangled and uncorrelated with the bottom system.  No arbitrary joint
    top/bottom density input is claimed.
22. Paper `Fernandez/fernandez-2003.md:1077-1083,1136-1171` distinguishes
    quaternionic reduced-matrix inequality from equality of computational
    diagonals; it must not be paraphrased as the real reduced-matrix theorem.
23. Paper `Fernandez/fernandez-2003.md:1180-1188` counts unrestricted image
    matrices as gates before making unsupported primitive-decomposition claims.
    Abstract same-count results are not primitive-circuit equality or runtime.
24. Paper footnote `Fernandez/fernandez-2003.md:1292` describes finite-precision
    matrix approximations, while its main theorems say “exact.”  The exact and
    approximate models require separate relations and bridge theorems.
25. Paper `Fernandez/fernandez-2003.md:1251` infers operational converse failure
    from matrix non-surjectivity.  That inference requires a chosen simulation
    relation, encoders, decoders, ancilla policy, and observation scope.

## Verification obligations before any row becomes final

For each family, Stage 1 and its later owner must:

1. expand the exact declaration/evidence arrays in the cohort JSON;
2. inspect scalar, dimension, nonempty, normalization, unitarity, and
   commutativity assumptions from the Lean signatures;
3. state the strongest candidate relation without defining it to contain the
   target theorem tautologically;
4. compile a proof-bearing wrapper through the public declaration;
5. record every weaker consequence and attempt the converse on an exact small
   example;
6. add a checked counterexample or exact obstruction for every published
   non-arrow;
7. keep source-only and Goal 3 rows visibly unimplemented; and
8. add public results to the independent Goal 2 API manifest and axiom audit
   without changing this frozen family count.
