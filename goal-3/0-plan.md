# Goal 3 — Close the Remaining *Quaternionic Computing* Frontier

## Big-Picture Objective

Starting from the completed Goal 1 release and the required Goal 2 semantic-
equivalence retrofit, tackle every paper item that remains not fully proved.
Before Goal 2, the inventory has 47 such rows.  Goal 2 owns the two ray rows
`FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY`, so the expected Goal 3
baseline is 45 rows: 26 partially formalized, 16 intentionally excluded, and 3
unresolved.  Stage 1 must recompute this baseline from the actual post-Goal-2
traceability state rather than trusting the forecast.  Close ordinary
formalization debt with proofs, corrected theorems, counterexamples, or exact
reductions; recover the paper's hard claims when they are true; and turn its
underspecified or genuinely open questions into precise models with
substantive constructive, negative, or underdetermination results.

“Tackle everything” does not mean relabeling an open question as a theorem or
pretending to settle an entire research field.  It means that no row remains
untouched or hidden: every row receives an explicit model, target, dependency
path, attempted resolution, checked evidence, and honest residual frontier.

Completion requires every post-Goal-2 partial or unresolved row—expected to be
29—to leave those statuses through a proved positive result, a proved
corrected/negative result, or a formal underdetermination theorem that settles
what follows from the source's assumptions.  The 16 expected excluded rows
must each gain
either a proved/wrapped external result or a precise formal investigation with
at least one nontrivial theorem, counterexample, or underdetermination result;
none may remain excluded merely because it is difficult.

## Authoritative Inputs

- `Fernandez/fernandez-2003.md` and `Fernandez/images/` are the paper source.
- `docs/Traceability.md` is the 101-row source-to-Lean inventory.
- `docs/Corrections.md` records the 27 current corrections and their effects.
- `docs/ReleaseReport.md`, `docs/Architecture.md`, and `docs/Conventions.md`
  describe the verified Goal 1 baseline.
- `goal-1/0-plan.md` and its completed stage reports are prior evidence, not
  work that should be repeated.
- Completed `goal-2/0-plan.md` and its stage reports are a hard prerequisite.
  Goal 3 must reuse its equality, phase, measurement, channel, embedded-
  simulation, and approximation vocabulary rather than defining competitors.
- `docs/EquivalenceClassification.md`, the frozen Goal 1 comparison cohort,
  `docs/Goal2ClassificationRegistry.json`, and the Goal 2 semantic API manifest
  are authoritative semantic inputs once Goal 2 completes. The final registry's
  seven unresolved source-only families are a separate no-skip boundary ledger;
  they do not change the immutable 47-row traceability cohort count.
- Repository-root `BUILD-PLAN.md` is authoritative for every Lean-changing
  stage.  Its narrow-module, import-hygiene, focused-build, adjacent-consumer,
  boundary-check, reporting, and fold-back rules are goal requirements.

## Non-Negotiable Constraints and No-Cheating Rules

- Never use `sorry`, `admit`, `sorryAx`, an unjustified axiom, a vacuous
  hypothesis, or a definition engineered to make a target tautological.
- Do not close a row by changing its label.  Closure evidence must address the
  source claim or a clearly documented strongest justified correction.
- A conditional theorem does not prove existence of its hypotheses.  Supplied
  compilers, schedules, density certificates, dense-generator certificates,
  and cost bounds must not be presented as constructed algorithms.
- Keep exact algebra, finite encodings, approximation, computability,
  uniformity, runtime, and complexity-class claims as separate layers.
- Never infer exact equality from rounded data or call a rounded matrix
  unitary without a proof or a certified projection/compilation step.
- Keep quaternionic columns as right modules and quaternionic state/ray phase
  on the right. In square unitary dimension at least two, genuine operator
  projective phase is limited to the proved central real-sign kernel; rank one
  instead has the proved full unit-quaternion family. Recheck dimensions,
  sector order, multiplication order, adjoints, and chronological evaluation
  at every abstraction boundary.
- Do not use commutative tensor identities over quaternions.  Physical routing
  gates must be emitted and counted; semantic reindexing is not a zero-cost
  routing implementation.
- Do not put an order on `ℍ` to reuse real/complex positive-semidefinite APIs.
  Native quaternionic mixed states require a real quadratic-form or checked
  complexification-based positivity convention.
- A finite exact gate library and an approximately dense library are different
  notions.  Precision dependence and compilation cost must be explicit.
- Noncomputable mathematical definitions may support proofs, but executable
  encoders, schedulers, compilers, and runtime theorems must have executable
  definitions and extraction/evaluation checks.
- The existing product-input ordering witness has equal computational-basis
  weights.  It is not evidence of signaling, entanglement, bit commitment, or
  a physical causality violation without the missing operational definitions.
- A source question is not completed by defining a structure.  Its stage needs
  a constructive theorem, decisive counterexample/no-go result, or formal
  proof of underdetermination in the declared model.
- Preserve the stable Goal 1 APIs.  Put experimental or heavy research
  infrastructure in narrow leaves and promote it to the public root only after
  it has a real downstream theorem and an axiom audit.
- Do not start Goal 3 implementation before Goal 2 is complete and its clean
  release evidence is recorded.  Do not duplicate or bypass Goal 2 relations
  with ad hoc local predicates.
- Keep Goal 2's cross-model relations directional and retain every encoder,
  decoder, and top-sector policy. A representative `LinearEquiv` or `Equiv` is
  not ordinary ray, circuit, channel, product-state, or all-effect equivalence.
- Record every new source correction and all transitive effects immediately.
  Preserve unrelated user changes and never track generated build artifacts.

## Current Facts

- Goal 1 pins Lean 4.31.0 and mathlib v4.31.0 at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- The pre-Goal-2 Goal 1 baseline has 44 Lean sources. Clean public-root and
  explicit audit builds pass; 186 audited endpoints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The traceability checksum is exactly 101 rows: 21 proved as stated, 33
  corrected and proved, 28 partially formalized, 16 intentionally excluded,
  and 3 unresolved.
- Those counts are the pre-Goal-2 baseline.  Goal 2 is expected to close the two
  ray rows and may legitimately settle additional semantic obligations; Goal 3
  Stage 1 must derive its actual worklist and counts after that fold-back.
- Goal 2 Stage 4C has now closed exactly those two transferred rows as proved
  as stated. The current traceability disposition is therefore 23 proved as
  stated, 33 corrected and proved, 26 partially formalized, 16 intentionally
  excluded, and 3 unresolved. The expected 45-row Goal 3 worklist is unchanged,
  but Stage 1 must still recompute it after all later Goal 2 stages finish.
- Goal 2 Stages 1--11 are implemented: its inventory, exact/measurement core,
  normalized representative phase layer, real/complex operator-phase layer,
  quaternionic operator-phase classification, and normalized ray-quotient core
  are complete. `RealRay`, `ComplexRay`, and `QuaternionRay` have exact
  scalar-correct quotient equality and exact nonempty/empty index boundaries.
  Goal 2 Stage 4B has also descended basis distributions, finite events,
  deterministic pushforwards, supplied unitary evolution, and locally-unitary
  chronological-circuit evolution for all three scalar systems, with exact
  identity and composition order laws. Stage 4C now adds the exact
  complex-to-real embedding-orbit boundary: `ComplexRay` is equivalent to
  `RealSectorOrbit`, the bottom marginal distribution is preserved, and
  canonical-column descent to ordinary `RealRay` exists only on an empty
  index. Correction C-027 records that rays precede representative embeddings.
  Therefore `FER03-D01-REBIT` and
  `FER03-FND-COMPLEX-STATE-RAY` are proved as stated and `closedByGoal2`. The
  quaternionic layer proves the side-correct five-relation vocabulary,
  raw/normalized bridge, dimension-at-least-two central-sign kernel, and full
  unit-quaternion rank-one exception. Stage 5 adds certified classical
  computational-basis behavior for real, complex, and quaternionic matrices
  and chronological circuits: equality is equality of proved all-column
  permutations, never the vacuous raw transition biconditional. On the
  certified class it is equivalent to scalar-correct input phase, output
  phase, and basis measurement; the existing preparation circuit implements
  the all-input XOR permutation while its known-ground-input theorem remains
  separately scoped. Stage 6 adds the finite real/complex physical core:
  positive-semidefinite trace-one densities, Loewner-interval effects,
  real-valued Born probabilities in `[0,1]`, exact `U * ρ * Uᴴ` evolution,
  pure/basis compatibility, and separation by genuine physical effects.
  Stage 7 adds bundled real/complex-style unitary operators and certified
  chronological circuits. Its same-space `ChannelEq` compares complete
  evolved densities for every input, `AllMeasurementEq` quantifies over every
  genuine effect, and the two relations are equivalent. On explicitly
  inhabited real and complex matrix spaces, global sign/phase, raw and
  normalized projective action, channel equality, and all-effect agreement
  have exact iff characterizations; the evaluator-backed circuit forms retain
  chronological append order and cover zero-wire circuits without a redundant
  nonempty premise. Stage 8 adds the checked implication/strictness hierarchy:
  all-pure-input basis measurement is exactly output-row sign/phase for
  rectangular real, complex, and quaternionic matrices with finite input
  indices; finite-distribution equality is exactly all finite events and all
  same-universe finite deterministic pushforwards; and the real/complex
  global/projective/channel/all-effect graph is explicit. Equal basis
  distributions still do not recover rays, and output-row phase still does not
  recover channels. Stage 9A now adds 38 generic directional cross-model
  declarations and 20 concrete representative-encoding declarations. The
  generic API keeps encoders, decoders, observation maps, and `Top`/`Input`
  policy types explicit; `ExactStateEncoding` is only a left-inverse certificate
  on the encoder image. For all four canonical columns, separate right inverses
  prove the stronger raw `ℝ`-linear equivalences and normalized-representative
  `Equiv`s. These do not identify ordinary ray spaces: complex realification
  still uses `RealSectorOrbit`. Nor do normalized `Rebit`/`Qubit` coefficient
  parameters certify product top/bottom states; the existing non-product
  witness refutes that reading. Stage 9A adds no paper correction.
  Stage 9B now adds 16 proof-bearing wrappers for all eleven assigned frozen
  operator/state/reindex/schedule/compiler families. Raw coefficient pairs are
  not pure/product top states; Equation 63 remains a named reindexing rather
  than a circuit translator; schedules and exact compilers remain supplied
  data, with no schedule choice/independence or compiler existence/synthesis/
  runtime conclusion. Stage 9B also adds no paper correction.
  Stage 9C now adds explicit full-target one- and two-added-wire decoders,
  including equality of the one-wire distribution decoder with deterministic
  pushforward by `tailBits`. It adds 18 semantic outcome wrappers allocated as
  `2 + 4 + 4 + 4 + 4`: two representative raw pointwise results, then four
  each for complex-to-real, fixed-order quaternion-to-complex, supplied-
  schedule quaternion-to-complex, and composed quaternion-to-real simulation.
  Two infrastructure aggregates separately allocate the ten decoder and eight
  postprocessing declarations. The composed quaternion-to-real decoder removes
  the outer realification wire first and the inner complexification wire
  second. Raw pointwise wrappers require no local unitarity; normalized
  distribution, event, and deterministic-pushforward results require the
  appropriate local-unitarity certificate. Schedules remain supplied data.
  Stage 9C does not add product or mixed-top semantics, partial trace, channels,
  randomized algorithms, resource bounds, or compiler/schedule construction,
  and it adds no paper correction.
  Stage 10 now supplies the rigorous semantic metric boundary. Its 169 stable
  declarations cover scoped real/complex Euclidean induced operator distance,
  native underlying-real quaternionic operator distance, directional mapped
  comparison, real/complex global phase and quaternion central-sign budgets,
  correctly right-sided normalized state-ray budgets, half-L1 total variation,
  normalized output/event/pushforward bounds, zero-budget exact bridges, and
  exact fixed-budget strictness witnesses. It introduces no quaternion matrix
  norm instance or arbitrary unit-quaternion operator phase.
  Stage 11 adds six stable strongest-scope existing-result wrappers and a
  non-root 15-endpoint audit. Its final overlay gives all 51 frozen comparison
  families and all 936 declarations exactly one checked disposition, including
  explicit axes for all ten empty families. The maintained validator and all
  generated Lean name/evidence/consumer checks pass. Stage 12 closes the final
  hierarchy gap with nine real/complex/quaternionic raw, normalized, and
  circuit projective-to-input phase arrows plus a non-root three-endpoint
  quaternionic strictness audit. The final Goal 2 release has 101 Lean sources
  including the public root, 1,284 semantic-manifest declarations, 168
  resolving consumers, 365 direct manifest audit labels, 551 root axiom
  commands, and exact root/local axiom union `propext`, `Classical.choice`, and
  `Quot.sound`. The root parser reports 548 nonempty plus three axiom-free
  blocks; the existing-result and projective-input parsers report 15 and three
  nonempty blocks. Clean/default/integrated/exhaustive builds complete 2,782,
  2,775, 2,777, and 2,787 jobs. Stage 11 corrected two Stage 10 strictness entries that were
  genuinely printed in the root audit but mislabeled transitive in manifest
  metadata. The corrected first-1,269 structural hash is
  `c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229`
  and the preserved first-1,275 hash is
  `bbea85679b6e8425f398f8ab984736472450a440cad984315d4dbd2c62def45f`;
  the full-1,284 hash is
  `a372726bee9bf0dff73bc2100db4196f501395491ba7b5e2e95e19efbcaed983`;
  the frozen Goal 1 cohort checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
  Goal 2 is now a satisfied prerequisite; Goal 3 may begin at its first stage.
  Finite scalar encodings,
  rounding/code-to-value certification, accumulated circuit error, approximate
  compiler/synthesis construction, runtime, and uniformity remain assigned to
  Goal 3 rather than Stage 10. Native
  quaternionic density/channel semantics, partial trace, Kraus maps,
  instruments, mixed-top or phase-kickback semantics, cross-model channel
  equality, and randomized/resource upgrades also remain Goal 3 work.
- The main scalar, matrix, state, placement, ordered-circuit, exact simulation,
  outcome, Equation 63, and finite resource results are already complete.
- Mathlib has projectivization and alternating-map infrastructure, matrix
  positive-semidefiniteness over ordered/`RCLike` scalars, permutation
  matrices, and Turing-machine definitions.  It does not provide a ready
  quantum density/partial-trace library, Pfaffian theorem, quantum-channel
  library, or BQP framework.
- Mathlib's `LinearAlgebra/SymplecticGroup.lean` still lists determinant one as
  a TODO and proves only that the determinant is a unit.
- The determinant sign is nevertheless expected to be provable algebraically:
  wedge the canonical symplectic 2-form to a nonzero top alternating form,
  combine symplectic preservation with the determinant action on top forms,
  and cancel.  A Pfaffian covariance proof is the fallback.
- The paper's missing logarithmic-depth construction has a concrete candidate.
  A two-rail Bell-basis splitter can intertwine one logical real complex
  structure `J` with `J` acting on either output rail.  A balanced tree can
  supply one phase rail per gate occurrence and later uncompute it.  This must
  be checked against the library's exact sign convention; it is phase-reference
  encoding, not cloning.
- The advertised bounded generic synthesis is false or underspecified under
  standard readings.  A finite discrete library has only finitely many words
  under a fixed length bound, while a paired diagonal symplectic phase family
  already gives infinitely many targets inside the complexification image.  A
  corrected constructive synthesis is expected to scale like the dense matrix
  size, not `O(2^d)` without further structure.
- Exact finite universality is impossible for a continuous unitary group;
  approximate/dense universality is the meaningful interpretation.  A finite
  quaternionic dense generator remains a substantial mathematical target, not
  a consequence of the existing conditional compiler interface.
- The ten explicit source questions, bit-commitment sketch, physicality prose,
  and destructive-interference explanation are research prompts rather than
  supplied theorem statements.  They require new operational models.

## Permitted Closure Outcomes

Every row must finish Goal 3 with one of the following evidence-backed
outcomes, recorded in traceability and the new closure ledger:

1. **Proved:** a faithful formal statement is proved.
2. **Corrected and proved:** an error or missing hypothesis is documented and
   the strongest useful corrected result is proved.
3. **Refuted:** a faithful formal reading is disproved by a theorem or checked
   counterexample, with a nearby correct result supplied.
4. **Resolved under explicit assumptions:** both the assumptions and the
   theorem are formal, and no existence/runtime conclusion is inferred beyond
   them.
5. **Formally underdetermined:** two incompatible extensions satisfy all
   source-supplied constraints, proving that the prose does not determine a
   unique mathematical claim.
6. **Open after a completed case study:** allowed only for a genuine source
   research question that was already intentionally excluded, after a precise
   model and a nontrivial formal result have been delivered.  This outcome may
   not be used for any row that is partial/unresolved at the post-Goal-2 Goal 3
   baseline.  The
   remaining question must receive a new frontier ID and exact theorem target.

The six labels above are closure-ledger outcomes, not silent replacements for
the existing five canonical traceability statuses.  Stage 1 must encode this
mapping: an originally partial/unresolved row may finish only as **proved as
stated** or **corrected and proved**, with refutation, conditional repair, or
underdetermination recorded inside the status narrative and backed by a Lean
theorem.  An originally excluded research question may remain **intentionally
excluded** only after its required formal case study; any residual open theorem
gets a new ID.  The checker must enforce this policy.

## Exact Closure Ledger

The table assigns the expected 45 post-Goal-2 rows exactly once.  Stage 1 must
replace this forecast with the actual post-Goal-2 worklist and verify its
checksum mechanically before implementation begins.  Any additional row
settled by Goal 2 is removed with an explicit dependency record; no row may
simply disappear.

Expected prerequisite dispositions:

| Goal 2 owner | Transferred rows | Required Goal 2 disposition |
|---|---|---|
| Phase/ray classification | `FER03-D01-REBIT`; `FER03-FND-COMPLEX-STATE-RAY` | `closedByGoal2`, with quotient/evolution/outcome theorems and updated canonical traceability status |

The final Goal 2 classification registry also carries seven source-only family
boundaries into Goal 3. They overlap the mathematical work below but are not
additional traceability rows and must not be added to the 47/45 counts:

| Registry family | Goal 3 owner | Required boundary |
|---|---|---|
| `EQC-045-NORM-PRESERVER-CONVERSES` | `4-FOUNDATIONS` | Scalar-specific linear/antiunitary norm-preserver converses with exact hypotheses |
| `EQC-046-MIXED-TOP-OBSERVATIONAL` | `3-DENSITY` | Joint density, product/no-correlation top hypothesis, partial trace, and decoded marginal |
| `EQC-047-QUATERNION-REDUCED-SEPARATION` | `3-DENSITY` | Pure-state quaternionic reduced-matrix inequality separated from diagonal agreement |
| `EQC-048-COMPUTATIONAL-MODEL-EQUIVALENCE` | `12-UNIFORMITY`; `13-REALQTM` | Uniform encoders/decoders, acceptance behavior, error, and resource overhead |
| `EQC-049-PHYSICAL-SWAP-SIMULATION` | `6-ROUTING` | Physical swap network, exact denotation, architecture, and routing cost |
| `EQC-050-TOP-WIRE-PHASE-TRACKING` | `14-STRUCTURE` | Convention-correct invariant-subspace/orbit formulation with explicit decoded observables |
| `EQC-051-OPERATIONAL-CONVERSE-SIMULATION` | `14-STRUCTURE`; `16-CHANNELS` | Explicit operational relation with allowed encoders, ancillas, decoders, marginals, and tests before any converse separation |

| Stage | Traceability rows | Baseline | Required direction |
|---|---|---:|---|
| 3-DENSITY | `FER03-R-PARTIAL-TRACE-BLOCK-SUM`; `FER03-R-ARBITRARY-TOP-REBIT`; `FER03-Q-ARBITRARY-TOP-QUBIT` | 3 partial | Joint density matrices, partial trace, and mixed product/no-correlation top densities |
| 4-FOUNDATIONS | `FER03-FND-LINEAR-ISOMETRY-UNITARY`; `FER03-FND-FINITE-DIM-COMPLETE`; `FER03-FND-REAL-PRESERVERS-ORTHOGONAL`; `FER03-INT-NOT-NPLUS1-REBITS` | 2 partial + 2 excluded | Close background facts and prove the exact linear-dimension limitation |
| 5-DETERMINANT | `FER03-T05-QUATERNION-COMPLEXIFICATION-GROUP` | 1 partial | Prove the missing `det = 1` branch and the corrected special-unitary image theorem |
| 6-ROUTING | `FER03-FND-ARBITRARY-WIRE-ROUTING`; `FER03-R-TOPO-SORT-COMPLEXITY`; `FER03-Q-CUT-POSET` | 3 partial | Counted swap routing, verified topological sort, and corrected temporal cuts |
| 7-PHASEFANOUT | `FER03-R-REAL-GATE-OPTIMIZATION`; `FER03-R-MULTI-ANCILLA-LOG-DEPTH` | 1 partial + 1 unresolved | Optimized real gates and an exact logarithmic-depth construction or faithful-model class-wide no-go |
| 8-ENCODING | `FER03-R-LOCAL-GATE-COST`; `FER03-R-PREPROCESSING-COST`; `FER03-RES-UNIFORM-CIRCUIT-WITHOUT-UNIVERSAL-SET`; `FER03-RES-EXPLICIT-MATRIX-ARITY` | 4 partial | Executable codes, translators, validators, and bit/work bounds |
| 9-APPROX | `FER03-FND-FINITE-PRECISION` | 1 partial | Certified rounding and accumulated state/outcome error bounds |
| 10-SYNTHESIS | `FER03-RES-GENERIC-DECOMPOSITION`; `FER03-RES-CONSTANT-D`; `FER03-RES-ARBITRARY-D-OVERHEAD` | 2 partial + 1 unresolved | Refute unsupported bounds and instantiate a corrected explicit synthesis theorem |
| 11-UNIVERSALITY | `FER03-RES-QUATERNIONIC-UNIVERSAL-SET` | 1 unresolved | Prove one width-independent finite bounded-arity schema dense at every quaterbit width, or a model-wide no-go |
| 12-UNIFORMITY | `FER03-D02-REAL-ALGORITHM`; `FER03-D05-QUATERNIONIC-ALGORITHM`; `FER03-R-COMPUTATIONAL-UNIVERSALITY`; `FER03-RES-ABSTRACT-LITTLE-OVERHEAD`; `FER03-INT-PREFERRED-PATH-BQP` | 5 partial | Encoded uniform families, runtime, randomized outcomes, and corrected class containment |
| 13-REALQTM | `FER03-T01-BERNSTEIN-VAZIRANI-REAL-QTM` | 1 excluded | Independently state and prove the external approximate-real QTM result or its strongest verified correction |
| 14-STRUCTURE | `FER03-FND-ANY-HILBERT-SCALARS`; `FER03-R-PHASE-TRACKING-INTERPRETATION`; `FER03-INT-QUATERNION-PHASE-QUBIT` | 3 partial | Exact complex-structure and subsystem characterizations |
| 15-MULTIPATH | `FER03-INT-DESTRUCTIVE-INTERFERENCE-CAUSE`; `FER03-OPEN-ALL-EVALUATION-PATHS`; `FER03-OPEN-PATH-WEIGHTS`; `FER03-OPEN-PATH-INTERFERENCE`; `FER03-OPEN-BEYOND-QUANTUM-SPEEDUP` | 5 excluded | Classical-mixture and coherent-path models, counterexamples, and underdetermination/complexity results |
| 16-CHANNELS | `FER03-INT-FREE-NONLOCAL-CORRELATION`; `FER03-OPEN-CHANNEL-CAPACITY`; `FER03-OPEN-REBIT-INFORMATION-THEORY` | 1 partial + 2 excluded | Native quaternionic mixed/channel semantics, witness classification, and proved comparisons or obstructions |
| 17-PROTOCOLS | `FER03-INT-BIT-COMMITMENT`; `FER03-OPEN-QUATERBIT-TELEPORTATION`; `FER03-OPEN-COMMUNICATION-COMPLEXITY` | 3 excluded | Formal protocols and a proof, attack, comparison, or underdetermination result for each scoped question |
| 18-PHYSICALITY | `FER03-INT-RULE-OUT-PHYSICALITY` | 1 excluded | A conditional information-theoretic no-go theorem or formal underdetermination, never a claim about Nature by definition |
| 19-ALGEBRAS | `FER03-OPEN-OTHER-SCALARS`; `FER03-OPEN-ALGEBRAIC-COMPLEXITY-PICTURE` | 2 excluded | Concrete octonion/finite-field interface results and a precise algebraic-model comparison |

Forecast checksum: partial `3+2+1+3+1+4+1+2+5+3+1 = 26`; excluded
`2+1+5+2+3+1+2 = 16`; unresolved `1+1+1 = 3`.

## Dependency Shape

```text
1-REBASE -> 2-SEMANTICS
2-SEMANTICS
  ├─ 3-DENSITY -> 14-STRUCTURE -> 15-MULTIPATH
  │                    └────────> 16-CHANNELS -> 17-PROTOCOLS -> 18-PHYSICALITY
  ├─ 4-FOUNDATIONS -> 5-DETERMINANT
  ├─ 6-ROUTING -> 7-PHASEFANOUT
  └─ 8-ENCODING -> 9-APPROX -> 10-SYNTHESIS -> 12-UNIFORMITY
                                      └──────> 11-UNIVERSALITY
8-ENCODING + 9-APPROX -> 13-REALQTM
3-DENSITY + 14-STRUCTURE -> 16-CHANNELS
4-FOUNDATIONS + 14-STRUCTURE -> 19-ALGEBRAS
all stages -> 20-RELEASE
```

Every mathematical Goal 3 workstream therefore has `2-SEMANTICS` as a
transitive prerequisite; the additional arrows record its domain-specific
dependencies.

## Mandatory Compiling Milestones

The numbered stages are closure workstreams, not permission to batch several
library-sized changes into one unverified edit.  Before implementing any broad
workstream below, create the listed sub-stage reports (for example
`6A-SWAPS.md`) and complete them independently.  The umbrella checkbox remains
open until every milestone and its source-facing consumer is verified.

| Workstream | Required milestones and independent exits |
|---|---|
| 6-ROUTING | `6A-SWAPS`: emitted adjacent-swap network and semantics; `6B-TOPOSORT`: in-memory executable sorter/cycle certificate and work count; `6C-CUTS`: order-ideal/maximal-chain theorems consuming schedules |
| 7-PHASEFANOUT | `7A-REALOPT`: independent real-gate optimization; `7B-SPLITTER`: two-rail orthogonal/intertwining smoke theorem; `7C-RAILTREE`: balanced code and resource arithmetic; `7D-MULTITOPSIM`: circuit/operator/state/outcome simulation and depth theorem |
| 8-ENCODING | `8A-SCALARCODE`: exact component codecs/round trips; `8B-CIRCUITCODE`: gate/DAG/schedule codecs and validators; `8C-CODECOST`: executable translations plus bit/output/work bounds |
| 10-SYNTHESIS | `10A-GATEMODELS`: exact/approximate primitive semantics and image-internal no-go; `10B-FACTOR`: mathematical two-level factorization; `10C-LOCALIZE`: bounded-local decomposition/lower bound; `10D-COMPILER`: encoded standard-library compiler and simulation consumer |
| 11-UNIVERSALITY | `11A-DEFINITIONS`: exact/dense/kernel-correct notions; `11B-LIE`: fixed-dimension Lie generation; `11C-ALLWIDTH`: one finite bounded-arity schema across all widths; `11D-DENSITY`: closure theorem and public certificate |
| 12-UNIFORMITY | `12A-FAMILIES`: encoded generators/postprocessors; `12B-RAMCOST`: executable translation and explicit work proofs; `12C-TMBRIDGE`: machine-level polynomial bridge; `12D-BQP`: library-relative then standard-library bounded-error containment |
| 13-REALQTM | `13A-SOURCE`: primary statement audit; `13B-QTMMODEL`: finite-time semantics; `13C-STABILITY`: approximation/error theorem; `13D-SIMULATOR`: real-amplitude construction and overhead |
| 16-CHANNELS | `16A-QDENSITY`: native quaternionic positivity/closure; `16B-CHANNELS`: channels/instruments/marginals; `16C-WITNESS`: exact operational classification; `16D-CAPACITY`: scoped capacity/rebit case study |
| 17-PROTOCOLS | `17A-TELEPORT`: protocol/cost theorem; `17B-COMMUNICATION`: communication model/comparison; `17C-COMMITMENT`: faithful sketch completion and security/attack/underdetermination result |
| 19-ALGEBRAS | `19A-OCTONIONS`: nonassociative model/counterexample; `19B-FINITEFIELD`: probability obstruction/repair data; `19C-ALGCOMPLEXITY`: shared-interface comparison theorem |

If current facts reveal another workstream crossing dependency layers, split it
in `0-plan.md` before implementation rather than stretching one stage report.

## Success Metrics and Verification Requirements

- A machine-checked ledger accounts for the immutable 47-row pre-Goal-2 cohort:
  each ID is either `closedByGoal2` with evidence or appears exactly once in
  the Goal 3 worklist.  The expected Goal 3 worklist has 45 IDs.
- Every row partial/unresolved at the Goal 3 baseline—expected 29—leaves those
  canonical statuses.  Negative, conditional, or underdetermination
  resolutions require a proved theorem with precise scope; residual questions
  receive new IDs.
- Every originally excluded row has new formal evidence or a completed formal
  case study; changing documentation alone is insufficient.
- All public mathematical results compile with no holes or project axioms and
  are included in `QuaternionicComputing/AxiomAudit.lean`.
- Executable claims have `#eval`/test fixtures and do not obtain computability
  from classical choice or noncomputable decoders.
- Cost theorems count input/output bit length, arithmetic/model assumptions,
  schedules, routing gates, approximation precision, and primitive synthesis
  at the layer where each matters.
- Focused leaf and adjacent-consumer builds pass at each stage.  Any public
  root/high-fanout change triggers the broader builds required by
  `BUILD-PLAN.md`.
- Final verification includes a clean `lake build`, explicit
  `lake build QuaternionicComputing.AxiomAudit`, warning-as-error checks,
  proof-hole/project-axiom/unsafe/opaque scans, forbidden-shortcut scans,
  traceability checksum, downstream import smoke test, and `git diff --check`.

## Stages

### 1-REBASE

#### Big Picture Objective

Freeze an exact, executable definition of the remaining work before changing
mathematics or statuses.

#### Detailed Implementation Plan

- Refuse to begin until Goal 2 is marked complete and its build, audit, frozen
  cohort-registry check, semantic API-manifest check, traceability fold-back,
  and downstream smoke evidence are present.
- Create `docs/RemainingWork.md` accounting for the immutable 47-row cohort:
  mark each row `closedByGoal2` with evidence or assign it to Goal 3 with its
  post-Goal-2 status, dependencies, intended closure outcome, primary route,
  fallback, and verification witness.
- Add a separate seven-family section for `EQC-045`--`EQC-051`, preserving the
  Goal 2 registry IDs, owners, exact obstructions, and closure evidence without
  counting them as seven additional traceability rows or silently merging them.
- Re-read the source sections and relevant citations for each hard/external
  item; use primary literature and record versions rather than relying on the
  paper's summaries.
- Add a checker that parses traceability, recomputes current status/correction/
  audit counts, verifies every pre-Goal-2 ID is closed by Goal 2 or assigned
  exactly once to Goal 3, validates canonical-status/closure-outcome mapping,
  and enforces new IDs for residual open work.
- Recompute the Lean source/module count, public-root closure, executable axiom-
  audit endpoint count, correction count, and downstream import surface after
  Goal 2; do not retain Goal 1 release numbers as current evidence.
- Record clean Goal 1 and Goal 2 build/audit baselines and inspect current diffs
  before any feature work.

#### Completion Requirements

- All 47 cohort IDs are accounted for exactly once.  Forecast Goal 3 totals are
  45 rows with categories 26/16/3, but the checker-derived post-Goal-2 totals
  replace the forecast.
- All seven unresolved Goal 2 registry families are also assigned exactly once
  to the owners above and linked to overlapping traceability rows without
  changing the 47/45 ledger totals.
- Every row has a stage, concrete success test, and non-tautological fallback.
- The closure-outcome taxonomy is mapped unambiguously to the canonical
  traceability statuses and enforced by the checker.
- All correction dependencies present after Goal 2 are linked where relevant,
  including C-001–C-026 and every correction added during Goal 2.
- Baseline builds, audit, scans, and diff state are recorded in `1-REBASE.md`.

### 2-SEMANTICS

#### Big Picture Objective

Integrate Goal 2's rigorous comparison vocabulary into every remaining Goal 3
workstream before adding new mathematics.

#### Detailed Implementation Plan

- Import the narrow Goal 2 leaves for exact, phase, basis, distribution,
  channel/all-effect, embedded-simulation, and approximate relations.
- Reuse the Stage 9A directional certificate API, Stage 9B proof-bearing
  wrappers, and Stage 9C decoded-outcome API at their actual strength:
  generic left-inverse encodings remain directional, while the four canonical
  coordinate maps separately expose representative `LinearEquiv`/`Equiv`
  values. Stage 9B operator/state wrappers retain raw coefficient encoders,
  explicit reindexing/added wires, supplied schedules, and supplied compilers.
  Stage 9C supplies explicit full-target one/two-wire decoders, decoded raw
  point weights, and normalized distribution/event/pushforward results; the
  one-wire decoder is exactly pushforward by `tailBits`, and composed
  quaternion-to-real decoding removes the outer realification wire before the
  inner complexification wire. Its schedules are still supplied, and its
  normalized results retain their local-unitarity assumptions. Never
  substitute any of these results for a ray, channel, product/mixed-state,
  partial-trace, compiler-existence, synthesis, randomized, resource, or
  runtime theorem.
- Map every Goal 3 stage target to the strongest applicable relation and input/
  observation scope before implementation; flag claims needing a genuinely new
  relation rather than using vague equality prose.
- Add downstream `example`/`#check` smoke consumers showing that the existing
  central simulations, ordering witnesses, and distribution results inhabit
  their public Goal 2 classifications. Do not create duplicate wrapper
  theorems; add a new wrapper only when a later Goal 3 result introduces
  genuinely new semantics.
- Record how Goal 2 closed the two transferred ray rows and remove any duplicate
  quotient work from Goal 3.

#### Completion Requirements

- Every remaining stage names its comparison relation, phase convention, input
  scope, observation scope, exact/approximate status, and encoding/marginal
  policy.
- No Goal 2 definition is duplicated or weakened by a local Goal 3 predicate.
- Downstream smoke consumers compile against the public Goal 2 API and all
  transferred rows have explicit `closedByGoal2` evidence.
- Focused semantic-wrapper builds, public-root build, classification checker,
  and axiom spot-audit pass.

### 3-DENSITY

#### Big Picture Objective

Build the finite real/complex mixed-state and partial-trace layer needed to
prove the paper's arbitrary mixed top-wire statements.

#### Detailed Implementation Plan

- Extend Goal 2's finite real/complex density/effect and unitary-channel core;
  do not redefine its `DensityMatrix`, `Effect`, `ChannelEq`, or
  `AllMeasurementEq` APIs.  Add narrow `State/PartialTrace.lean` and
  `State/MixedTop.lean` leaves with convex mixtures, partial trace, and the
  simulator-specific mixed-top constructions.
- Define partial trace as an explicit finite diagonal-block sum on product
  indices and prove Hermiticity, positivity, trace preservation, linearity,
  tensor-product, and pure rank-one laws.
- Prove the explicit equivalence between the simulator's `AddedWire`/sum basis
  and the product index used by partial trace, so the generic API consumes the
  existing embedded states rather than a parallel toy representation.
- Express the realification and complexification top encodings as frames and
  prove bottom distributions for every supplied joint density satisfying an
  explicit tensor-product/no-correlation top hypothesis, including maximally
  mixed and off-diagonal top-density examples. Do not reuse a normalized
  `Rebit`/`Qubit` coefficient parameter as if it were that joint-state
  certificate.
- Keep native quaternionic density matrices out of this stage; they require the
  separate positivity convention in Stage 16.

#### Completion Requirements

- The generic block-sum partial trace theorem is proved, not just the existing
  rank-one special case.
- Both arbitrary mixed-top claims quantify over actual density matrices, not
  only pure states or ensemble syntax.
- Tensor-product/no-correlation hypotheses are explicit and proved of the
  actual joint density; no result is generalized to entangled top/bottom
  inputs.
- The three assigned rows close with focused builds, numerical sanity checks,
  traceability updates, and audited axioms.

### 4-FOUNDATIONS

#### Big Picture Objective

Close the finite-dimensional background facts and replace the paper's
`n+1`-rebit overreach with an exact linear-dimension theorem.

#### Detailed Implementation Plan

- Locate and wrap the strongest matching mathlib completeness and
  norm-preserving-linear-map results; prove missing finite matrix equivalences
  between norm preservation and unitarity.
- Prove that a complex-linear transformation preserving the real subspace has
  real entries and that unitary preservation then gives an orthogonal real
  matrix.
- Compare real dimensions of quaternionic `N`-columns and `(2N)`-dimensional
  real columns and prove there is no injective real-linear state-vector map of
  the required `n+1`-rebit dimension when `N > 0`.
- Document that this rules out only faithful real-linear vector embeddings,
  not every conceivable operational simulation or nonlinear encoding.

#### Completion Requirements

- The two background exclusions become exact imported/wrapped or newly proved
  theorems with matching assumptions.
- The real-preserver characterization is bidirectional at the matrix level.
- The dimension no-go theorem has explicit nonzero hypotheses and is not sold
  as a universal simulation lower bound.
- All four assigned rows and C-017 are updated with builds and axiom evidence.

### 5-DETERMINANT

#### Big Picture Objective

Prove that the complexification of every quaternionic unitary has determinant
one and finish the corrected special-unitary group theorem.

#### Detailed Implementation Plan

- Add a proof leaf such as `Matrix/SymplecticDeterminant.lean` rather than
  expanding the existing high-fanout determinant core.
- Define the canonical symplectic 2-form from `Matrix.J`, recursively wedge it
  using `AlternatingMap.domCoprod`, and compute a nonzero value of its top
  exterior power on the standard basis, including rank zero.
- Prove that a symplectic matrix preserves this top form while its action on a
  top alternating form scales by `det`; cancel the nonzero value to prove a
  reusable `symplectic_det_eq_one` theorem.
- If the alternating-map route is structurally blocked, implement the minimal
  Pfaffian API and covariance theorem instead.  A fallback is not completion
  until one route proves the sign.
- Apply the theorem to `Quaternion.complexify_mem_symplectic`, export the
  special-unitary result, and reconcile the image/equivalence documentation.

#### Completion Requirements

- `det (Quaternion.complexify U) = 1` compiles for every finite quaternionic
  unitary, including the empty-index edge case.
- The proof does not use connectedness, a Study determinant, or a Pfaffian as
  an axiom/opaque placeholder.
- Theorem 5, C-004, all dependents, public exports, and the axiom audit are
  updated; the previous `±1` theorem remains as a reusable weaker fact.
- Focused and adjacent group/simulation builds pass.

### 6-ROUTING

#### Big Picture Objective

Turn semantic placement and supplied schedules into explicit, counted routing
and finite-DAG algorithms, while correcting the paper's temporal-cut claim.

#### Detailed Implementation Plan

- Add wire-permutation and swap leaves.  Prove that adjacent two-wire swap is a
  real `0–1` unitary placed gate over every supported coefficient star ring.
- Implement an adjacent-swap network on `Fin n`, prove its permutation/evaluator
  semantics and a quadratic bound, then route a noncontiguous support to
  canonical slots, apply the local gate, and unroute.
- Lift routing gatewise to circuits with exact count/arity/depth statements and
  a quaternionic noncontiguous example.
- Define in-memory finite decidable precedence DAGs, executable topological
  sorting that returns a `LegalSchedule` or cycle witness, and an explicit work
  counter.  Their byte/string serialization belongs to Stage 8.
- Define temporal cuts as order ideals.  Prove that prefixes of a legal schedule
  form a maximal chain and characterize the converse; disprove or correct any
  claim that one sort totally orders every cut.

#### Completion Requirements

- Physical swaps appear in emitted circuits and resource counts; no semantic
  equivalence is charged as zero gates.
- Topological sort is executable and its soundness/completeness and stated work
  bound are proved.
- Cut/schedule theorems state exactly which cuts are ordered.
- All three rows close with focused builds, `#eval` fixtures, routing examples,
  and boundary scans.

### 7-PHASEFANOUT

#### Big Picture Objective

Recover or decisively delimit the paper's missing multi-top logarithmic-depth
complex-to-real simulation and implement the real-gate optimization.

#### Detailed Implementation Plan

- Define the exact real complex-structure matrix `J` used by `Matrix.realify`.
  Construct and prove orthogonal a two-rebit splitter whose fresh-ancilla
  restriction maps the logical basis to the appropriate Bell basis and
  intertwines logical `J` with `J` on either output rail.
- Recursively build a balanced splitter tree with
  `m = 2^ceilLog2(max 1 s)` rails, prove `m < 2s` for `s > 0`, and prove every
  rail realizes the same logical complex structure on the code space.
- Assign distinct rails to gate occurrences, lift each source support layer,
  and prove the translated gates preserve the code.  Reverse the splitter tree
  to decode.
- Target exact resources: width `n+m`, gate count `s+2(m-1)`, translated local
  arity `d+1`, splitter arity two, and support depth
  `t+2*ceilLog2(max 1 s)`, adjusting statements if checked edge cases require.
- Add an optimized branch for provably real source gates that acts only on
  bottom wires and prove its evaluator and improved resource facts.
- If the candidate fails, isolate the first false intertwining/composition
  obligation, prove a no-go for that architecture, and continue to the next
  explicit encoding.  A candidate-specific failure does not refute the paper's
  existential claim, and falling back to the one-shared-wire theorem does not
  resolve it.

#### Completion Requirements

- An exact operator/state/distribution theorem and explicit ancilla tradeoff
  prove the corrected logarithmic-depth claim.  A negative completion requires
  a theorem ruling out the claim under a faithful explicit resource model, not
  merely failure of the proposed splitter.
- The construction is described as phase-reference encoding, never cloning.
- Empty circuits, one gate, non-power-of-two gate counts, and mixed real/complex
  gate lists are tested.
- C-015 and both assigned rows close with resource proofs, focused/full
  affected builds, and axiom audit entries.

### 8-ENCODING

#### Big Picture Objective

Give circuits, gates, schedules, and exactly representable scalars executable
finite descriptions with honest bit and work costs.

#### Detailed Implementation Plan

- Add an `Encoding/` layer for bit strings, dyadic/rational real components,
  complex/quaternion tuples, dense gates, supports, circuit DAGs, schedules,
  and deterministic/randomized postprocessing descriptions.
- Supply decoders, round-trip theorems, Boolean well-formedness/unitarity or
  certificate validators where decidable, and malformed-input rejection.
- Implement code-level realification, complexification, routing, scheduling,
  and exact gate-list translation; prove decoding commutes with semantic maps.
- Define bit length, read/write work, and output-size counters.  Prove bounds
  that include scalar component lengths, indices, supports, and all emitted
  entries rather than only matrix dimension.
- Add `#eval` fixtures for valid and invalid small circuits.

#### Completion Requirements

- No function claims to computably encode an arbitrary real number.  Exact
  codes cover a declared countable scalar class; general scalars pass to Stage
  9 approximation certificates.
- Translation algorithms are executable and preserve evaluator semantics on
  decoded exact inputs.
- Local/preprocessing/description bounds follow from the actual code and work
  counters, not supplied constants alone.
- All four assigned rows close with focused builds, evaluation tests, and
  documentation of the encoding model.

### 9-APPROX

#### Big Picture Objective

Bridge arbitrary mathematical gates to finite descriptions with quantified
error, extending Goal 2's metric comparison vocabulary without weakening the
exact Goal 1 theorems.

#### Detailed Implementation Plan

- Reuse Goal 2's `operatorDistance`/approximate-comparison relations, norm
  conventions, and basic observable bounds.  Add encoded scalar, matrix,
  circuit, state, and distribution approximation leaves with certified
  code-to-value error and accumulation relations.
- Prove componentwise-to-matrix bounds, submultiplicative/telescoping circuit
  error, normalized-state error, basis-event error, and total-variation bounds.
- Distinguish rounded matrices from exact unitary primitive circuits.  Add a
  certified unitary approximation/compiler interface and prove the guarantees
  only from its certificate.
- Provide two deliberately separate APIs: an executable quantizer for encoded
  Cauchy/approximation oracles (and rational/dyadic inputs), and a semantic
  existential approximation certificate for arbitrary Lean `ℝ` values.  There
  is no executable function from arbitrary `ℝ` to finite code.
- Implement precision budgeting across gates and show how requested output
  tolerance determines per-gate tolerances and code size.
- Reconcile the paper's finite-precision footnote with the exact simulation
  theorems rather than altering those theorems.

#### Completion Requirements

- At least one executable encoded-oracle approximation family supplies codes
  with a proved convergence/error theorem; arbitrary mathematical reals use
  only the separate semantic existence interface.
- No theorem concludes exact equality or exact unitarity from rounding.
- Accumulated error includes every gate and produces an observable-distribution
  guarantee suitable for Stage 12.
- `FER03-FND-FINITE-PRECISION` and C-024 close with focused builds and audits.

### 10-SYNTHESIS

#### Big Picture Objective

Settle the unsupported generic decomposition bound and replace it with proved
results in explicit primitive-gate models.

#### Detailed Implementation Plan

- Define finite discrete, continuously parameterized local, exact, and
  approximate gate-library models before counting elementary gates.
- Prove that a finite discrete library has only finitely many words of length
  at most `K`; use the paired symplectic family
  `diag(exp(i*θ), exp(-i*θ))` (and identity blocks), explicitly exhibited as
  complexifications of diagonal unit quaternions, to refute bounded exact
  generic generation inside the actual target image.
- Construct a reusable exact two-level/QR-style decomposition with a checked
  `O(m^2)`-scale count for `m × m` unitaries.  Classify this mathematical
  continuous-parameter factorization as noncomputable unless its parameters
  are encoded, then give the strongest justified localization to one-/two-
  qubit primitives with explicit arity and parameter assumptions.
- Prove a formal parameter-dimension lower bound for continuously parameterized
  bounded-local gates.  If the first manifold route is disproportionate, seek
  a smaller algebraic/smooth-dimension lemma or split out its prerequisite; do
  not mark the stage complete while this remains a faithful unresolved reading
  of the source claim.
- Also prove a two-model underdetermination theorem if needed: unrestricted
  full-arity primitives trivialize the count, while a finite exact library
  cannot cover the target.  This diagnoses the missing primitive semantics but
  does not replace the bounded-local lower bound when that is the intended
  reading.
- Instantiate `ExactGateCompiler` where the encoded exact model permits it and
  build an epsilon-dependent compiler into one declared standard finite
  complex gate library, with semantic and runtime/precision certificates for
  Stage 12.  Propagate corrected count/depth bounds to Table 1.

#### Completion Requirements

- The paper's `2^(d+1)` statement is either proved under a faithful explicit
  gate model or formally refuted; ambiguity is not retained as “unresolved.”
- A constructive replacement compiler is implemented and semantically proved,
  not merely postulated as structure data.
- The standard finite-complex-library approximation compiler needed by Stage
  12 is either constructed here or assigned to an explicit new prerequisite
  stage; standard-gate BQP cannot rely on the QR theorem alone.
- Constant-`d` and arbitrary-`d` consequences state exact dependence on matrix
  size, precision, primitive model, and serialization.
- The three assigned rows and C-013/C-014/C-019 close with focused builds,
  small decompositions, and end-to-end compiled simulations.

### 11-UNIVERSALITY

#### Big Picture Objective

Resolve the conjectured finite quaternionic universal gate set under a precise
approximate/dense meaning.

#### Detailed Implementation Plan

- Reuse Goal 2's operator-action kernel, right-phase, and approximation
  conventions.  Define exact word generation, topological closure, and epsilon
  generation in its operator norm on the compact symplectic matrix group, plus
  local placement of one finite bounded-arity gate schema whose labels do not
  depend on total circuit width.
  Quotient operators only by a rigorously proved kernel of their action on
  right-phase rays (expected at most the central `±I`), never by arbitrary unit
  quaternion right phase.
- Prove exact finite universality impossible for nontrivial continuous target
  groups by countability or the stronger bounded-word result from Stage 10.
- Investigate a concrete approximate candidate: a finite complex universal
  library embedded in `ℍ`, one irrational quaternionic-direction rotation,
  and inverses/entangling placement.
- Formalize the Lie-algebra decomposition of the compact symplectic target,
  prove that conjugates of the added quaternionic direction generate the
  missing complement, and use a verified compact-Lie closure theorem or build
  the needed special case to prove density.
- Lift the fixed-arity generators by placement and prove density in every
  `Sp(2^n)` from one width-independent schema, with any small-width base cases
  or exceptions stated explicitly.  A fixed-`n`, `n`-dependent dense set is
  only an intermediate theorem and does not resolve the source claim.
- Export a dense-generator certificate and only then connect it to approximate
  synthesis.  Efficiency is a separate Stage 12 obligation.
- If a candidate fails, record its counterexample and test another candidate.
  Failure of one finite set does not refute existence of some finite dense set.

#### Completion Requirements

- Exact and approximate universality have separate theorem names and outcomes.
- A concrete finite candidate is proved dense, or a decisive theorem rules out
  the entire approximate-universality class under the source's intended model.
  A candidate-specific no-go or conditional interface alone does not complete
  the stage.
- The same finite labels and arity bound work at every circuit width; allowed
  central operator phases, topology, placement, and small-width cases are
  explicit.  Stage 12 handles effective word finding and runtime, not existence
  of a width-independent universal schema.
- The unresolved row receives a proved resolution and axiom-audited public or
  research-leaf theorem.

### 12-UNIFORMITY

#### Big Picture Objective

Upgrade finite semantic simulations to encoded uniform algorithms and honest
bounded-error complexity results.

#### Detailed Implementation Plan

- Define encoded real, complex, and ordered quaternionic circuit families,
  uniform generators, input/output conventions, and deterministic plus finite
  randomized postprocessing kernels.
- Connect executable translation, routing, scheduling, approximation, and
  synthesis to an explicit list/RAM cost model, then build the required
  Turing-machine bridge before using standard polynomial-time terminology.
- Define library-relative bounded-error language classes and prove closure
  under the translated generators and postprocessors.
- First prove exact library-relative containment by taking the finite target
  library to be the realified/complexified image of a finite encoded source
  library.  This does not require solving Stage 11.
- For standard fixed-gate BQP, use the encoded epsilon-dependent complex
  compiler produced by Stage 10 (or an explicit prerequisite split), with
  Stage 9 error accumulation.  Alternatively prove gate-library invariance
  from an explicitly admissible finite complex library.  Do not infer this
  bridge from quaternionic source density.
- State separately what is proved for each supplied legal quaternionic
  schedule and what would be needed to choose or sample schedules uniformly.

#### Completion Requirements

- The real and quaternionic algorithm definitions have actual finite encodings,
  generators, schedulers, postprocessing, and runtime statements.
- A supplied `LegalSchedule` or compiler structure is not used as evidence of
  computability or polynomial time.
- The corrected computational-universality/overhead/BQP theorems include
  precision and bounded-error accounting and compile end to end.
- All five assigned rows close with executable examples, cost verification,
  traceability, and axiom audit updates.

### 13-REALQTM

#### Big Picture Objective

Independently verify the external Bernstein–Vazirani approximate-real-amplitude
QTM result instead of leaving it as an attributed exclusion.

#### Detailed Implementation Plan

- Retrieve and audit the primary theorem statement, conventions, error metric,
  time overhead, amplitude class, and measurement semantics.
- Define only the finite-time quantum Turing-machine configuration/operator
  layer needed for the theorem, reusing mathlib Turing-machine infrastructure
  where it genuinely matches.
- Formalize amplitude approximation and stability over a bounded computation,
  then construct the real-amplitude simulator and prove output-distribution and
  time/space overhead.
- If the cited statement differs materially from the paper's paraphrase,
  formalize the source theorem and record the correction rather than proving a
  convenient circuit analogue under the QTM label.

#### Completion Requirements

- The primary theorem or strongest faithful correction is stated and proved
  without importing it as an axiom.
- Approximation, halting/time bounds, and acceptance probabilities are explicit.
- A finite-circuit theorem alone cannot close this QTM row unless an actual
  circuit/QTM equivalence theorem is also proved.
- The external row gains reproducible source mapping, focused builds, and axiom
  audit coverage.

### 14-STRUCTURE

#### Big Picture Objective

Replace heuristic phase and “any Hilbert space” prose with exact structural
and operational statements.

#### Detailed Implementation Plan

- Define the real complex structure `J` and characterize the image of
  realification as the real matrices commuting with it.  Give the analogous
  conjugate-symplectic characterization for quaternionic complexification.
- State all image, intertwining, ray, and outcome results using the Goal 2
  embedded-operator/state/observable relation names and classification axes.
- Formalize a subsystem/circuit-scalar interface containing the associative
  star algebra, real-valued weight, local composition, placement coherence,
  and measurement laws actually needed by the circuit model.
- Provide real, complex, and quaternionic instances and prove that Hilbert
  structure alone does not supply this interface.
- State the exact pure-state, ray, and basis-outcome facts already available for
  the product-input ordering witness, but defer mixed-state correlation and
  signaling classification to Stage 16's native quaternionic operational API.
- Translate “top wire stores phase” into invariant-subspace/intertwining
  theorems, not a degree-of-freedom slogan.

#### Completion Requirements

- Both embedding-image characterizations are bidirectional with explicit
  dimensions and signs.
- The scalar interface has real consumers and does not encode desired
  simulation theorems as fields.
- The witness is not called entangled, signaling, or nonlocal at this layer.
- All three assigned rows close with corrected formal statements, examples,
  and audits.

### 15-MULTIPATH

#### Big Picture Objective

Give rigorous finite meanings to “following all evaluation paths” and determine
what the paper's missing weighting/interference rule can and cannot imply.

#### Detailed Implementation Plan

- Add `Path/ClassicalMixture.lean`: distributions over legal schedules,
  averaged output density/distribution, normalization, and exact complex
  simulation by linearity.
- Add `Path/Coherent.lean`: amplitude-weighted sums of scheduled operators or
  outputs, the exact normalization/unitarity obligations, and small
  counterexamples showing normalized coefficients alone do not make the sum a
  valid evolution.
- Prove underdetermination by constructing two inequivalent multi-path
  extensions that agree with every single-path axiom supplied by the paper.
- Analyze enumeration/sampling cost and prove only conditional complexity
  consequences from an explicit efficiently samplable/compilable weighting
  rule.
- Formalize concrete interference identities and counterexamples sufficient to
  separate “interference occurs” from “interference causes computational
  speedup.”

#### Completion Requirements

- Classical mixing and coherent superposition are separate APIs and theorems.
- At least one nontrivial valid multi-path model and one invalid naive model are
  proved; no arbitrary weight rule is chosen and called canonical.
- The beyond-BQP question receives a theorem, reduction, or formal
  underdetermination result in a declared model.
- All five assigned rows gain formal evidence and exact residual frontiers.

### 16-CHANNELS

#### Big Picture Objective

Establish a sound channel layer and use it to obtain concrete real/quaternionic
information-theoretic results.

#### Detailed Implementation Plan

- Extend Goal 2's same-space real/complex density, effect, unitary-channel,
  `ChannelEq`, and `AllMeasurementEq` layer with finite Kraus channels,
  instruments, trace preservation, complete positivity where meaningful,
  marginals, product states, and data processing.
- Define native quaternionic density positivity by a real quadratic form or a
  proved complexification characterization; prove unitary conjugation and the
  chosen partial trace preserve it.  Never synthesize an order on `ℍ`.
- Define product/separable states, marginals, local operations, and signaling
  tests, then classify the existing product-input ordering witness exactly.
  Distinguish ray change, computational-distribution equality, correlation,
  entanglement, and signaling.
- State channel-capacity quantities only after fixing tensor composition,
  allowed encodings/decodings, asymptotic regularization, and entropy or
  operational alternatives.
- Prove at least one substantive rebit-vs-qubit and quaternionic-vs-complex
  channel comparison, equality, separation, or obstruction.

#### Completion Requirements

- Channel and native quaternionic mixed-state definitions satisfy checked
  positivity/normalization closure laws and small exact examples.
- Capacity claims name the channel class, resource, regularization, and scalar
  model; no informal “capacity changes” theorem is accepted.
- The correlation row and both source questions have precise results or formal
  proofs that the declared axioms underdetermine them, plus named residual
  targets where applicable.
- New heavy APIs remain narrow until downstream results and audits justify
  promotion.

### 17-PROTOCOLS

#### Big Picture Objective

Test the paper's bit-commitment sketch and the teleportation/communication
questions in explicit adversarial and costed protocol models.

#### Detailed Implementation Plan

- Define local parties, admissible operations, classical messages, schedules,
  correctness, information cost, and compositional execution using Stage 16
  channels.
- Formalize exact/approximate teleportation and the classical-bit cost for a
  quaterbit under the chosen subsystem convention; prove a protocol or lower
  bound rather than relying on dimension counting alone.
- Define communication-complexity problems and costs and prove at least one
  comparison or simulation theorem between scalar models.
- Define hiding, binding, cheating strategies, opening verification, and the
  security parameter for bit commitment.  Encode the paper's sketch, then
  prove security or exhibit a formal attack/underspecification witness.

#### Completion Requirements

- The existing equal-basis-weight ordering witness is not used as security or
  signaling evidence without an operational theorem.
- Teleportation and communication results include all classical/quantum or
  quaternionic resources and exact/approximate conventions.
- The bit-commitment row closes with a full scoped security proof, a scoped
  attack on a faithful minimal completion, or a formal underdetermination
  theorem exhibiting two completions that satisfy every stated sketch
  constraint but differ in hiding/binding.  Prose about Alice and Bob is
  insufficient.
- All three rows have executable finite examples where possible and axiom-
  audited theorems.

### 18-PHYSICALITY

#### Big Picture Objective

Translate the claim that information-theoretic principles “rule out”
quaternionic physics into a valid conditional theorem—or prove that the stated
principles do not determine that conclusion.

#### Detailed Implementation Plan

- Identify explicit operational axioms from the cited reconstruction/no-bit-
  commitment programs and formalize only those needed for a finite no-go.
- Connect Stage 17's actual bit-commitment outcome to the axioms and prove the
  corresponding incompatibility implication if its premises hold.
- Separate algebraic order dependence, no-signaling, relativistic causality,
  cryptographic impossibility, and empirical physicality.
- If multiple operational completions satisfy the paper's mathematical core
  but disagree on the physicality criterion, prove formal underdetermination.

#### Completion Requirements

- No theorem declares a model physically false by definition or appeal to
  authority.
- The result is a precise implication from named operational axioms, or a
  checked underdetermination theorem.
- Every dependence on Stage 16–17 definitions is explicit and the source prose
  is reclassified accurately.
- The assigned row gains a substantive formal result and documented limits.

### 19-ALGEBRAS

#### Big Picture Objective

Test how far the circuit architecture extends beyond `ℝ`, `ℂ`, and `ℍ`, using
concrete nonassociative and finite-field cases rather than a vague taxonomy.

#### Detailed Implementation Plan

- Implement or reuse a minimal octonion model and prove an explicit associator
  counterexample showing why unparenthesized matrix/circuit products and the
  current placement laws fail; identify any alternative-tree semantics that
  remains coherent.
- Prove the finite-field obstruction to ordinary nonnegative real Born weights
  or state the additional valuation/embedding data required by a viable model.
- Factor the Stage 14 circuit-scalar interface into necessary laws and classify
  the real, complex, quaternionic, octonionic, and selected finite-field cases.
- Formulate a finite algebraic complexity comparison and prove at least one
  simulation, separation, or impossibility theorem.

#### Completion Requirements

- The stage does not claim a classification of all scalar systems without a
  proof; it delivers checked representative successes/failures.
- Octonion nonassociativity and finite-field probability issues are executable
  examples plus general lemmas, not prose observations.
- Both source questions gain precise case-study results and named remaining
  classification targets.
- Experimental modules remain isolated from the stable associative core.

### 20-RELEASE

#### Big Picture Objective

Reconcile the entire 101-row inventory and publish the expanded library and
research boundary in a form another Lean project can trust and reuse.

#### Detailed Implementation Plan

- Re-run the closure checker and independently review every one of the 47
  pre-Goal-2 cohort rows, including each `closedByGoal2` disposition, every new
  correction, and every dependency effect.
- Reconcile `EQC-045`--`EQC-051` separately against their Goal 3 owners and
  operational obstructions; none may disappear merely because the overlapping
  traceability row has a different identifier.
- Stabilize module boundaries, namespace names, public imports, docstrings,
  examples, research/diagnostic separation, and downstream usage guidance.
- Update README, Architecture, Conventions, Traceability, Corrections,
  RemainingWork, ReleaseReport, and AxiomAudit documentation.
- Run clean builds, strict checks, downstream smoke tests, executable fixtures,
  source scans, tracked-artifact checks, and an independent requirement audit.

#### Completion Requirements

- The immutable 47-row cohort has no unexamined item; Goal 2 dispositions and
  Goal 3 closure outcomes satisfy the rules above and totals reconcile with the
  101-row source inventory.
- The seven unresolved Goal 2 classification families have terminal Goal 3
  evidence or new frontier IDs, while remaining separate from the 47-row
  arithmetic.
- No original partial/unresolved row retains either status.  A corrected,
  negative, conditional, or underdetermination theorem moves it to **corrected
  and proved**; any residual research question receives a new frontier ID.
  No excluded item remains supported by prose alone.
- All completed modules contain no holes or project axioms, and every main new
  result appears in the executable axiom audit.
- Clean public-root/audit builds, warning-as-error checks, all executable tests,
  downstream import smoke, whitespace/forbidden-token/artifact scans, and
  `git diff --check` pass and are recorded.
- The final report distinguishes completed formalization from genuinely open
  scientific research and gives precise instructions for extending each.

## Stage Status

- [ ] 1-REBASE
- [ ] 2-SEMANTICS
- [ ] 3-DENSITY
- [ ] 4-FOUNDATIONS
- [ ] 5-DETERMINANT
- [ ] 6-ROUTING
- [ ] 7-PHASEFANOUT
- [ ] 8-ENCODING
- [ ] 9-APPROX
- [ ] 10-SYNTHESIS
- [ ] 11-UNIVERSALITY
- [ ] 12-UNIFORMITY
- [ ] 13-REALQTM
- [ ] 14-STRUCTURE
- [ ] 15-MULTIPATH
- [ ] 16-CHANNELS
- [ ] 17-PROTOCOLS
- [ ] 18-PHYSICALITY
- [ ] 19-ALGEBRAS
- [ ] 20-RELEASE
