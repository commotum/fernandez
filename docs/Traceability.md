# Paper-to-Lean Traceability

## Source and status policy

The local source is `Fernandez/fernandez-2003.md`, an extraction of José M.
Fernandez and William A. Schneeberger's *Quaternionic Computing*, labeled
`quant-ph/0307017v2`.  Line locators below refer to that file.  See
`Corrections.md` for diagnoses and repairs.

During implementation, **planned** and **in progress** are temporary statuses.
At release every row marked important must have exactly one terminal status:

- **proved as stated**;
- **corrected and proved**;
- **partially formalized**;
- **intentionally excluded**;
- **unresolved**.

Priorities are `P0` (central dependency cone), `P1` (important reusable result),
`P2` (model/context), and `P3` (external, historical, physical, or speculative).
Lean declaration names replace the current stage targets as proofs land.

## Goal 2 semantic-classification overlay

Goal 2 Stage 2 adds proof-bearing vocabulary without changing any paper row's
terminal status. `ExactOperatorEq` and `ExactCircuitEq` classify literal
same-space matrix and chronological-evaluator equality. `OutputWeightEqAt`,
`BasisMeasurementEq`, and `PureInputBasisMeasurementEq` separate one supplied
input, every computational-basis input, and every normalized pure input.
`BasisWeightEq ↔ NormalizedDistributionEq` identifies pointwise normalized
basis weights with the packaged finite distribution and yields finite-event
and deterministic-pushforward consequences. These wrappers make the existing
evidence more precise; they do not promote any basis-only theorem to ray,
channel, all-effect, mixed-state, or cross-model equality.

Stage 3A adds representative-level real sign, complex right phase, and
quaternionic right phase with distribution and evolution laws. Stage 3B adds
the distinct real/complex global, input-column, output-row, and projective
operator/circuit relations, together with only their justified measurement
and sided-composition implications. Stage 3C adds five side-sensitive
quaternionic operator relations, four evaluator-backed circuit wrappers, the
raw/normalized projective bridge, and the sharp projective-kernel theorem:
with explicit square dimension at least two and only the first matrix assumed
unitary, all-input right-ray action is exactly one central real sign; rank one
instead admits every unit quaternion, with `j` a noncentral witness. This
clarifies C-006 rather than introducing a new paper correction: right unit
phase remains the state/ray convention, while arbitrary unit-quaternion phase
is not matrix-wide operator global phase. None of these same-space relations
is channel or all-effect equality.

These semantic layers sharpen how existing evidence is described. Stage 4A adds normalized
`RealRay`, `ComplexRay`, and `QuaternionRay` quotients, with exact constructor
equality, normalized representative elimination, and the sharp
`Nonempty ray ↔ Nonempty index` boundary. Stage 4B now descends basis weights,
normalized distributions, finite events, deterministic pushforwards, supplied
unitary evolution, and explicitly locally-unitary chronological-circuit
evolution for all three scalar systems. Identity and composition laws record
the exact order: `U` then `V` is `V * U`, and `C ++ D` acts first by `C`, then
by `D`. The API covers the inhabited zero-wire circuit basis but defines no
arbitrary-matrix or uncertified-circuit action. It adds no density, effect,
channel, approximation, or cross-model embedding theorem. Stage 4C supplies
the separate complex-to-real boundary: `ComplexRay` is equivalent to the
unit-rotation quotient `RealSectorOrbit`, its bottom marginal distribution is
preserved, and neither canonical column descends to ordinary `RealRay` except
vacuously on an empty index. Correction C-027 records this source-order issue.
The two transferred ray rows are now proved as stated and `closedByGoal2`;
mixed-top, phase-kickback, cross-model density, and channel claims remain open
in their existing rows. Stage 7 supplies only same-space real/complex unitary
channels and does not change those cross-model dispositions.

Stage 5 adds a certified-only classical reversible basis layer. A
`BasisPermutationImplementation` supplies an explicit permutation and proves
the phased one-hot action on every input column; `SameBasisBehavior` compares
only two supplied certificates. On the certified real, complex, and
quaternionic classes, equality of the permutation is equivalent to the
correctly sided input phase, output phase, and basis-measurement relations,
with evaluator-backed circuit versions. Two explicit nonmonomial real
unitaries prove that equality of raw transition predicates can be vacuous and
therefore is not the implemented behavior relation. Exact/global/central
phase gives only a forward preservation result, and no generic projective,
channel, or all-effect conclusion is added.

Stage 6 adds reusable finite same-space physical-state infrastructure without
changing any paper row's terminal status. `DensityMatrix` packages
positive-semidefinite trace-one matrices, with explicit real and complex
aliases, pure/basis constructors, the empty-index obstruction, and unitary
conjugation `U * ρ * Uᴴ`. `Effect` packages the genuine Loewner interval
`0 ≤ E ≤ 1`; its real Born value lies in `[0,1]` and recovers the existing
real/complex basis weights on pure state-derived densities. The theorem
`DensityMatrix.eq_iff_forall_effect_bornValue_eq` proves that all genuine
physical effects separate an arbitrary fixed pair of densities, using
rank-one projector effects rather than arbitrary trace tests. This is the
foundation for Stage 7, not a channel theorem: no `ChannelEq`,
`AllMeasurementEq`, quaternionic density/positivity, partial trace, Kraus map,
instrument, or cross-model mixed-top result is added. In particular, the
existing mixed-top and channel rows remain open at exactly their prior status.

Stage 7 consumes that infrastructure without changing any paper row's terminal
status. `UnitaryOperator` bundles real/complex-style finite unitaries;
`ChannelEq` compares their complete output density for every density input,
and `AllMeasurementEq` quantifies every input and genuine physical `Effect`.
The two relations are equivalent by Stage 6 separation. Raw and normalized
real/complex projective action, global sign/phase, and channel equality have
the same kernel on an explicitly inhabited matrix index, while named
empty-index results use exact subsingleton matrix equality instead of vacuous
density quantification. `UnitaryCircuit` lifts these facts through
`OrderedCircuit.eval`; its `BitBasis` is inhabited even at zero wires, and
append retains the order `eval D * eval C`. These are same-space semantics
only. No quaternionic channel, arbitrary trace test, cross-model/mixed-top
channel, partial trace, Kraus map, instrument, teleportation protocol, or
capacity result is added.

Stage 8 closes the proof-bearing same-space implication and strictness graph
without changing any paper row's terminal status and without creating a new
paper correction. For arbitrary rectangular real, complex, and quaternionic
matrices with only a finite input type, all-normalized-pure-input basis
agreement is exactly output-row phase, with quaternionic phase on the left.
Finite-distribution equality is exactly equality of all finite-event weights
and of all deterministic pushforwards to finite targets in the same universe.
The real/complex channel and all-effect covering arrows and the circuit lifts
reuse the already checked kernels. Exact unitary and normalized-state
witnesses show why output-row or basis-only agreement does not imply channel
equality and why equal basis distributions do not imply ray equality. These
results refine the semantic classification of existing evidence; they do not
alter the scope of a fixed-input witness, infer an unrestricted classical
permutation, or close any cross-model, mixed-top, quaternionic-channel,
approximation, ordering-resource, or complexity row.

Stage 9A adds directional cross-model relation vocabulary without changing a
paper row's terminal status or adding a paper correction. `ExactStateEncoding`
and `LosslessStateEncoding` keep explicit encoders, decoders, and total-weight
policies; the operator, intertwining, and decoded-observation relations likewise
retain direction and observation scope. Their generic `AllTop...` forms quantify
an uninterpreted top-sector parameter, not a hidden product subsystem. The four
canonical raw state columns are proved to be explicit-decoder `ℝ`-linear
equivalences, and their normalized restrictions are equivalences of
representative carriers. This strengthens the checked classification of the
representative-encoding rows, but it does not identify ordinary ray spaces or
close the Stage 9B circuit/operator and Stage 9C outcome families. In
particular, `RealSectorOrbit` remains the complex-to-real ray target and
`NonProductWitness.encodedState_not_pureTopBottomProduct` prevents a normalized
`Rebit`/`Qubit` coefficient parameter from being read as a factorization proof.

## Numbered definitions, theorems, lemmas, and corollary

| ID | Source | Concise target and dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-D01-REBIT` | L92–115, Eq. 4–6 | Normalized vectors in `ℝ²`, with optional pure-state quotient by `±1`. Depends on finite real state conventions. | P2 / `State/Basic.lean`, `State/RealPhase.lean`, `State/Ray.lean`, `State/RayObservables.lean`, `State/RayEvolution.lean`, `Semantics/Ray.lean`, `State/RealificationOrbitBoundary.lean` | **proved as stated** (`closedByGoal2`): `Rebit` is explicitly normalized and `RebitRay` is the `Bool`-indexed normalized quotient. `RealRay.mk_eq_mk_iff_eq_or_eq_neg` proves literal ray equality is exactly equality or pointwise negation; the generic quotient has representative induction/lifting and the exact index-inhabitation boundary. `RealRay.distribution`, `basisWeight`, `eventWeight`, deterministic `pushforward`, supplied-unitary evolution, and locally-unitary circuit evolution all descend with exact representative, identity, matrix-composition, empty-circuit, and chronological-append laws. Stage 4C additionally proves that realification of a complex source ray must not be confused with this ordinary sign quotient: canonical complex-to-real columns survive in `RealRay` only for source phases `±1` (C-027). This boundary completes rather than weakens the paper's rebit definition |
| `FER03-D02-REAL-ALGORITHM` | L140–142 | Classical uniform generator, real circuit measurement, and postprocessing. Depends on circuit/output semantics and an encoding model. | P2 / `State/Distribution.lean`, `Simulation/Postprocessing.lean`, 8-RESOURCES | **partially formalized**: fixed finite real-circuit output distributions, all finite events, and every deterministic finite postprocessing map are covered; no discrete circuit encoding, uniform classical generator, randomized machine, or runtime theorem is supplied |
| `FER03-D03-QUATERBIT` | L791–812, Eq. 44–45 | Normalized vectors in `ℍ²`, right unit phase, and basis weights. Depends on quaternion norm and right-module conventions. | P0 / `Scalar/Phase.lean`, `State/Basic.lean`, `State/Ray.lean`, `State/RayObservables.lean`, `State/RayEvolution.lean`, `Semantics/Ray.lean`, `Semantics/OperatorPhase/Quaternion.lean`, `Semantics/OperatorPhase/QuaternionCircuit.lean`, `Semantics/OperatorPhase/QuaternionKernel.lean` | **corrected and proved**: `Quaterbit`, its normalization, the raw and normalized right-phase equivalence relations, and `QuaterbitRay` repair C-005/C-006 with phase strictly on the right. `QuaternionRay.mk_eq_mk_iff` makes that relation literal quotient equality; basis distributions, finite events, deterministic pushforwards, unitary action, and locally-unitary chronological-circuit action now descend with exact identity and composition laws. The normalized left-phase diagnostic confirms that the paper's side cannot be retained. The separate operator classification proves that this state phase does not license arbitrary unit-quaternion matrix-wide phase: dimensions at least two have only the central real-sign projective kernel, while rank one has the explicitly proved full unit-quaternion exception |
| `FER03-D04-ORDERED-CIRCUIT-OUTPUT` | L841–849 | Product of explicitly placed gates along one legal order. Depends on noncommutative-safe placement and evaluation order. | P0 / `Circuit/Basic.lean`, `Circuit/Ordering.lean` | **corrected and proved**: `LegalSchedule` lists every finite gate occurrence exactly once and certifies the supplied precedence constraints; `scheduledCircuit`, `scheduledEval`, and `OrderedCircuit.eval` give the reverse-chronological product for that exact schedule. Existence of a schedule is the consistency certificate; no transitive DAG structure is assumed |
| `FER03-D05-QUATERNIONIC-ALGORITHM` | L851 | Uniform generator emits circuit plus legal ordering; ordered state is measured/postprocessed. | P2 / `Circuit/Ordering.lean`, `Simulation/Scheduled.lean`, `Simulation/Postprocessing.lean`, 8-RESOURCES | **partially formalized**: the finite gate family, supplied legal schedule, ordered normalized output, exact per-schedule simulation, finite events, and deterministic finite postprocessing core is present; no discrete encoding, uniform classical generator, randomized postprocessor, or runtime model is claimed |
| `FER03-T01-BERNSTEIN-VAZIRANI-REAL-QTM` | L148–156 | External approximate-real-amplitude QTM result. | P3 / 9-COVERAGE | **intentionally excluded**: attributed, unproved, and underspecified in source |
| `FER03-T02-COMPLEX-CIRCUIT-TO-REAL` | L167–170 | Translate `n`-qubit, `s`-gate, arity-`≤d` ordered circuits to `n+1` rebits with `s` image gates of arity `≤d+1`; separately prove operator and observable preservation. | P0 / `Simulation/ComplexToReal.lean`, `Simulation/Postprocessing.lean`, `Simulation/Resources.lean` | **corrected and proved** by `complexToReal_exactSimulation`, with separate operator/state/probability/count/width/arity results; equality of every finite event and deterministic finite pushforward; and exact literal shared-top support depth and dense-slot consequences. None is a runtime or synthesis theorem (C-010/C-019/C-024) |
| `FER03-T03-COMPLEX-REALIFICATION-GROUP` | L173–320 | Injective star-preserving realification; `U(N)` image is in `SO(2N)`. Depends on L01/L02 and determinant identity. | P0 / `Matrix/Unitary.lean`, `Matrix/Determinant.lean` | **corrected and proved**: `realifyStarMonoidHom`, `realifyUnitaryEquivImage`, `realify_mem_specialOrthogonal`; dimension/domain repair C-002 and missing determinant proof C-020 |
| `FER03-T04-ORDERED-QUATERNIONIC-TO-COMPLEX` | L853–855 | Translate a fixed ordered `n`-quaterbit circuit to `n+1` qubits with one arity-`d+1` image gate per source gate; prove embedded evolution and bottom measurement equality. | P0 / `Simulation/QuaternionToComplex.lean`, `Simulation/Scheduled.lean`, `Simulation/Postprocessing.lean`, `Simulation/Resources.lean` | **corrected and proved** by `quaternionToComplex_exactSimulation` for arbitrary chronological circuits and `scheduledQuaternionToComplex_exactSimulation` for each supplied legal schedule, with separate operator/state/probability/resource conclusions, finite-event and deterministic-pushforward preservation, and literal shared-top depth/dense-slot results. The schedule is retained, not chosen or identified, and no runtime is inferred (C-006/C-010/C-019/C-024) |
| `FER03-T05-QUATERNION-COMPLEXIFICATION-GROUP` | L861–965 | Injective star-preserving homomorphism from quaternionic unitaries to complex unitaries in dimension `2N`; separately audit determinant one. | P0 / `Matrix/Unitary.lean`, `Matrix/Determinant.lean` | **partially formalized**: corrected `U(2N)` and symplectic image proved by `complexifyUnitaryEquivImage`, `complexify_mem_unitary`, `complexify_mem_symplectic`; determinant is formally reduced to `1 ∨ -1`, but the `SU(2N)` sign refinement remains unresolved (C-003/C-004) |
| `FER03-L01-REALIFICATION-MUL` | L211–270, Eq. 11–13 | `h(AB)=h(A)h(B)` for compatible complex matrices. Depends on re/im product identities. | P0 / `Matrix/Realification.lean` | **proved as stated**, generalized to compatible rectangular shapes by `realPart_mul`, `imagPart_mul`, `realify_mul` |
| `FER03-L02-REALIFICATION-ADJOINT` | L282–320, Eq. 15–16 | `h(Aᴴ)=h(A)ᵀ`. | P0 / `Matrix/Realification.lean` | **proved as stated**, generalized to rectangular matrices by `realPart_conjTranspose`, `imagPart_conjTranspose`, `realify_conjTranspose` |
| `FER03-L03-REAL-CIRCUIT-COMPOSITION` | L438–487, Eq. 23 | Evaluation of translated ordered circuit equals realification of source evaluation. Depends on L01 and local placement naturality. | P0 / `Simulation/ComplexToReal.lean` | **corrected and proved**, generalized to arbitrary finite wire types/supports by `eval_realifyCircuit`; the equality is typed through `wireRealify` |
| `FER03-L04-REALIFICATION-INTERTWINES-STATES` | L489–558, Eq. 24–27 | `h(U) h₀(ψ)=h₀(Uψ)` and corresponding `h₁` identity. | P0 / `State/Realification.lean`, `Semantics/SimulationEncoding.lean` | **corrected and proved** for compatible rectangular matrices by `realify_mulVec_realColumn0` and `realify_mulVec_realColumn1`; the ill-typed source derivation is replaced per C-021. Stage 9A additionally proves both raw column maps are explicit-decoder `ℝ`-linear equivalences and both normalized representative maps are `Equiv`s; the `StateIntertwining` wrapper for this theorem family remains Stage 9B work |
| `FER03-L05-REAL-REDUCED-MEASUREMENT` | L561–659, Eq. 28–33 | Equal reduced real matrices for both encodings and pointwise equality of computational-basis diagonals/weights. | P0 / `State/Realification.lean` | **corrected and proved** directly: `reducedRealOuter_realColumns`, `reducedRealOuter_realColumn0`, `reducedRealOuter_diagonal`, `realColumn0_bottomWeight`, `realColumn1_bottomWeight`; no partial-trace hierarchy is required |
| `FER03-L06-QUATERNION-COMPLEXIFICATION-MUL` | L895–927, Eq. 49 | `ĥ(AB)=ĥ(A)ĥ(B)` for compatible quaternion matrices. Depends on Co/Wd multiplication. | P0 / `Matrix/Complexification.lean` | **proved as stated**, generalized to compatible rectangular shapes by `complexPartMatrix_mul`, `jPartMatrix_mul`, `complexify_mul` without commutativity |
| `FER03-L07-QUATERNION-COMPLEXIFICATION-ADJOINT` | L929–965, Eq. 50–51 | `ĥ(Aᴴ)=ĥ(A)ᴴ`. | P0 / `Matrix/Complexification.lean` | **proved as stated**, generalized to rectangular matrices by `complexPartMatrix_conjTranspose`, `jPartMatrix_conjTranspose`, `complexify_conjTranspose` |
| `FER03-L08-QUATERNIONIC-CIRCUIT-COMPOSITION` | L967–980 | Translated ordered operator equals `ĥ(Qσ)`. Depends on L06 and placement naturality. | P0 / `Simulation/QuaternionToComplex.lean` | **corrected and proved** by `eval_complexifyCircuit`; it fills the source's missing noncommutative local proof before applying ordered-list induction |
| `FER03-L09-QUATERNION-STATE-INTERTWINING` | L983–1073, Eq. 52–57 | `ĥ(Q) ĥ₀(ψ)=ĥ₀(Qψ)` and corresponding `ĥ₁` identity. | P0 / `State/Complexification.lean`, `Semantics/SimulationEncoding.lean` | **corrected and proved** for compatible rectangular matrices by `complexify_mulVec_complexColumn0` and `complexify_mulVec_complexColumn1`, with the missing source output relation eliminated (C-012/C-021). Stage 9A additionally proves both raw column maps are explicit-decoder `ℝ`-linear equivalences and both normalized representative maps are `Equiv`s; the `StateIntertwining` wrapper remains Stage 9B work |
| `FER03-L10-QUATERNION-COMPUTATIONAL-MEASUREMENT` | L1075–1171, Eq. 58–62 | Each complex encoding preserves bottom computational-basis weights after summing over top qubit. | P0 / `State/Complexification.lean` | **proved as stated** at the observable level by `complexColumn0_bottomWeight` and `complexColumn1_bottomWeight`; the proof uses the scalar norm decomposition rather than the paper's imprecise density algebra |
| `FER03-C01-ORDERED-QUATERNIONIC-TO-REAL` | L1202–1221, Eq. 63 | Compose T04 and T02 to simulate with `n+2` rebits; also verify the direct `4N` real representation. | P1 / `Simulation/QuaternionToReal.lean`, `Matrix/QuaternionRealification.lean`, `Simulation/Resources.lean` | **corrected and proved** compositionally by `quaternionToReal_exactSimulation`, `eval_quaternionToRealCircuit`, nested state intertwining, and four-sector probability preservation; the literal composite also has support depth exactly source gate count and dense-slot factor `16`. Independently, `directRealify_eq_reindex` proves at the algebraic matrix level that Equation 63 is the same embedding in the paper's `[Re,ImI,ImK,ImJ]` sector order. The public circuit theorem remains the two-wire composition; no direct placement or wire-facing translator is claimed |

## Foundational and model claims

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-FND-COMPLEX-STATE-RAY` | L38, L73–90 | Normalized complex vectors modulo unit right/commutative phase. | P2 / `State/ComplexPhase.lean`, `State/Ray.lean`, `State/RayObservables.lean`, `State/RayEvolution.lean`, `Semantics/Ray.lean`, `State/RealificationOrbit.lean`, `State/RealificationOrbitObservables.lean`, `State/RealificationOrbitBoundary.lean` | **proved as stated** (`closedByGoal2`): `ComplexRay` and `QubitRay` give literal quotient equality, with `ComplexRay.mk_eq_mk_iff` identifying it exactly with unit right phase, representative induction/lifting, and the exact empty-index boundary. Computational-basis distributions, events, deterministic pushforwards, supplied-unitary evolution, and locally-unitary circuit evolution descend with exact identity and composition laws; `ComplexStatePhaseEq.iff_complexRay_mk_eq` bridges representative semantics to quotient equality. Under realification, the correct phase-invariant target is `RealSectorOrbit`, with `complexRayEquivRealSectorOrbit` and `ComplexRay.realificationOrbit_distribution` proving exact representation and bottom-outcome preservation. Either canonical representative column fails to define an ordinary target-`RealRay` map on every nonempty index type; this is correction C-027, not a failure of the source ray definition |
| `FER03-FND-COMPUTATIONAL-MEASUREMENT` | L40–48, Eq. 1 | Basis outcome weight is squared scalar norm; normalized weights sum to one. | P0 / `State/Basic.lean` | **proved as stated** for finite real, complex, and quaternion columns by `*BasisWeight`, `*TotalWeight`, their nonnegativity theorems, and `NormalizedState.sum_basisWeight` |
| `FER03-FND-LINEAR-ISOMETRY-UNITARY` | L50, FN2 | Complex-linear finite norm preservers are unitary; antiunitaries excluded by linearity. | P2 / mathlib matrix API | **intentionally excluded** as a background finite-dimensional linear-algebra characterization: the library represents allowed transformations directly by mathlib's `Matrix.unitaryGroup`/`unitary` predicates and proves the norm-preservation direction it consumes. It does not reprove the converse classification of all complex-linear norm preservers or the separate antiunitary theory |
| `FER03-FND-FINITE-DIM-COMPLETE` | FN1 | Finite-dimensional inner-product spaces are complete. | P3 / 9-COVERAGE | **intentionally excluded**: existing background fact not used by finite matrix core |
| `FER03-FND-ARBITRARY-WIRE-ROUTING` | L57, FN3 | Route noncontiguous gates with swaps under an explicit cost model. | P2 / `Circuit/Placement.lean`, 8-RESOURCES | **partially formalized**: `supportSplit` and `placeOnSupport` give semantics on every injective, possibly noncontiguous support; no physical swap synthesis or quadratic cost is inferred |
| `FER03-FND-GROUND-STATE-WLOG` | L59, L561 | Absorb known basis input preparation into a circuit; not an unknown-state WLOG. | P1 / `Circuit/BasisPreparation.lean`, `Semantics/BasisBehavior.lean`, `Semantics/BasisBehaviorCircuit.lean` | **corrected and proved** for a classically known computational-basis assignment: `basisPreparationGate` is a full-support XOR permutation gate, is locally/globally unitary, maps the ground basis column to the requested basis column, and `eval_prepend_basisPreparation_mulVec_ground` absorbs it into chronological evaluation. Stage 5 additionally certifies the actual matrix, gate, and singleton circuit as implementing `x ↦ x XOR b` for every basis input. This all-input certificate is distinct from the one-known-ground-input preparation statement. No unknown-state preparation, primitive synthesis, or uniform runtime claim is made |
| `FER03-FND-ANY-HILBERT-SCALARS` | L61 | Claim that any Hilbert scalar system automatically gives a sound circuit model. | P2 / `Circuit/Placement.lean`, `Matrix/KroneckerCommute.lean`, `Circuit/OrderingWitness.lean` | **partially formalized**: the library constructs finite subsystem placement explicitly, proves the exact entrywise-commutation boundary for tensor interchange, and gives an order-sensitive quaternionic witness; it does not attempt a classification of all Hilbert-space scalar systems (C-023) |
| `FER03-FND-REAL-PRESERVERS-ORTHOGONAL` | L67–69 | A complex-linear map preserving the real subspace has a real matrix; norm preservation gives orthogonality. | P1 / 3-MATRICES | **partially formalized**: the matrix-level norm-preserving consequence needed here is `realify_mem_orthogonal`; the broader invariant-real-subspace characterization is not used by the simulations |
| `FER03-FND-REAL-CIRCUIT-SOUNDNESS` | L119–134 | Products and legal placements of orthogonal gates remain orthogonal. | P1 / `Circuit/Placement.lean`, `Circuit/Basic.lean` | **corrected and proved**, generalized to any star ring by `place_mem_unitary`, `PlacedGate.denote_mem_unitary`, and `OrderedCircuit.eval_mem_unitary` |
| `FER03-FND-OUTCOME-EQUIVALENCE-SUFFICES` | L140–142 | Classical postprocessing only observes the output distribution. | P0 / `State/Distribution.lean`, `Simulation/Postprocessing.lean` | **corrected and proved** for finite deterministic semantics: `realifyCircuitBottomDistribution_eq` and `complexifyCircuitBottomDistribution_eq` give equality of normalized bottom distributions, hence equal weight for every finite event and equal pushforwards under every deterministic map to a finite type; no runtime claim is included |
| `FER03-FND-FINITE-PRECISION` | FN6 | Classical descriptions contain finite-precision approximations. | P1 / 8-RESOURCES | **partially formalized** only as a boundary: exact abstract matrices and exact certified compilation are separated from approximation; no discrete scalar encoding, error metric, stability theorem, or finite-precision compiler is available (C-024) |

## Complex-to-real algebra, states, and circuits

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-R-REALIFICATION-DEF` | L175–203, Eq. 8–10 | Define `h(A)=[[re A,im A],[-im A,re A]]`; tensor notation only mnemonic. | P0 / `Matrix/Realification.lean` | **proved as stated**: `realPart`, `imagPart`, `realify` and four block-entry lemmas; the operator-valued tensor mnemonic is intentionally not encoded |
| `FER03-R-REIM-PRODUCT` | L213–239, Eq. 11–12 | Scalar and compatible-matrix real/imaginary product formulas. | P0 / mathlib, `Matrix/Realification.lean` | **proved as stated**: scalar `Complex.mul_re`/`Complex.mul_im`; matrix `realPart_mul`/`imagPart_mul` |
| `FER03-R-REIM-ADJOINT` | L310–318, Eq. 16 | Real/imaginary components of complex adjoint. | P0 / `Matrix/Realification.lean` | **proved as stated**: `realPart_conjTranspose`, `imagPart_conjTranspose` |
| `FER03-R-SERIAL-COMPOSITION` | L322–340, Fig. 1 | A legal order gives a reverse chronological matrix product. | P0 / `Circuit/Basic.lean` | **proved as stated** for an explicit chronological list by `OrderedCircuit.eval`, `eval_cons`, and `eval_append`; legality generation is separate |
| `FER03-R-TOPO-SORT-COMPLEXITY` | L336, FN5 | Topological sorting is efficient; circuit/TM equivalence is external. | P2 / `Circuit/Ordering.lean`, `Circuit/ScheduleCount.lean` | **partially formalized**: `LegalSchedule` packages a supplied order and `allChronologicalOrders` enumerates finite permutations, but neither is a topological-sorting algorithm; no computability, runtime, graph encoding, or circuit/TM equivalence is formalized |
| `FER03-R-QUANTUM-GATE-PADDING` | L344–363, Eq. 17, Fig. 2 | Lift arbitrary-arity local gate to noncontiguous wires via explicit support/permutation. | P0 / `Circuit/Placement.lean` | **corrected and proved**, generalized by `place`, `place_apply`, `supportSplit`, and `placeOnSupport`; reindexing is semantic and no swap cost is counted |
| `FER03-R-STATE-ENCODINGS` | L365–390, Eq. 18–19 | `h₀(z)=(re z,-im z)`, `h₁(z)=(im z,re z)` coordinatewise. | P0 / `State/Realification.lean` | **proved as stated**: `realColumn0`, `realColumn1`, their sector lemmas, reconstructions, and injectivity |
| `FER03-R-ENCODINGS-ORTHOGONAL` | L393 | Both state encodings preserve norm and are mutually real-orthogonal. | P1 / `State/Realification.lean` | **proved as stated**: `realColumn0_dot_self`, `realColumn1_dot_self`, `realColumns_orthogonal`, `realColumns_equal_norm` |
| `FER03-R-ENCODINGS-LINEAR` | L393 | Encodings are additive and `ℝ`-linear, not `ℂ`-linear. | P0 / `State/Realification.lean` | **corrected and proved** by bundled `realColumn0Linear` and `realColumn1Linear` (C-007) |
| `FER03-R-BASIS-ENCODING` | L395–405, Eq. 20–21 | Real basis vectors acquire top coordinate 0 or 1. | P0 / `State/Realification.lean` | **proved as stated**: `realColumn0_single`, `realColumn1_single` |
| `FER03-R-LOCAL-GATE-COST` | L407 | Constant-arity exact entry conversion is constant cost under a fixed encoding. | P2 / `Circuit/DescriptionCost.lean` | **partially formalized**: `translationWork_le_gateCount_mul` proves the finite conditional bound from a separately supplied per-gate cost `≤ K`; no scalar encoding or theorem deriving such a constant cost from arity is provided |
| `FER03-R-NONFACTORING-OUTPUT` | Fig. 3, L409–411, L561 | Non-real examples yield non-product encoded states. | P1 / `Simulation/NonProductWitness.lean` | **corrected and proved** by a normalized rational witness: the source amplitudes `3/5` and `(4/5)i` encode canonically as `(3/5,0,0,-4/5)`, and `NonProductWitness.encodedState_not_pureTopBottomProduct` rules out even unnormalized pure top/bottom factors. This is not a mixed-state, signaling, or cryptographic theorem |
| `FER03-R-REAL-GATE-PADDING` | L413–430, Eq. 22, Fig. 4 | Place each image gate on the source support plus shared top wire. | P0 / `Circuit/AddedWire.lean`, `Circuit/Realification.lean` | **corrected and proved**, generalized by `addTopSplit`, `wireRealify_place`, `realifyPlacedGate_denote`, and the translated support-map theorems |
| `FER03-R-ANCILLA-REUSE` | L432–436, Fig. 5 | All translated gates reuse one top wire; abstract gate count remains `s`. | P0 / `Simulation/ComplexToReal.lean` | **corrected and proved** structurally: `realifyCircuit` maps every gate into the same `AddedWire W`, while `gateCount_realifyCircuit` is exact |
| `FER03-R-SWAP-REALIFICATION` | L462–478 | Realification commutes with central permutation/padding operations. | P0 / `Circuit/Realification.lean` | **corrected and proved** in the stronger support-independent semantic form `wireRealify_place`; explicit physical swap lists are neither needed nor counted |
| `FER03-R-PARTIAL-TRACE-BLOCK-SUM` | L579–598, Eq. 30 | Tracing a two-level top subsystem sums diagonal blocks. | P0 / `State/Realification.lean` | **partially formalized** by the explicit rank-one `reducedRealOuter`; Stage 6 now supplies finite same-space real/complex density matrices, but no generic partial-trace operator or cross-model mixed-state theorem, so this row remains partial |
| `FER03-R-ARBITRARY-TOP-REBIT` | L661 | Any normalized pure or mixed product top rebit yields the same bottom basis statistics. | P1 / `State/Realification.lean`, `State/RealificationOrbit.lean`, `State/RealificationOrbitObservables.lean`, `Semantics/Simulation.lean` | **partially formalized**: every normalized `Rebit` coefficient pair is covered by `realTopCombination_bottomWeight_of_rebit` and `realTopState`; Stage 4C further proves every such coefficient encoding is in the canonical `RealSectorOrbit`, so its descended bottom distribution is the source complex-ray distribution. The coefficient pair selects a linear combination of canonical columns and does not assert that the encoded target factors into pure top and bottom states; `NonProductWitness.encodedState_not_pureTopBottomProduct` refutes that reading. Stages 6–7 supply same-space real/complex densities and unitary channels, but no cross-model mixed product-density encoder, no-correlation certificate, partial trace, or decoded-effect theorem, so the mixed extension remains open |
| `FER03-R-REAL-GATE-OPTIMIZATION` | L667 | A real source gate maps to identity on top coordinate times the gate. | P1 / `Matrix/Realification.lean`, `Simulation/Resources.lean` | **partially formalized**: `realify_map_ofReal` proves the exact doubled block-diagonal matrix, but the literal uniform gate translator still adds and uses the shared top wire for every occurrence; no optimized circuit translation or resource theorem removes it |
| `FER03-R-SERIAL-DEPTH` | L669 | Shared-top construction has target depth at most gate count and can lose parallelism. | P1 / `Circuit/Depth.lean`, `Simulation/Resources.lean` | **corrected and proved** in the explicit support-disjoint model: every `SupportLayering` has depth at most gate count, and every layering of the literal realified circuit has depth exactly the source gate count because all image gates use the top wire. This is not a lower bound for alternative translations |
| `FER03-R-MULTI-ANCILLA-LOG-DEPTH` | L671 | Several top wires allegedly give `O(log s)` depth increase. | P2 / 8-RESOURCES | **unresolved**: the paper supplies no construction, correctness proof, ancilla count, fan-in convention, or primitive gate set; the one-shared-wire depth theorem neither proves nor refutes another encoding (C-015) |
| `FER03-R-PREPROCESSING-COST` | L673 | Translation is linear time under fixed-arity/unit-cost exact gate encoding. | P1 / `Circuit/DescriptionCost.lean`, `Circuit/Compilation.lean` | **partially formalized**: additive work and compiled-count bounds are proved only from explicit per-gate `K` premises; there is no discrete encoding, implementation, arithmetic-cost model, or unconditional preprocessing-runtime theorem (C-019/C-024) |
| `FER03-R-SUBSET-MEASUREMENTS` | L673 | All marginals of bottom computational-basis outcomes are preserved. | P1 / `State/Distribution.lean`, `Simulation/Postprocessing.lean` | **corrected and proved** for every finite bottom event and, more generally, every deterministic map to a finite output type by `realifyCircuitOutput_eventWeight` and `realifyCircuitOutput_pushforward_eq` |
| `FER03-R-COMPUTATIONAL-UNIVERSALITY` | L675–679 | Image of a quantum-universal family computationally simulates it with shared top rebit. | P1 / `Simulation/ComplexToReal.lean`, `Simulation/Postprocessing.lean` | **partially formalized**: every supplied finite circuit has an exact image with the same deterministic finite output distribution, but no encoded uniform circuit family, universal primitive library, compiler, or runtime theorem establishes the paper's computational-universality conclusion |
| `FER03-R-PHASE-TRACKING-INTERPRETATION` | L681–687, FN7 | Top rebit records the real/imaginary relation; heuristic phase-kickback analogy. | P2 / `State/Realification.lean`, `State/RealificationOrbit.lean`, `State/RealificationOrbitObservables.lean`, `Simulation/NonProductWitness.lean` | **partially formalized**: the exact sector action proves how every complex phase rotates the two real coordinates, `RealSectorOrbit` packages the resulting phase-invariant representation, and its bottom marginal is exactly the source ray distribution. Both canonical columns and every normalized `Rebit` top-sector coefficient lie in the same orbit. The coefficient is not an independent pure top factor; the non-product witness proves that boundary. The dynamical “phase kickback” analogy, its maximally-mixed exception, and arbitrary mixed-top behavior remain interpretive/unformalized claims assigned to Goal 3 |

## Quaternion algebra, states, and ordering

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-Q-ALGEBRA` | L697–711, Eq. 34–35, FN8 | Reuse associative noncommutative division algebra and basis multiplication. | P0 / `Scalar/Quaternion.lean` | **proved as stated** via mathlib `Quaternion` plus public `i`, `j`, `k`, `i_mul_i`…`i_mul_j_mul_k` |
| `FER03-Q-CONJUGATE-NORM` | L713–729, Eq. 36–37 | Conjugation and norm-square coordinate formula. | P0 / mathlib + `Scalar/Quaternion.lean` | **proved as stated** via `Quaternion.normSq_def'`, `self_mul_star`, `star_mul_self`, and component norm theorem |
| `FER03-Q-CO-WD-DECOMP` | L731–753, Eq. 38–40 | Define `complexPart` and neutral-name `jPart` (paper “weird part”); reconstruct `q=z+w j`. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart`, `jPart`, `eq_complexPart_add_jPart_mul_j`, `components_injective` |
| `FER03-Q-CO-WD-MUL` | L755–769, Eq. 41 | Order-sensitive multiplication formulas. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart_mul`, `jPart_mul` |
| `FER03-Q-CO-WD-NORM` | L771–777, Eq. 42 | Quaternion norm square is sum of component complex norm squares. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `normSq_eq_complexPart_add_jPart` |
| `FER03-Q-CO-WD-CONJ` | L779–787, Eq. 43 | Components under quaternion conjugation. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart_star`, `jPart_star` |
| `FER03-Q-UNITARY-SP` | L816–820 | Generic quaternionic unitary matrices form the compact symplectic group. | P0 / `Matrix/Unitary.lean` | **corrected and proved** at the finite matrix/image level: quaternionic unitaries use generic `unitary (Matrix n n ℍ)` and `complexify_mem_symplectic` proves their complex images preserve `Matrix.J`; no quaternion determinant is assumed |
| `FER03-Q-KRONECKER-INTERCHANGE` | L822–830, Eq. 46 | Prove commutative case and correct entrywise-commutation sufficient condition; disprove “only if C,D are 0–1.” | P0 / `Matrix/KroneckerCommute.lean`, `Circuit/Placement.lean` | **corrected and proved**: `kronecker_mul_kronecker_of_entrywiseCommute` gives the rectangular sufficient condition on the two middle factors, with commutative and zero–one corollaries; `oneByOne_interchange_without_zeroOne` is an explicit non-zero–one success and `oneByOne_interchange_i_j_failure` an `i`/`j` failure. No necessity or `iff` characterization is claimed (C-009) |
| `FER03-Q-PARALLEL-ORDER-DEPENDENCE` | L831–839, Fig. 6 | Exhibit disjoint local gates/orderings with distinct operators and observable outcomes. | P0 / `Circuit/OrderingWitness.lean`, `Simulation/OrderingWitness.lean` | **corrected and proved** existentially: disjoint locally unitary rational `i`/`j` mixers admit two legal orders with unequal operators and normalized `00` weights `8281/15625` and `1369/15625`; exact complex simulation preserves both the operator gap and weights. This does not universalize order dependence to every disjoint pair (C-018) |
| `FER03-Q-CUT-POSET` | L837 | Relate legal gate linear extensions to evaluation chains; do not identify one sort with a total order on all cuts. | P2 / `Circuit/Ordering.lean` | **partially formalized**: `LegalSchedule` is the finite gate-occurrence linear-order core and `scheduledCircuit` turns it into an evaluation chain. A temporal-cut type/poset and the paper's identification of one gate sort with a total order on all cuts are deliberately not formalized |
| `FER03-Q-NUMBER-OF-PATHS` | L839 | Families can have many linear extensions; state any counting bound precisely. | P2 / `Circuit/ScheduleCount.lean` | **corrected and proved** for the unconstrained finite case: `allChronologicalOrders` is duplicate-free and has exactly `(Fintype.card ι)!` orders, all legal for empty precedence. Every general legal schedule lies in that enumeration, but no factorial or exponential count is claimed for an arbitrary precedence relation |
| `FER03-Q-COMPLEXIFICATION-DEF` | L861–887, Eq. 47–48 | Define the explicit complex block embedding; tensor notation is mnemonic. | P0 / `Matrix/Complexification.lean` | **corrected and proved**: `complexify` is the explicit block matrix, with entrywise lower-block conjugation and four block-entry lemmas; malformed/formal tensor display excluded per C-011 |
| `FER03-Q-ADJOINT-COMPONENTS` | L931–940, Eq. 50 | Co/Wd identities for quaternionic conjugate transpose. | P0 / `Matrix/Complexification.lean` | **proved as stated**: `complexPartMatrix_conjTranspose`, `jPartMatrix_conjTranspose` |
| `FER03-Q-STATE-ENCODINGS` | L983–1005, Eq. 52–53 | Define `ĥ₀(q)=(Co q,-conj(Wd q))`, `ĥ₁(q)=(Wd q,conj(Co q))`. | P0 / `State/Complexification.lean`, `Semantics/SimulationEncoding.lean` | **proved as stated**: `complexColumn0`, `complexColumn1`, sector lemmas, real-linear maps, reconstruction, basis maps, norm preservation, and `complexColumns_orthogonal`; Stage 9A strengthens both raw coordinate maps to explicit-decoder `ℝ`-linear equivalences and both normalized representative maps to `Equiv`s, without asserting a ray or behavioral equivalence |
| `FER03-Q-ARBITRARY-TOP-QUBIT` | L1075 | Any normalized pure/mixed product top qubit preserves bottom basis statistics. | P1 / `State/Complexification.lean`, `Semantics/Simulation.lean` | **partially formalized**: every normalized `Qubit` coefficient pair is covered by `complexTopCombination_bottomWeight_of_qubit` and `complexTopState`. The coefficient pair selects a canonical-column combination; it does not certify a factorized target state. Same-space complex densities/channels now exist, but no quaternionic-source density encoding, mixed product-density construction, no-correlation certificate, partial trace, or decoded-effect theorem is available |
| `FER03-Q-DIRECT-REALIFICATION` | L1208–1221, Eq. 63 | Verify direct `4×4` scalar representation and matrix/unitary consequences. | P1 / `Matrix/QuaternionRealification.lean`, `Matrix/QuaternionRealificationUnitary.lean`, `Matrix/ProperImage.lean` | **corrected and proved**: `directRealify` has four real sectors per source index, all 16 Equation 63 entries, and the pure sector permutation `[3,1,0,2]` relation `directRealify_eq_reindex` to `realify (complexify A)`. It is injective, multiplicative, star-preserving, and sends quaternionic unitaries into `SO(4N)` with determinant one. `directRealifyUnitaryEquivImage` gives the corrected isomorphism onto its image, while `directWitness_specialOrthogonal_not_directRealify` proves the image is already proper in `SO(4)` at rank one (C-025) |

## Resource and universality claims

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-RES-Q-WIDTH-DEPTH` | L1176–1180 | Abstract ordered simulation width `n+1`; shared top wire can serialize depth to `s`. | P1 / `Simulation/QuaternionToComplex.lean`, `Circuit/Depth.lean`, `Simulation/Resources.lean` | **corrected and proved** for the literal construction: width is exactly `n+1`, and every support-disjoint layering of the complexified circuit has depth exactly source gate count `s` because every image gate uses the shared top wire. This is construction-specific, not an alternative-encoding lower bound |
| `FER03-RES-ABSTRACT-GATE-COUNT` | L1180 | One `(d+1)`-ary image gate per `d`-ary source gate. | P0 / `Circuit/Cost.lean`, primary simulation leaves | **corrected and proved**: both `gateCount_*Circuit` equalities and `mem_*Circuit_arity` provenance theorems give one target gate with exact local arity `+1`; composed simulation gives exact `+2` |
| `FER03-RES-GENERIC-DECOMPOSITION` | L1180–1184 | Generic target unitary elementary-gate synthesis bound. | P1 / `Circuit/Compilation.lean` | **unresolved** as an existence/bound claim: the source gives no primitive library or synthesis theorem, and dense arity-`d` input already has `4^d` scalar slots. `ExactGateCompiler` proves consequences only from supplied compiler data and does not instantiate the claimed `2^(d+1)` bound (C-013) |
| `FER03-RES-CONSTANT-D` | L1184 | With fixed `d` and a valid synthesis theorem, overhead is constant per gate. | P1 / `Circuit/Compilation.lean`, `Simulation/CompiledResources.lean` | **partially formalized** conditionally: a supplied exact compiler with per-image-gate count `≤ K` yields compiled count and canonical serial depth `≤ s*K`; fixed arity alone does not provide such a compiler or constant `K` (C-013/C-014) |
| `FER03-RES-QUATERNIONIC-UNIVERSAL-SET` | L1186 | Existence of finite quaternionic universal gate set. | P2 / 9-COVERAGE | **unresolved**: explicitly conjectural in paper |
| `FER03-RES-UNIFORM-CIRCUIT-WITHOUT-UNIVERSAL-SET` | L1186 | Alternative uniformly generated bounded-description gate interface. | P2 / `Circuit/Ordering.lean`, `Circuit/Compilation.lean` | **partially formalized** only at the finite semantic level: `LegalSchedule` and `ExactGateCompiler` are supplied mathematical data, not evidence of an encoded computable or uniform generator; no discrete description language or runtime model is present |
| `FER03-RES-EXPLICIT-MATRIX-ARITY` | L1188 | Full matrix descriptions of polynomial size imply `d=O(log n)`. | P1 / `Circuit/DescriptionCost.lean` | **partially formalized** by the exact finite facts `denseEntrySlots = 4^d` and `localArity_le_log_four_of_denseEntrySlots_le`; the asymptotic polynomial-size premise and scalar bit encoding are not formalized, so no bit-complexity conclusion follows |
| `FER03-RES-ARBITRARY-D-OVERHEAD` | L1188 | Polynomial overhead conclusion from logarithmic arity. | P1 / `Circuit/DescriptionCost.lean`, `Circuit/Compilation.lean` | **partially formalized**: exact dense-slot/logarithmic-arity facts and conditional `s*K` compiler bounds are proved, but no theorem derives `K=O(n)` or any primitive-count/runtime overhead from arity alone (C-013/C-019) |
| `FER03-RES-TABLE-1` | L1190–1198 | Width/size/depth summary after binary synthesis. | P1 / `Circuit/Depth.lean`, `Circuit/DescriptionCost.lean`, `Circuit/Compilation.lean`, `Simulation/Resources.lean`, `Simulation/CompiledResources.lean` | **corrected and proved** in three explicitly separated models: source resources; the literal abstract image (`n+1` width, `s` image gates, support depth exactly `s`, dense slots factor `4`); and a conditionally compiled target (exact summed count and canonical serial depth `≤s*K` only from a supplied exact compiler/per-gate bound). The source's unconditional `2^(d+1)` count and `t*2^(d+1)` depth are rejected (C-013/C-014) |
| `FER03-RES-ABSTRACT-LITTLE-OVERHEAD` | Abstract L18–20, L1239 | Similar width/size and efficient simulation. | P1 / primary simulation leaves, `Simulation/Resources.lean`, `Simulation/Postprocessing.lean` | **partially formalized**: exact abstract width/count/arity, dense-slot factors, literal support depth, and deterministic outcome preservation are proved; “efficient” uniform compilation, finite precision, synthesis, and BQP conclusions lack the required encoded computational model (C-019/C-024) |

## Interpretation, converse, and physical claims

| ID | Source | Disposition target | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-INT-QUATERNION-PHASE-QUBIT` | L1200–1204 | Document component-subspace intuition; do not claim a qubit literally stores all unit-quaternion degrees of freedom. | P2 / `State/Complexification.lean` | **partially formalized**: `complexColumn0`/`complexColumn1`, their sector formulas, reconstruction, norm preservation, and arbitrary pure-top measurement theorem give the exact two-complex-sector content. The claim that one top qubit “stores” a unit-quaternion phase is retained only as intuition, not an equality of state spaces or degree-of-freedom theorem |
| `FER03-INT-NOT-NPLUS1-REBITS` | L1204 | Record only a limitation of the presented method; no lower bound follows. | P2 / 9-COVERAGE | **partially formalized** as correction C-017; no impossibility theorem |
| `FER03-INT-ORDER-DEPENDENCE-INTRINSIC` | L1223–1229, Fig. 7 | Prove algebraic explicit witness; separate “non-local time” interpretation. | P1 / `Circuit/OrderingWitness.lean`, `Simulation/OrderingWitness.lean` | **corrected and proved** at the algebraic/observable level by the two-schedule disjoint unitary witness and its exact complex translation; this is an existential example only. The paper's universal and physical “non-local time” interpretations are not Lean conclusions (C-018) |
| `FER03-INT-FREE-NONLOCAL-CORRELATION` | L1231, FN10 | Distinguish gate-order dependence from entanglement/signaling. | P2 / `Circuit/ProductInputOrderingWitness.lean` | **partially formalized**: the Stage 7 disjoint local unitary gates act on a normalized, pointwise-factorized ground input; their two legal orders produce normalized outputs that are not even equivalent under unit quaternionic right phase. All four computational-basis weights nevertheless agree pointwise. This proves an algebraic ray-level order effect from one product input, not entanglement, signaling, causality violation, mixed-state behavior, or cryptographic security |
| `FER03-INT-BIT-COMMITMENT` | L1231 | Source supplies no hiding/binding definitions or security proof. | P3 / 9-COVERAGE | **intentionally excluded**: the source gives only an informal scenario, with no protocol syntax, adversary model, hiding definition, binding definition, composability convention, or security proof. The product-input ordering diagnostic is not a substitute for any of these obligations |
| `FER03-INT-RULE-OUT-PHYSICALITY` | L1233, L1245–1249 | Philosophical/external information-theoretic interpretation. | P3 / 9-COVERAGE | **intentionally excluded** from Lean theorem surface |
| `FER03-INT-PREFERRED-PATH-BQP` | L1239–1241 | Conditional documentation after corrected uniform resource theorem. | P2 / `Simulation/Scheduled.lean`, `Simulation/Postprocessing.lean`, `Simulation/Resources.lean` | **partially formalized**: every supplied finite legal schedule is simulated exactly and preserves deterministic finite output processing, but BQP containment requires encoded uniform families, computable approximation/synthesis, and polynomial runtime, none of which is formalized |
| `FER03-INT-NONSURJECTIVE-CONVERSES` | L1251 | Prove exact image/properness facts with corrected target and low-dimensional exceptions; do not infer all operational lower bounds. | P1 / `Matrix/ProperImage.lean` | **corrected and proved** by exact low-dimensional witnesses: `realWitness_specialOrthogonal_not_realify` gives an `SO(4)` matrix outside every complex `2 × 2` realification; `complexWitness_specialUnitary_not_complexify` gives an `SU(4)` matrix outside every quaternionic `2 × 2` complexification; and `directWitness_specialOrthogonal_not_directRealify` gives an `SO(4)` matrix outside every direct quaternionic `1 × 1` realification. C-016 corrects the complex target ambiguity and records the unformalized doubled-map `N=1` onto exceptions; no operational lower bound follows |
| `FER03-INT-DESTRUCTIVE-INTERFERENCE-CAUSE` | L1253–1257 | Conjectural explanation of quantum speedup. | P3 / 9-COVERAGE | **intentionally excluded** as a mathematical theorem |

## Explicit open questions

The paper asks, rather than proves, each item below.  They are retained for
source completeness and are **intentionally excluded** from the completion
requirements of this library unless a later stage proves a nearby finite result.

| ID | Source | Question | Status |
|---|---|---|---|
| `FER03-OPEN-ALL-EVALUATION-PATHS` | L1243 | Can a model coherently follow all gate-evaluation paths? | **intentionally excluded**: explicit source question, not a claimed result |
| `FER03-OPEN-PATH-WEIGHTS` | L1243 | Could paths carry probabilities or amplitudes? | **intentionally excluded**: no multi-path semantics or weighting rule is supplied |
| `FER03-OPEN-PATH-INTERFERENCE` | L1243 | Could paths interfere constructively or destructively? | **intentionally excluded**: no path superposition or interference model is supplied |
| `FER03-OPEN-BEYOND-QUANTUM-SPEEDUP` | L1243 | Could path parallelism exceed quantum computational power? | **intentionally excluded**: speculative complexity question with no formal model |
| `FER03-OPEN-QUATERBIT-TELEPORTATION` | L1251 | How many classical bits are needed to teleport a quaterbit? | **intentionally excluded**: no quaternionic channel, teleportation protocol, discard operation, or communication model is defined; same-space real/complex unitary-channel equality does not address the question |
| `FER03-OPEN-CHANNEL-CAPACITY` | L1251 | How do quaternionic amplitudes affect channel capacities? | **intentionally excluded**: no quaternionic, noisy, or capacity framework is defined; the finite same-space unitary-channel equivalence layer has no coding or information-rate semantics |
| `FER03-OPEN-COMMUNICATION-COMPLEXITY` | L1251 | How does communication complexity change? | **intentionally excluded**: no communication model or cost measure is defined |
| `FER03-OPEN-REBIT-INFORMATION-THEORY` | L1251 | What analogous distinctions occur for rebits? | **intentionally excluded**: broad research question, not a source theorem |
| `FER03-OPEN-OTHER-SCALARS` | L1253–1257 | What coherent models arise from octonions or finite fields? | **intentionally excluded**: outside the associative real/complex/quaternion scope |
| `FER03-OPEN-ALGEBRAIC-COMPLEXITY-PICTURE` | L1257 | How much does amplitude structure affect complexity classes? | **intentionally excluded**: speculative complexity-class program without encoded models |

## Figure, table, and footnote coverage

- Figure 1 maps to `FER03-R-SERIAL-COMPOSITION`.
- Figure 2 maps to `FER03-R-QUANTUM-GATE-PADDING`.
- Figure 3 maps to `FER03-R-NONFACTORING-OUTPUT`.
- Figure 4 maps to `FER03-R-REAL-GATE-PADDING`.
- Figure 5 maps to `FER03-R-ANCILLA-REUSE` and L03.
- Figure 6 maps to `FER03-Q-KRONECKER-INTERCHANGE` and
  `FER03-Q-PARALLEL-ORDER-DEPENDENCE`.
- Figure 7 maps to `FER03-INT-ORDER-DEPENDENCE-INTRINSIC`.
- Table 1 maps to `FER03-RES-TABLE-1`.
- Footnotes 1–10 are covered respectively by the finite-dimensional,
  antiunitary, routing, historical attribution, topological-sort, finite-
  precision, phase analogy, quaternion non-anticommutativity, nomenclature, and
  non-entanglement qualifications above.  Historical attributions and mere
  nomenclature are intentionally excluded from Lean declarations.

## Central dependency spine

```text
Co/Wd and re/im scalar identities
  → multiplicative, star-preserving matrix embeddings
    → unitary/orthogonal image results
      → state embeddings and basis-weight preservation
        → noncommutative-safe local gate placement
          → ordered circuit evaluation
            → corrected Theorems 2 and 4
              → Corollary 1, ordering witnesses, and defensible resource bounds
```
