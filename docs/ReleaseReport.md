# Quaternionic Computing Lean Library — Release Report

- Release date: 2026-07-10
- Project version: 0.1.0
- Lean: 4.31.0
- Mathlib: v4.31.0 (`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`)

## Outcome

This repository reconstructs the important finite-dimensional mathematics of
Fernandez and Schneeberger's *Quaternionic Computing*
(`quant-ph/0307017v2`) as a reusable Lean library. At the Stage 4C checkpoint,
three stable public leaves and one non-root diagnostic leaf extended the
previous 65-source tree to 69 Lean sources including the public root. Stage 5
adds the certified basis-behavior core, evaluator-backed circuit layer, and a
non-root complete audit, bringing the tree to 72 Lean sources including the
public root. Stage 6 adds three stable density/effect/separation leaves and one
non-root complete audit, bringing the checkpoint tree to 76 Lean sources
including the public root. Stage 7 adds the channel core, real/complex phase
kernel, evaluator-backed circuit lift, and non-root complete audit, bringing
the checkpoint tree to 80 Lean sources including the public root. Stage 8 adds
three stable hierarchy leaves and one non-root complete audit, bringing the
checkpoint tree to 84 Lean sources including the public root. Stage 9A adds the
directional cross-model relation leaf, its concrete representative-encoding
leaf, and one non-root audit, bringing the checkpoint tree to 87 Lean sources
including the public root. Stage 9B adds the stable proof-bearing simulation
wrapper leaf and extends the existing non-root audit, bringing the checkpoint
tree to 88 Lean sources including the public root. Stage 9C adds the stable
outcome-decoder and semantic-outcome leaves and extends postprocessing plus the
non-root audit, bringing the checkpoint tree to 90 Lean sources including the
public root. Goal 2 remains active: approximation, registry closure, and the
final release audit are later stages.

The paper was treated as a mathematical source rather than a specification.
Every important inventory item has one terminal disposition: among 101 rows,
23 are proved as stated, 33 corrected and proved, 26 partially formalized, 16
intentionally excluded, and 3 unresolved.  The correction log contains 27
independently checked issues or scope repairs.

No completed module contains `sorry`, `admit`, an unexplained project axiom,
or an unsafe shortcut.

## Formalized mathematics

### Scalars

- Mathlib's real quaternions are used directly.
- The paper's complex/`j` decomposition `q = z + wj` is reconstructed and
  proved injective.
- Multiplication, conjugation, norm-square, and `i`/`j`/`k` order identities are
  checked componentwise.
- The paper's quaternionic left-phase convention is disproved by an explicit
  norm-preserving gate and replaced by unit phase on the right.
- Complex and quaternionic right-phase relations preserve normalization,
  basis weights, total weight, and compatible matrix evolution.

### Semantic equality and phase

- Literal operator equality and chronological-circuit evaluator equality have
  separate names from every observational or phase relation.
- `RealRay`, `ComplexRay`, and `QuaternionRay` are literal quotients of
  normalized representatives by exactly real sign, complex unit right phase,
  and quaternionic unit right phase. `RebitRay`, `QubitRay`, and
  `QuaterbitRay` are their two-level aliases.
- Ray constructor equality is exactly the corresponding representative
  relation; for real rays it is exactly equality or pointwise negation. The
  quotient interface supplies representative existence, induction, invariant
  lifting, and function extensionality without selecting a canonical
  representative.
- Normalized rays exist exactly when their finite index type is nonempty, with
  explicit empty instances at dimension zero.
- Computational-basis distributions, basis and finite-event weights, and
  deterministic pushforwards descend to real, complex, and quaternionic rays,
  with exact representative, identity, and composition laws.
- Supplied unitary matrices and explicitly locally-unitary chronological
  circuits act on all three ray types. Identity and empty circuits act
  trivially; first `U` then `V` is `V * U`, and `C ++ D` acts first by `C`,
  then by `D`, including at the inhabited zero-wire circuit basis.
- The descent API does not act by arbitrary matrices or uncertified circuits
  and asserts no density, effect, channel, or approximation result.
- Complex-to-real ray encoding uses the separate unit-rotation quotient
  `RealSectorOrbit`, with `ComplexRay I ≃ RealSectorOrbit I` and exact bottom
  marginal distribution preservation. Neither canonical representative
  column defines an ordinary target-`RealRay` map on a nonempty index type;
  phases survive that sign quotient exactly at `±1`. This closes the two
  transferred ray rows as proved as stated and records correction C-027.
- Fixed-input, all-basis-input, and all-normalized-pure-input basis agreement
  are separate predicates, with finite distributions, events, and
  deterministic pushforwards downstream.
- `BasisTransition` is only a raw phased-column diagnostic.
  `BasisPermutationImplementation` instead carries an explicit permutation and
  certifies every input column; `SameBasisBehavior` can be formed only from two
  such certificates and compares their permutations.
- On certified real, complex, and quaternionic operators, same basis behavior
  is equivalent to the correctly sided input phase, output phase, and
  `BasisMeasurementEq`. `BasisClassicalCircuit` and
  `SameCircuitBasisBehavior` lift these exact characterizations through
  `OrderedCircuit.eval` while storing local unitarity.
- Exact equality and real/complex global phase or quaternionic central sign
  preserve certified behavior. No converse to one global phase and no generic
  projective, channel, or all-effect result is inferred.
- Two exact rational real unitaries with every entry nonzero have equal empty
  raw transition relations but unequal basis probabilities and no certified
  permutation. Thus the tempting unrestricted transition biconditional is not
  used as classical behavior.
- Real and complex operators and evaluated circuits have distinct global,
  input-column, output-row, and all-pure-input projective-action relations.
- Global phase implies both sided basis phases and projective action. Input
  phase implies basis-input agreement; output phase and projective action imply
  all-pure-input basis agreement.
- Sided composition laws follow chronological order. A common earlier
  projective evolution requires unitarity, and no arbitrary two-sided closure
  is exported. Input- and output-dependent phase families are not promoted to
  channel equality.
- Rational unitary witnesses certify exact/global strictness, input/output
  incomparability, superposition sensitivity, and the separation between
  output-basis probabilities and output rays.
- Quaternionic operators have five side-sensitive comparisons: one central
  real sign, input-column unit phases on the right, output-row unit phases on
  the left, and raw versus normalized all-input right-ray action. The raw and
  normalized projective relations are equivalent for every finite input type;
  on an empty input type both are trivial for distinct but checked reasons.
- Four quaternionic circuit wrappers compare evaluator semantics. Their
  normalized-input quantifier is nonvacuous even on zero wires because
  `BitBasis W` is inhabited; no raw-projective circuit wrapper is exported.
- In finite square dimension at least two, with decidable indices and only the
  first operator assumed unitary, raw or normalized projective action is
  equivalent to one central real sign. Rank one is sharp: the projectively
  trivial scalar operators are exactly the full unit-quaternion family, and
  `j` is an explicit unitary noncentral witness.
- Quaternionic operator-phase results are not promoted to channel or
  all-effect equality. The separate Stage 7 real/complex unitary layer proves
  exactly the justified global/projective channel characterizations.

### Density matrices and physical effects

- `DensityMatrix 𝕜 I` packages exactly a positive-semidefinite finite
  matrix and a trace-one proof. Hermiticity is derived, and an explicit theorem
  proves that no density matrix exists on an empty index type.
- The proof core is generic over `RCLike 𝕜`; the library exposes explicit
  `RealDensityMatrix` and `ComplexDensityMatrix` aliases for its supported
  physical models. No quaternionic density/positivity API is inferred.
- Pure densities are normalized ket--bra matrices, basis densities are their
  computational-basis instances, and constructors from existing normalized
  real and complex states have the expected entries.
- `DensityMatrix.unitaryConjugate U hU ρ` has matrix `U * ρ * Uᴴ` and is
  proved positive semidefinite and trace one. Identity, pure-state
  compatibility, and the chronological law “first `U`, then `V` equals
  conjugation by `V * U`” are exact.
- `Effect 𝕜 I` packages the genuine Loewner interval `0 ≤ E ≤ 1`.
  Zero, identity, complements, normalized rank-one projectors, and basis
  effects are constructed without treating arbitrary matrices as effects.
- `Effect.bornValue E ρ` is the real part of `trace (E * ρ)`. The scalar
  pairing is proved real and nonnegative, the real value lies in `[0,1]`, and
  zero, identity, complement, pure, and basis formulas compile. Basis effects
  on state-derived densities recover the existing real/complex basis weights.
- Genuine physical effects separate arbitrary finite densities:
  `DensityMatrix.eq_iff_forall_effect_bornValue_eq` proves literal density
  equality iff all `Effect` Born values agree. Its reverse direction uses
  normalized rank-one physical effects and quadratic-form polarization, not
  arbitrary trace-test matrices.
- This fixed-pair separation theorem is not `ChannelEq` or
  `AllMeasurementEq` by itself. Stage 7 now supplies those same-space unitary
  relations and consumes this separation theorem. Neither stage adds
  quaternionic mixed-state theory, partial trace, Kraus maps, instruments, or
  arbitrary mixed-top simulation.

### Unitary channels and all physical measurements

- `UnitaryOperator 𝕜 I` bundles a finite `RCLike` square matrix with its
  unitary certificate; `RealUnitaryOperator` and `ComplexUnitaryOperator` are
  the supported model aliases.
- `ChannelEq U V` compares the complete evolved density matrix for every
  density input. `AllMeasurementEq U V` compares every genuine physical-effect
  Born value for every density input. `channelEq_iff_allMeasurementEq` proves
  them equivalent through physical-effect separation, not arbitrary trace
  tests or basis effects alone.
- Chronological composition is explicit: `U.followedBy V` stores `V * U` and
  evolves first by `U`, then by `V`. Both relations are equivalence relations
  and are congruent under this composition.
- Raw real/complex projective action is equivalent to the existing normalized
  relation by a checked zero/nonzero normalization proof. Global real
  sign/complex phase implies channel equality without an inhabited premise,
  and channel equality implies raw and normalized projective action.
- On an explicitly nonempty finite matrix index, global sign/phase, raw
  projective action, normalized projective action, `ChannelEq`, and
  `AllMeasurementEq` are equivalent. The proof uses basis columns and pairwise
  sums for `V * Uᴴ`, with no determinant or dimension-at-least-two argument.
- Empty-index channel equality is physically vacuous because no density input
  exists. Separate empty-index theorems prove exact equality of the unique
  square matrices and derive global phase from that matrix fact.
- `UnitaryCircuit` bundles a chronological circuit with its local-unitarity
  certificate. `CircuitChannelEq` and `CircuitAllMeasurementEq` compare its
  derived evaluator, preserve exact equality and chronological append, and
  have the same real/complex global/projective characterizations. `BitBasis W`
  is canonically inhabited even at zero wires, so these circuit theorems need
  no redundant nonempty premise.
- The channel API is same-space and real/complex-style only. It adds no
  quaternionic channels, cross-model channel relation, partial trace, Kraus
  maps, instruments, decoded marginal, mixed-top simulation, or capacity
  result.

### Same-space semantic hierarchy

- `Hierarchy/OutputPhase.lean` proves, for arbitrary rectangular matrices with
  only a finite input type, that all-normalized-pure-input computational-basis
  agreement is exactly one output-row sign/phase. The quaternionic phase acts
  on the left. The theorem needs no output finiteness, decidable equality,
  nonempty index, unitarity, or nonzero-row premise.
- `Hierarchy/State.lean` characterizes equality of finite distributions by
  equality of every singleton event, every finite event, and every
  deterministic pushforward to a finite target in the same universe. Its
  state wrappers preserve the distinction between exact representatives,
  scalar-correct rays, basis weights, and distributions.
- `Hierarchy/Operator.lean` supplies useful real/complex channel and
  all-effect consequences, direct global/projective characterizations, and
  evaluator-backed circuit lifts. Its quaternionic contribution is limited to
  the output-left-phase circuit characterization; no quaternionic channel is
  introduced.
- The three stable leaves export exactly `9 + 13 + 27 = 49` declarations. The
  non-root hierarchy audit allocates all 49, checks rectangular and empty
  boundaries, and packages exact failed-converse witnesses. In particular,
  output-row phase and basis-only agreement do not imply channel equality, and
  equal basis distributions do not determine a ray.

### Directional cross-model certificates

- `ExactStateEncoding` is the source-to-target certificate
  `Function.LeftInverse decode encode`; it gives exact reconstruction on the
  encoder image and injectivity, not generic surjectivity or a carrier
  equivalence.
- `LosslessStateEncoding` additionally preserves supplied total-weight
  functionals. `ExactOperatorEmbedding`, `StateIntertwining`, and the decoded
  basis-weight/distribution predicates keep their embedding, encoders, decoders,
  and observation scope explicit.
- The `AllTop...` variants quantify an explicit `Top` parameter. The generic
  relation does not manufacture purity, normalization, product structure,
  mixedness, a marginal, channel behavior, or all-effect behavior.
- Both canonical complex-to-real columns and both canonical
  quaternion-to-complex columns are exact `ℝ`-linear coordinate equivalences
  with displayed inverses. Their normalized restrictions are equivalences of
  representative carriers.
- These concrete bijections are not ray or behavioral equivalences. Complex
  phase still requires `RealSectorOrbit`; the normalized `Rebit`/`Qubit`
  top-sector values used by the pure-state formulas are coefficient parameters,
  not product-factor certificates. The non-product witness makes that boundary
  explicit.
- Stage 9A classifies the representative encodings and generic relation
  vocabulary. Stage 9B adds exact operator/state/reindex/schedule/compiler
  wrappers for all eleven assigned frozen families. Their coefficient pairs
  are raw coordinates, and schedules and compilers are supplied data. Stage 9C
  adds explicit full-target one/two-wire decoders and 18 proof-bearing outcome
  wrappers at the raw-weight, normalized-distribution, finite-event, and
  deterministic-pushforward levels.

### Matrix embeddings and groups

- `Matrix.realify` maps compatible complex matrices to doubled real block
  matrices and preserves zero, addition, multiplication, identity, adjoint,
  and injectivity.
- `Quaternion.complexify` gives the corresponding quaternion-to-complex block
  map without using commutative algebra illegally.
- Both primary maps are bundled as injective star-monoid/group maps.
- Complex unitaries realify into `SO(2N)`.  The missing source determinant
  argument is repaired by
  `det(realify A) = Complex.normSq (det A)`.
- Quaternionic unitaries complexify into complex unitary matrices preserving
  the canonical symplectic form.  Their determinant is proved real and equal
  to `1` or `-1`; the positive-sign refinement remains explicitly unresolved.
- Equation 63's direct quaternion-to-real map is formalized with four sectors,
  all sixteen coordinate formulas, and target cardinality `4N`.  It is exactly
  `realify (complexify A)` after the simultaneous sector permutation
  `[3,1,0,2]`, with no additional signs.  Quaternionic unitaries embed into
  `SO(4N)` and are multiplicatively equivalent to their image.
- Explicit matrices prove qualified non-surjectivity in `SO(4)`, `SU(4)`, and
  the direct rank-one `SO(4)` target.  These are matrix facts, not operational
  lower bounds.

### States and measurements

- `RealState`, `ComplexState`, and `QuaternionState` are normalized finite
  columns with nonnegative squared-norm basis weights summing to one.
- Both columns of each doubled state embedding are defined, reconstructed,
  proved injective, norm-preserving, appropriately real-linear, and compatible
  with matrix evolution. Stage 9A strengthens each raw canonical coordinate map
  to an explicit `ℝ`-linear equivalence and each normalized representative map
  to an `Equiv`, without inferring a ray or behavioral equivalence.
- Bottom computational-basis probabilities are preserved after summing over
  the added top wire.
- The real rank-one reduced matrices for the two canonical encodings are equal.
- `FiniteDistribution` packages normalized finite outcomes, event weights, and
  deterministic pushforwards.
- `RealRay`, `ComplexRay`, and `QuaternionRay` expose those finite observables
  directly, together with deterministic-pushforward identity and composition.
- Normalized ray evolution is available only from supplied unitaries or
  locally-unitary circuit certificates, with exact matrix and chronological
  order laws and no arbitrary-matrix or channel interpretation.
- A normalized rational complex state has a canonical real encoding that is
  provably not a pure top/bottom product.

### Circuits, ordering, and simulation

- `PlacedGate` derives a global operator from an explicit local/complement wire
  split.  Placement works on arbitrary noncontiguous finite supports and is
  multiplicative, adjoint-preserving, injective, and unitary-preserving over
  noncommutative coefficients.
- `OrderedCircuit` is a chronological list whose denotation is the reverse
  matrix product.  Exact fixed-value checks guard the order convention.
- Each primary gate translation adds one shared top wire, commutes with actual
  contextual placement, preserves local unitarity, and increases local arity
  by exactly one.
- `LegalSchedule` lists every gate occurrence once and certifies precedence.
  Pairwise commuting denotations give schedule independence.
- A disjoint pair of quaternionic unitary gates has two legal orders with
  distinct operators and distinct normalized measurement outcomes on one
  input.
- On a normalized product ground input, the same orders produce output rays
  that are not right-phase equivalent while every computational-basis weight
  agrees.  This separates algebraic state dependence from signaling or
  cryptographic claims.
- Corrected forms of Theorems 2 and 4 prove, separately, whole-operator
  embedding, state evolution, normalized bottom probability equality, exact
  gate count, width `+1`, and per-gate arity `+1`.
- Every supplied legal quaternionic schedule inherits the exact
  quaternion-to-complex simulation.
- Corollary 1 is proved by the visible composition of the two wire-facing
  translators, giving width and arity `+2` and four-sector probability
  preservation.  The Equation 63 API is supplementary and matrix-level; no
  second direct placed-gate translator is claimed.

### Resources

- `SupportLayering` gives an explicit support-disjoint depth certificate.  The
  literal shared-top translations have depth exactly the source gate count.
- A dense `d`-wire matrix has exactly `4^d` scalar-entry slots.  The primary
  translations multiply total slots by `4`; their composition by `16`.
- Empty precedence has exactly `s!` chronological orders.  No factorial count
  is asserted for an arbitrary precedence relation.
- `ExactGateCompiler` is supplied certified data, not an assumed compiler.  It
  yields exact compiled semantics/count and `s*K` count/serial-depth bounds only
  from an explicit per-gate bound.
- Finite event and deterministic postprocessing equality follow from the
  normalized bottom distributions.

## Main public API

Import the complete supported surface with:

```lean
import QuaternionicComputing
```

Representative exported declarations include:

| Area | Main declarations |
|---|---|
| Quaternion components | `Quaternion.complexPart`, `jPart`, `eq_complexPart_add_jPart_mul_j`, `complexPart_mul`, `jPart_mul` |
| State/ray phase | `Real.SignEquivalent`, `Complex.RightPhaseEquivalent`, `Quaternion.RightPhaseEquivalent`, the three normalized `*StatePhaseEq` relations, and the quotient types `RealRay`, `ComplexRay`, `QuaternionRay` with `RebitRay`/`QubitRay`/`QuaterbitRay` aliases |
| Ray quotient core | the three `*Ray.mk_eq_mk_iff` theorems, `RealRay.mk_eq_mk_iff_eq_or_eq_neg`, representative `exists_rep`/`inductionOn`/`lift` APIs, and `realRay_nonempty_iff`/`complexRay_nonempty_iff`/`quaternionRay_nonempty_iff` |
| Certified basis behavior | `BasisPermutationImplementation`, `SameBasisBehavior`, `BasisClassicalUnitaryOperator`, `BasisClassicalCircuit`, `SameCircuitBasisBehavior`, the scalar `sameBasisBehavior_iff_*` families, and the certified XOR preparation declarations |
| Densities and effects | `DensityMatrix`, `RealDensityMatrix`, `ComplexDensityMatrix`, `DensityMatrix.pure`, `basis`, `unitaryConjugate`; `Effect`, `RealEffect`, `ComplexEffect`, `Effect.projector`, `basis`, `bornValue`, `bornValue_mem_Icc`; and `DensityMatrix.eq_iff_forall_effect_bornValue_eq` |
| Channels | `UnitaryOperator`, `ChannelEq`, `AllMeasurementEq`, `channelEq_iff_allMeasurementEq`; `RealRawProjectiveActionEq`, `ComplexRawProjectiveActionEq`, the real/complex global/projective `*_iff_channelEq` families; `UnitaryCircuit`, `CircuitChannelEq`, `CircuitAllMeasurementEq`, and their phase/append bridges |
| Semantic hierarchy | `realOutputBasisSignEq_iff_pureInputBasisMeasurementEq`, `complexOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq`, `quaternionOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq`; `FiniteDistribution.eq_iff_eventWeight_eq`, `eq_iff_allPushforward_eq_sameUniverse`; and the channel/all-effect covering-arrow families in `Semantics.Hierarchy.Operator` |
| Cross-model certificates | `ExactStateEncoding`, `LosslessStateEncoding`, `ExactOperatorEmbedding`, `StateIntertwining`, `DecodedBasisWeightAgreement`, `DecodedDistributionAgreement`, the three `AllTop...` relations, and the four canonical `*LinearEquiv`/`*StateEquiv` values |
| Operator/circuit phase | `RealGlobalSignEq`, `ComplexGlobalPhaseEq`, the real/complex input-, output-, and projective-action relations; `QuaternionCentralSignEq`, `QuaternionInputRightPhaseEq`, `QuaternionOutputLeftPhaseEq`, `QuaternionRawProjectiveActionEq`, `QuaternionProjectiveActionEq`; their evaluator-backed circuit wrappers, measurement arrows, and sided composition laws |
| Quaternion projective kernel | `quaternionRawProjectiveActionEq_iff_projectiveActionEq`, `quaternionProjectiveActionEq_iff_centralSignEq_of_unitary`, `quaternionRankOneScalar_projectiveActionEq_iff_normSq_eq_one`, `quaternionRankOneJ_exception` |
| Complex → real matrices | `Matrix.realify`, `realify_mul`, `realify_conjTranspose`, `realify_det`, `realify_mem_specialOrthogonal` |
| Quaternion → complex matrices | `Quaternion.complexify`, `complexify_mul`, `complexify_conjTranspose`, `complexify_mem_unitary`, `complexify_mem_symplectic` |
| Direct quaternion → real | `Quaternion.directRealify`, `directRealify_eq_reindex`, `directRealify_mem_specialOrthogonal`, `directRealifyUnitaryEquivImage` |
| States | `State.NormalizedState`, `RealState`, `ComplexState`, `QuaternionState`, `realColumn0`, `complexColumn0` |
| Circuits | `Circuit.PlacedGate`, `placeOnSupport`, `OrderedCircuit.eval`, `LegalSchedule`, `basisPreparationGate` |
| Simulations | `Simulation.complexToReal_exactSimulation`, `quaternionToComplex_exactSimulation`, `scheduledQuaternionToComplex_exactSimulation`, `quaternionToReal_exactSimulation` |
| Resources | `Circuit.SupportLayering`, `PlacedGate.denseEntrySlots`, `ExactGateCompiler`, `allChronologicalOrders` |
| Outcomes | `State.FiniteDistribution`, `realifyCircuitBottomDistribution_eq`, `complexifyCircuitBottomDistribution_eq` |
| Diagnostics | `OrderingWitness.output_basis00_weight_ne`, `ProductInputOrderingWitness.ground_outputs_not_rightPhaseEquivalent`, `NonProductWitness.encodedState_not_pureTopBottomProduct` |

The full paper-to-declaration mapping is in `Traceability.md`.

## Project structure

```text
QuaternionicComputing/
  Scalar/       quaternion decomposition and phase correction
  Matrix/       embeddings, group/determinant results, image witnesses
  State/        normalized columns, phase quotients, encodings, finite distributions
  Semantics/    exact, phase, hierarchy, density/channel, and directional simulation APIs
  Circuit/      placement, chronology, scheduling, costs, diagnostics
  Simulation/   exact simulations, resources, examples, postprocessing
  AxiomAudit.lean
QuaternionicComputing.lean   public root
```

`Architecture.md` explains the dependency layers.  `Conventions.md` fixes
scalar sides, multiplication order, adjoints, basis orders, state/ray/outcome
distinctions, and resource meanings.  `MathlibAPI.md` records the selected
mathlib interfaces and noncommutative boundaries.

## Material corrections

The detailed source locations, diagnoses, proofs, and dependent effects are in
`Corrections.md`.  In summary:

1. Source metadata contains conflicting dates.
2. The realification group target is `SO(2N)`, and the construction uses
   `U(N)`, not merely `SU(N)`.
3. Quaternionic complexification has complex dimension `2N`.
4. The paper omits the determinant-one proof for quaternionic
   complexification; only the justified `±1` result is exported.
5. Quaterbit normalization omits the displayed `= 1`.
6. Quaternionic state/ray phase must act on the right. The separate operator
   classification permits only a central real sign as matrix-wide global
   phase, with the full unit-quaternion family proved only as the sharp
   rank-one projective exception.
7. State embeddings are real-linear, not silently complex/quaternion-linear.
8. The source gives the wrong codomain for `h₀` and `h₁`.
9. The stated noncommutative Kronecker condition names the wrong crossing
   factors and overstates necessity.
10. “Exact simulation” is split into typed operator, state, and observable
    conclusions.
11. The displayed quaternionic tensor embedding is malformed and is replaced
    by its block matrix.
12. Lemma 9 uses an undefined final state.
13. The generic elementary-gate decomposition bound lacks a gate library and
    is unsupported by the dense description size.
14. The resource discussion confuses `n` with gate count `s` and gives an
    incompatible depth formula.
15. The multi-top `O(log s)` depth claim has no construction.
16. The converse discussion has an ambiguous/wrong group target and ignores
    low-dimensional exceptions.
17. Failure of one method to use `n+1` rebits is not an impossibility theorem.
18. Quaternionic order dependence is existential, not universal.
19. Runtime and BQP conclusions require discrete encodings and uniformity.
20. The realification proof also omits determinant one; this gap is repaired.
21. The source state-intertwining calculations are dimensionally ill-typed.
22. Lemma 8 omits the critical noncommutative placement proof.
23. A Hilbert space alone does not supply coherent local circuit semantics.
24. Exact algebraic matrices and finite-precision descriptions are different
    models.
25. Equation 63 embeds into `SO(4N)` and is always equivalent to its image; at
    rank one the explicit `SO(4)` witness proves it is not onto the full target.
26. Ground-state “without loss of generality” hides state-preparation and
    uniformity assumptions; only the known basis-input reduction used here is
    packaged as a gate.
27. Physical source values are rays before representative embeddings are
    applied. Complex phase becomes a doubled-real sector rotation, not
    ordinary target-`RealRay` equality; representative intertwining and
    decoded bottom outcomes remain exact.

## Unresolved, partial, and excluded scope

Three inventory claims remain unresolved rather than assumed:

- the unconstructed multi-top `O(log s)` depth alternative; and
- the claimed generic `2^(d+1)` elementary-gate decomposition; and
- existence of the conjectured finite quaternionic universal gate set.

In addition, the positive determinant branch of the partially formalized
quaternionic group theorem remains an isolated proof obligation: the library
proves `det = 1 ∨ det = -1`, but not the general `det = 1` refinement.

Important partial boundaries include arbitrary mixed top states, generic
partial trace, Kraus maps, instruments, quaternionic density/channel
positivity, cross-model channel relations, physical swap synthesis and routing
cost, uniform circuit generators, finite scalar encodings,
approximation/error accumulation, generic unitary synthesis, randomized
postprocessing, preprocessing runtime, and BQP containment. Normalized ray computational-basis observables,
deterministic pushforwards, unitary evolution, and locally-unitary circuit
evolution descend with exact identity and composition laws. The complex-to-real
embedding-orbit boundary is also complete: the rebit and complex-state-ray
source rows are now proved as stated and `closedByGoal2`. This does not settle
arbitrary mixed top states, the paper's phase-kickback interpretation, partial
trace, or cross-model channel/all-input/all-effect semantics. Stages 6 and 7
do provide finite same-space real/complex densities, genuine effects,
fixed-pair separation, and unitary channel/all-effect equality; they do not
supply those missing cross-model constructions.
Stage 9A supplies generic directional comparison certificates and complete
representative-coordinate bijections. Stage 9B now gives the Goal 1
operator/state, Equation 63 reindexing, placed-gate, supplied-schedule,
composed, and conditional-compiler comparisons proof-bearing wrappers at their
exact scopes. The decoded probability/distribution/event/postprocessing
families now have Stage 9C wrappers whose source and full target carriers and
decoders remain visible. Raw point weights need no unitarity; normalized
distribution/event/pushforward results require local unitarity. Neither
checkpoint weakens the exact Goal 1 theorems or promotes them to product/mixed-
top, partial-trace, cross-model channel/all-effect, randomized, or resource
claims.

External/historical results, physical causality interpretations, bit
commitment, channel/communication questions, alternative scalar systems, and
the paper's explicit research questions are intentionally excluded with an
individual traceability disposition.  No excluded or unresolved claim is
represented by an axiom.

## Build and audit results

The release is pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.  Verification from the project root uses:

```sh
lake build
lake build QuaternionicComputing.AxiomAudit
```

The Stage 3B verification run completed adjacent builds (2,352 jobs), all
three real/complex operator-phase targets including the diagnostic leaf (2,355
jobs), the public root (2,559 jobs), the explicit axiom audit (2,559 jobs), and
the full cached project build (2,559 jobs), covering the 53-source Stage 3B
tree. Stage 3C separately completed a focused build of the quaternionic
kernel (2,354 jobs), the non-root quaternionic diagnostic leaf (2,356 jobs),
and the public root (2,562 jobs), plus strict warning-as-error checks of the
three public quaternionic leaves, root, diagnostic leaf, and axiom audit.
That completed the 57-source Stage 3C tree. Stage 4A adds the public ray core
and its non-root diagnostic leaf. Focused builds completed 2,346 jobs for
`State.Ray` and 2,347 for `State.RayAudit`; the public root completed 2,563,
and the combined ray/audit/root/axiom target completed 2,565. Stage 4B adds five
public leaves plus the non-root `State.RayDescentAudit` diagnostic. The helper
leaves' combined build completed 2,348 jobs; the focused diagnostic build
completed 2,361; the public root and standalone axiom audit each completed
2,568; and the combined five-public-leaf/diagnostic/root/audit target completed
2,570. That Stage 4B checkpoint had 65 Lean sources, 64 below
`QuaternionicComputing/` plus the public root. Existing dependency checkouts
remained pinned by the manifest; network bootstrap from a brand-new clone was
not rerun in this restricted environment.

Stage 4C contributes 84 stable declarations: 66 in the direct rotation/orbit
core, ten in the bottom-observable descent leaf, and eight in the exact
ordinary-real-ray boundary leaf. The three public leaves pass strict focused
compilation. Five aggregate theorems in the non-root
`State/RealificationOrbitAudit.lean` consume all 84 declarations with exact
allocation `28/13/25/10/8`; concrete examples distinguish source-ray and
sector-orbit equality from ordinary real-ray and full doubled-distribution
equality while preserving the bottom marginal. The four-leaf focused build
completed 2,355 jobs. The combined adjacent state/simulation, public-root,
explicit-audit target completed 2,573 jobs, and the cached default build
completed 2,571 jobs. All four Stage 4C leaves, the public root, and the axiom
audit pass warning-as-error compilation.

Stage 5 contributes 134 stable declarations: 90 in
`Semantics/BasisBehavior.lean` and 44 in
`Semantics/BasisBehaviorCircuit.lean`. Fourteen exact-allocation aggregates in
the non-root `Semantics/BasisBehaviorAudit.lean` consume the full surface as
90 core declarations and 44 circuit declarations, with no uncovered export.
The diagnostic leaf also checks empty indices, the inhabited zero-wire circuit
basis, a nonidentity Boolean permutation, all-input XOR behavior, and the
separate one-ground-input preparation theorem. Its two rational unitary
witnesses prove equal empty raw transition relations, no certified
permutations, and unequal `false → false` basis weights `9/25` and `25/169`.
The core, circuit, and diagnostic leaves pass focused builds and
warning-as-error source checks. All 18 local Stage 5 axiom endpoints use exactly
`propext`, `Classical.choice`, and `Quot.sound`. The integrated public-root
build completed 2,573 jobs; the root axiom audit contains 330 commands, 25 of
them Stage 5 endpoints.

Stage 6 contributes 97 stable declarations: 40 in
`Semantics/Density.lean`, 52 in `Semantics/Effect.lean`, and five in
`Semantics/EffectSeparation.lean`. Eight exact-allocation aggregates in the
non-root `Semantics/DensityAudit.lean` consume the complete surface as
`33 + 1 + 6`, `17 + 11 + 20 + 4`, and `5`, with no uncovered named export.
Concrete checks include real and complex pure/basis compatibility, the
genuinely mixed rebit density `(1/2) I`, Born bounds and complementation,
global-sign unitary conjugation, genuine-effect separation, and the exact
empty-index obstruction. All four Stage 6 leaves pass warning-as-error source
checks; the focused diagnostic build completed 2,672 jobs. The integrated
public-root plus explicit-axiom target completed 2,757 jobs. The public root
imports only the three stable leaves and excludes `DensityAudit.lean`.

The Stage 6 root audit adds 24 independent endpoints for a total of 354.
Every root endpoint and all seven local Stage 6 diagnostic endpoints use
exactly the union `propext`, `Classical.choice`, and `Quot.sound`; no
project-specific axiom is introduced. These are Stage 6 checkpoint results,
not by themselves evidence for the Stage 7 channel results recorded below or
for Goal 2 release completion.

Stage 7 contributes 139 stable declarations: 41 in
`Semantics/Channel.lean`, 40 in `Semantics/ChannelPhase.lean`, and 58 in
`Semantics/ChannelCircuit.lean`. Twenty-three exact-allocation aggregates in
the non-root `Semantics/ChannelAudit.lean` consume the full surface as
`20+11+10`, `2+7+7+6+2+2+6+6+2`, and
`2+19+2+10+10+1+2+2+2+4+4`, with no uncovered named export. Its examples
check real and complex global phase, a physically distinct identity/swap
channel, chronological operator/circuit composition, empty-index vacuity, and
the inhabited zero-wire circuit basis.

All three stable leaves and the non-root audit pass warning-as-error source
checks. The focused diagnostic build completed 2,686 jobs; the combined
public-root plus explicit-axiom target completed 2,760; the cached default
build completed 2,759; and the broader adjacent combined target completed
2,763. All 11 local Stage 7 diagnostic endpoints and all 393 public-root
endpoints use exactly `propext`, `Classical.choice`, and `Quot.sound`. The
public root imports only `Channel`, `ChannelPhase`, and `ChannelCircuit`, never
`ChannelAudit`.

Stage 8 contributes 49 stable declarations: nine in
`Semantics/Hierarchy/OutputPhase.lean`, 13 in
`Semantics/Hierarchy/State.lean`, and 27 in
`Semantics/Hierarchy/Operator.lean`. Twelve exact-allocation aggregates in the
non-root `Semantics/HierarchyAudit.lean` consume all 49 declarations. Its
rectangular, empty-index, singleton-distribution, strictness,
certified-classical, schedule, and Kronecker consumers compile without using
impossible normalized empty values.

The three stable leaves and non-root audit pass warning-as-error source checks.
Focused builds completed 2,355 jobs for `OutputPhase`, 2,356 for `State`,
2,693 for `Operator`, and 2,713 for `HierarchyAudit`; the combined hierarchy
audit/public-root/axiom-audit target completed 2,769 jobs. The public root
imports the three stable leaves but never `HierarchyAudit`. All 33 local Stage
8 diagnostic endpoints and all 422 public-root endpoints use only the exact
standard union `propext`, `Classical.choice`, and `Quot.sound`.
The cached default build completed 2,762 jobs, and a warning-as-error downstream
smoke importing only `QuaternionicComputing` instantiated the rectangular
output-phase characterizations, finite-distribution characterizations, and
representative operator/circuit hierarchy arrows.

Stage 9A contributes 58 stable declarations: 38 in
`Semantics/Simulation.lean` and 20 in
`Semantics/SimulationEncoding.lean`. Eleven manifest consumers—nine generic
relation aggregates and two representative-encoding aggregates—allocate the
complete surface. The non-root `Semantics/SimulationAudit.lean` additionally
checks concrete complex-to-real and quaternion-to-complex intertwining,
normalized `Rebit`/`Qubit` coefficient policies, decoded basis weights and
distributions, empty and singleton boundaries, ray non-descent, and the
non-product witness. Its ten local axiom commands are diagnostic.

Focused builds completed 2,345 jobs for `Semantics.Simulation`, 2,350 for
`Semantics.SimulationEncoding`, and 2,368 for `Semantics.SimulationAudit`; the
combined public-root plus explicit-axiom target completed 2,766 jobs. Stage 9A
adds 20 direct public-root audit endpoints, bringing the root audit from 422 to
442 commands. All Stage 9A local and public endpoints remain within the exact
standard union `propext`, `Classical.choice`, and `Quot.sound`.

Stage 9B contributes 16 stable declarations in
`Semantics/SimulationWrappers.lean`. They classify rectangular raw-state
intertwining, Equation 63 reindexing, translated placed-gate denotations,
primary and composed circuit operators/states, one supplied legal schedule,
preservation of the concrete schedule-operator gap, and exact compilation
under supplied compiler data. Six non-root `SimulationAudit` aggregates
allocate them exactly as `2 + 3 + 4 + 3 + 2 + 2`. The audit uses literal
canonical coefficient pairs, rectangular and raw-empty matrices, the existing
unequal schedules, local identity compilers, and zero-wire circuits without
constructing an impossible normalized empty state.

The wrapper leaf focused build completed 2,369 jobs; the extended audit build
completed 2,381; and the combined stable/audit/public-root/axiom-audit target
completed 2,767. Stage 9B adds 16 direct root-audit commands and six local
commands, bringing the checkpoint to 458 root commands and 16 local
`SimulationAudit` commands. Their exact axiom union remains `propext`,
`Classical.choice`, and `Quot.sound`.

Stage 9C adds ten stable decoder declarations in
`Simulation/OutcomeDecoder.lean`, eight new full-target/composed distribution
and postprocessing declarations, and 18 stable wrappers in
`Semantics/SimulationOutcomes.lean`. The one-wire distribution decoder equals
`pushforward tailBits`; the two-wire decoder removes the outer realification
wire and then the inner complexification wire. Five semantic audit aggregates
allocate the wrappers as `2 + 4 + 4 + 4 + 4`, and two infrastructure
aggregates allocate the ten decoder and eight postprocessing declarations.

Focused builds completed 2,347 jobs for `OutcomeDecoder`, 2,361 for the updated
`Postprocessing`, 2,365 for `SimulationOutcomes`, and 2,385 for the extended
audit. The combined stable/audit/public-root/axiom-audit target completed 2,769
jobs. Stage 9C adds 36 direct root commands, bringing the audit to 494, while
the curated local `SimulationAudit` has 20 commands. The root parser finds 491
nonempty and three axiom-free blocks; the local parser finds 19 nonempty and
one axiom-free block. Every endpoint uses a subset, and both collective unions
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Warning-as-error source checks passed for the stable operator-phase, ray,
certified-basis, density, effect, separation, and channel leaves, their
hierarchy and simulation-semantics leaves, their diagnostic leaves, public
root, axiom audit, and all Stage 9C source boundaries. The executable root audit
now contains 494
`#print axioms` commands, including 19 Stage 4C, 25 Stage 5, 24 Stage 6, 39
Stage 7, 29 Stage 8, 20 Stage 9A, 16 Stage 9B, and 36 Stage 9C endpoints. All
20 local
`SimulationAudit` prints,
all 33 local Stage 8 diagnostic prints, all
11 local Stage 7 prints, all seven local Stage 6 prints, all 18 local Stage 5
prints, the retained 12 local Stage 4C prints, and every root endpoint use only
subsets of `propext`, `Classical.choice`, and `Quot.sound`; the collective union
is exactly those three standard axioms. At the Stage 9C checkpoint, the parser
finds 491 nonempty plus three axiom-free root blocks and 19 nonempty plus one
axiom-free local `SimulationAudit` block. See `AxiomAudit.md` for the
interpretation.

At the Stage 4B checkpoint, the independent Goal 2 semantic manifest contained
exactly 487 declarations:
61 from Stage 2, 72 from Stage 3A, 150 from Stage 3B, and 101 from Stage 3C
(44 operator-core, 43 circuit, and 14 kernel declarations), plus 40 from Stage
4A and 63 from Stage 4B. The Stage 4B contribution is 60 observable,
distribution-law, circuit-helper, and evolution declarations plus three
semantic phase-to-quotient bridges. All seven semantic axes remain present,
all names resolve through the public root, and 100 manifest entries are direct
root-audit targets. Stage 4C appends its 84 declarations exactly once, for 571
entries in exact public-source order. All seven axes are nonempty, all 571
names and 59 distinct aggregate consumers resolve, and all 119 direct-audit
labels match actual root commands. The first 487 entries retain structural
SHA-256 `b44178bc6be2adb364fea5a88b88aaebf832b44eb36065435ed5aee89bee194a`;
Stage 5 appends its 134 declarations exactly once, bringing the manifest to
705 entries. The integrated checks resolve all 705 names, 73 distinct
consumers including 14 Stage 5 consumers, and 144 direct-audit labels including
25 Stage 5 labels. Stage 6 appends its 97 declarations exactly once, bringing
the manifest to 802 entries. The current checks resolve all 802 names, 81
distinct consumers including the eight Stage 6 aggregates, and 168
direct-audit labels including 24 Stage 6 labels. The frozen 936-declaration
Goal 1 cohort retains checksum
`65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.

Stage 7 appends its 139 declarations exactly once, bringing the semantic
manifest to 941 entries. The integrated checks resolve all 941 public names,
104 distinct aggregate consumers including the 23 Stage 7 consumers, and 207
direct-audit labels including 39 Stage 7 labels. The frozen Goal 1 cohort and
checksum remain unchanged.

Stage 8 appends its 49 declarations exactly once, bringing the semantic
manifest to 990 entries. The current manifest resolves 116 distinct aggregate
consumers, including the 12 Stage 8 aggregates, and records 236 direct-audit
labels, including 29 Stage 8 labels. The first 941 entries and the frozen Goal
1 cohort remain unchanged.

Stage 9A appends its 58 declarations exactly once, bringing the semantic
manifest to 1,048 entries. It resolves 127 distinct consumers, including the 11
Stage 9A aggregates, and records 256 direct-audit labels, including 20 Stage 9A
labels. The first 990 entries and the frozen Goal 1 cohort remain unchanged.

Stage 9B appends its 16 wrappers exactly once, bringing the semantic manifest
to 1,064 entries. It resolves 133 distinct consumers, including the six new
aggregates, and records 272 direct-audit labels, including all 16 Stage 9B
wrappers. The first 1,048 entries retain structural SHA-256
`3094cfd9a97646f24dbbb58002eacdddbe5dad746c80c920087059760638b7b5`;
the full 1,064-entry hash is
`ece77e3bd826d5f2db8cc63d14a6733910c5563cb473c5f518111eaccdfcade4`.
The frozen Goal 1 cohort remains unchanged.

Stage 9C appends 36 declarations exactly once: ten decoder declarations, eight
new concrete full-distribution/postprocessing declarations, and 18 semantic
wrappers. The manifest now has 1,100 entries, 140 distinct consumers, and 308
direct-audit labels. The first 1,064 entries retain structural SHA-256
`ece77e3bd826d5f2db8cc63d14a6733910c5563cb473c5f518111eaccdfcade4`;
the full 1,100-entry hash is
`d98dc2ee741dd792c204e088c396c7cbf95b1cc02f98fadceeccf94938da0870`.
The frozen Goal 1 checksum remains
`65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.

The warning-as-error downstream generated-name and consumer files import only
the public root or the named non-root audit and resolve all manifest targets.
Lean-source hole, project-axiom, opaque, unsafe, forbidden quotient-selection,
and heartbeat-override scans are empty through Stage 9C. The public root imports
no diagnostic leaf; artifact and whitespace scans and `git diff --check` pass.

## Using the library in a future project

Start with the public root:

```lean
import QuaternionicComputing

open scoped Matrix Quaternion
open QuaternionicComputing

#check Matrix.realify
#check Quaternion.complexify
#check Quaternion.directRealify
#check State.RealRay
#check State.ComplexRay.mk_eq_mk_iff
#check State.quaternionRay_nonempty_iff
#check State.RealRay.distribution
#check State.ComplexRay.evolveUnitary_comp
#check State.QuaternionRay.evolveCircuit_append
#check State.RealSectorOrbit
#check State.complexRayEquivRealSectorOrbit
#check State.ComplexRay.realificationOrbit_distribution
#check State.complexRay_realColumn0_lift_exists_iff_isEmpty
#check Semantics.QuaternionStatePhaseEq.iff_quaternionRay_mk_eq
#check Semantics.BasisPermutationImplementation
#check Semantics.SameBasisBehavior
#check Semantics.BasisClassicalCircuit
#check Semantics.SameCircuitBasisBehavior.iff_quaternionBasisMeasurementEq
#check Semantics.basisPreparationCircuit_eval_entry
#check Semantics.DensityMatrix
#check Semantics.RealDensityMatrix.ofState
#check Semantics.Effect
#check Semantics.Effect.bornValue_mem_Icc
#check Semantics.DensityMatrix.unitaryConjugate_comp
#check Semantics.DensityMatrix.eq_iff_forall_effect_bornValue_eq
#check Semantics.UnitaryOperator
#check Semantics.channelEq_iff_allMeasurementEq
#check Semantics.realGlobalSignEq_iff_channelEq
#check Semantics.complexProjectiveActionEq_iff_channelEq
#check Semantics.UnitaryCircuit
#check Semantics.circuitChannelEq_iff_allMeasurementEq
#check Semantics.realCircuitGlobalSignEq_iff_channelEq
#check Semantics.realOutputBasisSignEq_iff_pureInputBasisMeasurementEq
#check Semantics.complexOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq
#check Semantics.quaternionOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq
#check State.FiniteDistribution.eq_iff_eventWeight_eq
#check State.FiniteDistribution.eq_iff_allPushforward_eq_sameUniverse
#check Semantics.ExactStateEncoding
#check Semantics.LosslessStateEncoding
#check Semantics.StateIntertwining
#check Semantics.DecodedDistributionAgreement
#check Semantics.AllTopDecodedBasisWeightAgreement
#check Semantics.realColumn0LinearEquiv
#check Semantics.complexColumn0StateEquiv
#check Semantics.QuaternionCentralSignEq
#check Semantics.quaternionProjectiveActionEq_iff_centralSignEq_of_unitary
#check Simulation.quaternionToComplex_exactSimulation
#check Simulation.quaternionToReal_exactSimulation
```

For faster downstream rebuilds, import the narrow leaf that owns the required
declarations; the selected list in the repository README and the module tree in
`Architecture.md` give the stable boundaries.

When extending the library:

- keep quaternionic columns as right modules and put state/ray phase on the right;
- distinguish quaternionic input-right phase, output-left phase, central sign,
  and raw/normalized projective action; never use arbitrary unit-quaternion
  phase as matrix-wide global phase;
- require an explicit `BasisPermutationImplementation` before calling two
  operators or circuits classically basis-equivalent; never substitute the raw
  transition biconditional or generic measurement equality;
- represent finite real/complex mixed states with `DensityMatrix` and
  measurements with genuine Loewner `Effect` values; do not reinterpret an
  arbitrary trace test as a physical effect;
- use `UnitaryOperator`, `ChannelEq`, and `AllMeasurementEq` for complete
  same-space real/complex-style physical behavior; retain `Nonempty I` on
  matrix phase converses and do not infer quaternionic or cross-model channel
  semantics from them;
- preserve the chronological convention `[g₁,…,gₛ] ↦ Gₛ⋯G₁`;
- use generic `unitary (Matrix … ℍ)` rather than the commutative-only
  `Matrix.unitaryGroup` for quaternionic matrices;
- never use the commutative Kronecker interchange law over quaternions;
- distinguish matrix embedding, state evolution, ray equality, and output
  distribution equality in theorem statements;
- use the directional cross-model certificate matching the actual conclusion,
  keep encoders/decoders and top-sector policy explicit, and do not reinterpret
  a representative `LinearEquiv`/`Equiv` as ray, channel, or product-state
  equivalence;
- treat Equation 63 as a matrix reindexing unless a new direct placement/wire
  bridge is separately proved; and
- supply an `ExactGateCompiler` certificate before claiming primitive count or
  depth bounds.

New main public results should be imported by `QuaternionicComputing.lean`,
added to `AxiomAudit.lean`, mapped in `Traceability.md`, and checked under the
workflow in the repository-root `BUILD-PLAN.md`.
