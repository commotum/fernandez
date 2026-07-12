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
public root.

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
  or channel conclusion is exported.
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
- No operator-phase result is promoted to channel or all-effect equality.

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
  with matrix evolution.
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
  Semantics/    exact, measurement, certified basis, state-, and operator-phase relations
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

Important partial boundaries include mixed top states, generic density/partial
trace infrastructure, physical swap synthesis and routing cost, uniform
circuit generators, finite scalar encodings, approximation/error accumulation,
generic unitary synthesis, randomized postprocessing, preprocessing runtime,
and BQP containment. Normalized ray computational-basis observables,
deterministic pushforwards, unitary evolution, and locally-unitary circuit
evolution descend with exact identity and composition laws. The complex-to-real
embedding-orbit boundary is also complete: the rebit and complex-state-ray
source rows are now proved as stated and `closedByGoal2`. This does not settle
arbitrary mixed top states, the paper's phase-kickback interpretation, generic
density/partial trace, or channel/all-effect semantics.

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

Warning-as-error source checks passed for the stable operator-phase, ray, and
certified-basis leaves, their diagnostic leaves, public root, axiom audit, and
all Stage 5 source boundaries. The executable root audit now contains 330
`#print axioms` commands, including 19 Stage 4C and 25 Stage 5 endpoints. All
18 local Stage 5 diagnostic prints, the retained 12 local Stage 4C prints, and
every root endpoint use exactly the union `propext`,
`Classical.choice`, and `Quot.sound`. See `AxiomAudit.md` for the interpretation.

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
25 Stage 5 labels. The frozen 936-declaration Goal 1 cohort retains checksum
`65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.

The warning-as-error downstream generated-name and consumer files import only
the public root or the named non-root audit and resolve all manifest targets.
Lean-source hole, project-axiom, opaque, unsafe, forbidden quotient-selection,
and heartbeat-override scans are empty for Stage 5. The public root imports no
diagnostic leaf; artifact and whitespace scans and `git diff --check` pass.

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
- preserve the chronological convention `[g₁,…,gₛ] ↦ Gₛ⋯G₁`;
- use generic `unitary (Matrix … ℍ)` rather than the commutative-only
  `Matrix.unitaryGroup` for quaternionic matrices;
- never use the commutative Kronecker interchange law over quaternions;
- distinguish matrix embedding, state evolution, ray equality, and output
  distribution equality in theorem statements;
- treat Equation 63 as a matrix reindexing unless a new direct placement/wire
  bridge is separately proved; and
- supply an `ExactGateCompiler` certificate before claiming primitive count or
  depth bounds.

New main public results should be imported by `QuaternionicComputing.lean`,
added to `AxiomAudit.lean`, mapped in `Traceability.md`, and checked under the
workflow in the repository-root `BUILD-PLAN.md`.
