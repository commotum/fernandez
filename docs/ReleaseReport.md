# Quaternionic Computing Lean Library — Release Report

- Release date: 2026-07-10
- Project version: 0.1.0
- Lean: 4.31.0
- Mathlib: v4.31.0 (`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`)

## Outcome

This repository reconstructs the important finite-dimensional mathematics of
Fernandez and Schneeberger's *Quaternionic Computing*
(`quant-ph/0307017v2`) as a reusable Lean library. The current tree contains
53 Lean source files, including the public root, executable axiom audit, and
non-root semantic diagnostic leaves.

The paper was treated as a mathematical source rather than a specification.
Every important inventory item has one terminal disposition: among 101 rows,
21 are proved as stated, 33 corrected and proved, 28 partially formalized, 16
intentionally excluded, and 3 unresolved.  The correction log contains 26
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
- Fixed-input, all-basis-input, and all-normalized-pure-input basis agreement
  are separate predicates, with finite distributions, events, and
  deterministic pushforwards downstream.
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
| State/ray phase | `Real.SignEquivalent`, `Complex.RightPhaseEquivalent`, `Quaternion.RightPhaseEquivalent`, the three normalized `*StatePhaseEq` relations, their equivalence/distribution theorems, and their raw-matrix/circuit and normalized-unitary preservation laws |
| Operator/circuit phase | `RealGlobalSignEq`, `ComplexGlobalPhaseEq`, the real/complex input-, output-, and projective-action relations, their `*Circuit*Eq` wrappers, measurement arrows, and sided composition laws |
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
  State/        normalized columns, phase, encodings, finite distributions
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
6. Quaternionic state/ray phase must act on the right.
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
and BQP containment.

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
three operator-phase targets including the diagnostic leaf (2,355 jobs), the
public root (2,559 jobs), the explicit axiom audit (2,559 jobs), and the full
cached project build (2,559 jobs). Together these commands cover all 53 current
Lean sources. Existing dependency checkouts remained pinned by the manifest;
network bootstrap from a brand-new clone was not rerun in this restricted
environment.

Warning-as-error source checks passed for both stable operator-phase leaves,
the diagnostic leaf, public root, and audit. The executable audit now contains
251 `#print axioms` commands; every audited endpoint uses only
`propext`, `Classical.choice`, and `Quot.sound`.  See `AxiomAudit.md` for the
interpretation.

The independent Goal 2 semantic manifest contains exactly 283 declarations:
61 from Stage 2, 72 from Stage 3A, and 150 from Stage 3B. All seven semantic
axes are present, all names resolve through the public root, 35 real diagnostic
consumers resolve, and 65 manifest entries are direct root-audit targets. The
frozen 936-declaration Goal 1 cohort checksum remains unchanged.

The warning-as-error downstream file `/tmp/ReleaseImportSmoke.lean` imported
only `QuaternionicComputing`, checked representative scalar, matrix, state,
circuit, simulation, resource, outcome, phase, correction-witness, and example
APIs, and proved `card (DirectRealIndex Bool) = 8`.  Lean-source hole,
project-axiom, opaque, unsafe, and forbidden noncommutative-shortcut scans were
empty.  `git diff --check` passed, and no Lake/Lean build artifact is tracked.

## Using the library in a future project

Start with the public root:

```lean
import QuaternionicComputing

open scoped Matrix Quaternion
open QuaternionicComputing

#check Matrix.realify
#check Quaternion.complexify
#check Quaternion.directRealify
#check Simulation.quaternionToComplex_exactSimulation
#check Simulation.quaternionToReal_exactSimulation
```

For faster downstream rebuilds, import the narrow leaf that owns the required
declarations; the selected list in the repository README and the module tree in
`Architecture.md` give the stable boundaries.

When extending the library:

- keep quaternionic columns as right modules and put state/ray phase on the right;
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
