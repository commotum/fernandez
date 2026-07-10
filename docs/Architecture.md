# Library Architecture

## Design objective

The library is organized by reusable mathematics rather than the paper's
section order.  Paper-specific statements will be thin packaging over general
scalar, matrix, state, and circuit results.

## Module layers

```text
QuaternionicComputing/
  Scalar/
    Quaternion.lean          complex/`j`-component decomposition and identities
    Phase.lean               phase-side correction and counterexample
  Matrix/
    Realification.lean       complex matrices → real matrices
    Complexification.lean    quaternion matrices → complex matrices
    Unitary.lean             star homomorphisms and unitary/symplectic images
    Determinant.lean         isolated determinant and SO/sign results
    KroneckerCommute.lean    corrected noncommutative interchange boundary
  State/
    Basic.lean               normalized columns, weights, right phases
    Realification.lean       complex → real state columns and outcomes
    Complexification.lean    quaternion → complex state columns and outcomes
    Unitary.lean             normalized state evolution under unitary matrices
  Circuit/
    Placement.lean           noncommutative-safe contextual gate placement
    AddedWire.lean           shared distinguished-wire equivalences/reindexing
    Basic.lean               locality-certified gates and ordered semantics
    OrderSanity.lean         concrete noncommuting evaluator audit
    Cost.lean                generic width/arity bounds and maxima
    Realification.lean       one-gate complex-to-real translation
    Complexification.lean    one-gate quaternion-to-complex translation
    Ordering.lean            finite legal schedules and independence criterion
    OrderingWitness.lean     disjoint unitary order-dependence witness
  Simulation/
    Basic.lean               generic sum-index → added-wire state transport
    ComplexToReal.lean       corrected Theorem 2 family
    QuaternionToComplex.lean corrected Theorem 4 family
    QuaternionToReal.lean    corrected Corollary 1 family
    Scheduled.lean           fixed legal-schedule simulation bridge
    OrderingWitness.lean     translated observable ordering witness
    Examples.lean            exact non-real and quaternionic end-to-end checks
  Paper/
    Results.lean             source-numbered wrappers where useful
  Examples.lean
  AxiomAudit.lean
QuaternionicComputing.lean   stable public root import
```

Later names may change as their APIs are implemented, but the dependency direction must remain
scalar → matrix → state → minimal circuits → simulation → broader ordering and
resources.  Generic modules must not import paper-specific wrappers.

## Embedding implementation

The canonical embedding definitions use `Matrix.fromBlocks` on sum indices.
This matches the paper's displayed matrices exactly, keeps the added sectors
visible, and lets multiplication and adjoint proofs use
`Matrix.fromBlocks_multiply` and `Matrix.fromBlocks_conjTranspose`, both valid
over noncommutative coefficient rings where applicable.

For square matrices, complexification is bundled as a ring homomorphism and
both embeddings are bundled as injective star-monoid homomorphisms.  At the
circuit boundary, `addedBasisEquiv` identifies `BitBasis W ⊕ BitBasis W` with
`BitBasis (Unit ⊕ W)`: the two sum sectors are exactly the false and true
assignments of one distinguished top wire.  This keeps wire bookkeeping out of
the scalar/matrix proofs while making the shared added wire explicit.

Scalar component maps still receive direct entry-level theorems and concrete
sign tests.  Star/adjoint compatibility is a separate proof obligation; it is
not assumed merely from multiplicativity.

## State implementation

State maps use the two columns suggested by each scalar representation, stated
as explicit functions on finite vectors.  The low-level `realifyVec` map and
its matrix-action theorem live beside `realify` because they directly guard
the embedding's sign convention; `State/Realification.lean` reuses that map
and supplies the second column, real-linear bundles, normalized wrappers, and
measurement API.  `State/Complexification.lean` supplies the analogous two
real-linear quaternion-to-complex columns.  None is declared complex- or
quaternion-linear without the exact scalar action needed for that claim.

`State/Basic.lean` parameterizes `NormalizedState` by an explicit real-valued
scalar weight instead of introducing a global norm-square typeclass.  Its real,
complex, and quaternion specializations expose nonnegative basis weights and
normalization equations.  Quaternionic right phase is proved to preserve each
weight and commute with arbitrary matrix action.

Outcome preservation is proved coordinatewise:

```text
weight(source i) = weight(target (top=0, i)) + weight(target (top=1, i)).
```

Total-weight and normalized-state corollaries then follow.  For the real case,
`reducedRealOuter` also proves the paper's rank-one reduced-matrix equality
directly.  A general density-operator hierarchy remains optional and is not a
dependency of the central theorem.

## Circuit implementation

The minimum circuit layer uses any finite wire type `W`, with computational
basis `BitBasis W := W → Bool`.  A `PlacedGate R W` stores finite local and
complement wire types, an explicit split `Local ⊕ Complement ≃ W`, and only a
local square matrix.  Its global matrix is derived by padding as `U ⊗ₖ 1` and
reindexing; no unconstrained global operator can disagree with the locality
certificate.  `onSupport` constructs the split from an arbitrary injective,
possibly noncontiguous support.

Placement multiplication does not use the commutative Kronecker interchange
law.  Tensoring on the right by identity is identified with a block-diagonal
matrix, whose multiplication theorem is valid over noncommutative semirings.
This proves placement multiplication, adjoint preservation, and unitarity for
quaternion coefficients.

An `OrderedCircuit` is a chronological list.  Its evaluator reverses the list
before multiplying, so `[g₁, …, gₛ]` denotes `Gₛ * ⋯ * G₁`.  A generic
noncommutation theorem and a concrete quaternionic `i`/`j` witness guard this
order.  Gate count is list length; semantic reindexing does not add gates.

`AddedWire W := Unit ⊕ W` is shared by every translated gate.  `addTopSplit`
puts this one distinguished wire into the translated local support while
leaving the complement unchanged.  The separate realification and
complexification leaves prove, entrywise from the actual placement definition,
that translating a placed gate commutes with contextual placement.  Their
translated gate has local arity exactly one larger and the same complement.

The development must never use `Matrix.mul_kronecker_mul` for quaternionic
semantics: mathlib correctly requires commutative coefficients for that
interchange law.  `Matrix/KroneckerCommute.lean` proves the corrected
rectangular interchange theorem under the sufficient condition that every
entry of the two middle factors commutes.  It also proves the commutative and
zero–one special cases, exhibits a non-zero–one quaternionic success, and
exhibits failure for middle entries `i` and `j`.  It does not claim that
entrywise commutation is necessary.

The main simulation leaves use the exported monoid-hom evaluation lemma to
lift these one-gate identities over an ordered list.

## Scheduling and order dependence

`Circuit/Ordering.lean` separates a finite family of gate occurrences from its
chronological execution order.  A `LegalSchedule ι precedes` contains a list
of every identifier exactly once and a certificate that each supplied
precedence edge points forward in the list.  The relation is deliberately not
required to be a transitive partial order or an acyclic graph: existence of a
legal schedule is the finite consistency certificate needed by the evaluator.
Instantiating a schedule with a gate family produces an `OrderedCircuit`, so
Definition 4's corrected finite semantics is a thin layer over the established
chronological product.

Any two legal schedules enumerate permutation-equivalent gate occurrences,
but their products need not agree.  `scheduledEval_eq_of_pairwise_commute`
proves equality when all distinct global gate denotations commute.  The
separate witness leaf places rational unitary `i`- and `j`-mixers on disjoint
Boolean wires and proves that the two legal schedules have unequal operators
and unequal normalized `00` outcome weights.  This witness establishes
existence only; disjoint support is not by itself either a universal
order-dependence theorem or an order-independence theorem over quaternions.

The paper's cut-poset language is not identified with this occurrence-order
API.  No type of temporal cuts, theorem that one topological sort totally
orders all cuts, topological-sorting algorithm, or uniform circuit-family
generator is supplied.  Those graph, runtime, and Definition 5 uniformity
claims remain outside the finite core.

## Simulation implementation

`Simulation/Basic.lean` transports sum-index state columns through the same
`addedBasisEquiv` used by circuit matrices.  Its generic matrix-action theorem
proves that reindexing commutes with `mulVec`; its bottom-weight operation sums
the actual false/true assignments of the distinguished wire.  This keeps both
primary simulation proofs parallel without duplicating index algebra.

`State/Unitary.lean` proves, over a possibly noncommutative star ring, that a
unitary matrix preserves `star ψ ⬝ᵥ ψ`.  Real, complex, and quaternionic total
weights are exact specializations, yielding normalized-state evolution
constructors.  Thus the main observable conclusions compare genuine
normalized probability distributions, not merely unnormalized weights.

`realifyCircuit` and `complexifyCircuit` are literal `List.map`s of the public
placed-gate translations.  Their evaluator theorems use the public
chronological semantics; state evolution applies the resulting matrix to a
separately defined transported column.  Corrected Theorems 2 and 4 expose
operator embedding, state intertwining, bottom probability equality, unchanged
gate count, width `+1`, and exact per-gate arity `+1`.  Empty circuits have
maximum local arity zero; maximum-arity equality therefore carries the
necessary nonempty hypothesis.

`Simulation/Scheduled.lean` applies the fixed-order quaternion-to-complex
results to the exact chronological circuit selected by a supplied
`LegalSchedule`.  It preserves occurrence count, pointwise unitarity and arity
bounds, operator embedding, and bottom probability equality separately for
that schedule.  It neither chooses among legal schedules nor equates them.
`Simulation/OrderingWitness.lean` confirms that complexification preserves the
explicit operator gap and the two exact observable weights.

The corrected Corollary 1 is the visible composition
`realifyCircuit (complexifyCircuit c)`.  It uses two shared distinguished
wires, proves operator embedding `wireRealify (wireComplexify (eval c))`, exact
gate count, width and arity `+2`, nested state intertwining, and the four-sector
bottom probability sum.  It introduces no direct quaternion-to-real map.

## Group and determinant scope

The simulations require multiplicativity, adjoint preservation, injectivity,
and unitarity preservation.  They do not require determinant one.  The current
determinant boundary is therefore explicit:

- `realify_det` proves `detℝ(realify A) = normSq(detℂ A)`, so a complex
  unitary maps to `SO(2N)`;
- a quaternionic unitary maps injectively to a complex unitary preserving the
  canonical symplectic form;
- the available block and unitary laws prove only that its complex determinant
  is real and lies in `{1, -1}`.  The proof selecting `1` needs Pfaffian,
  connectedness, or Study-determinant infrastructure absent from the pinned
  mathlib, so that one refinement is recorded as unresolved;
- this unresolved special-unitary sign cannot be hidden inside a custom
  definition and does not block operator or measurement simulation.

## Verification architecture

- Every substantive module must compile without placeholders.
- `QuaternionicComputing/AxiomAudit.lean` lists `#print axioms` commands for the
  main public theorems.
- Small exact examples guard signs, multiplication order, placement, and
  outcome semantics.
- `docs/Traceability.md` and `docs/Corrections.md` are updated in the same stage
  as corresponding declarations.
- Release verification includes a downstream import module that imports only
  `QuaternionicComputing`.
