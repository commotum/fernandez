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
  State/
    Basic.lean               normalized columns, weights, right phases
    Realification.lean       complex → real state columns and outcomes
    Complexification.lean    quaternion → complex state columns and outcomes
  Circuit/
    Basic.lean               local gates, supports, placement, ordered semantics
    Ordering.lean            DAG/topological orders and ambiguity witnesses
  Simulation/
    ComplexToReal.lean       corrected Theorem 2 family
    QuaternionToComplex.lean corrected Theorem 4 family
    QuaternionToReal.lean    corrected Corollary 1 family
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
both embeddings are bundled as injective star-monoid homomorphisms.  At the circuit boundary,
`Matrix.reindexRingEquiv` and `Equiv.boolProdEquivSum` convert `ι ⊕ ι` to
`Bool × ι`, making the added top wire explicit without burdening scalar/matrix
proofs with wire encodings.

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

The minimum circuit layer stores:

- a finite source wire count;
- a local arity and injective support map;
- a square local matrix plus its validity proof where required;
- an ordered list of placed gates.

Circuit bases are `Fin n → Bool`.  A support equivalence splits full bit
assignments into local and complementary assignments, a local gate is padded as
`U ⊗ₖ 1`, and `Matrix.reindex` returns it to the full basis.  This construction
works over quaternion coefficients; its unitarity follows from
`Matrix.kronecker_mem_unitary` and unitary preservation under reindexing.  The
target translation adds one distinguished wire shared by all translated gates.

The development must never use `Matrix.mul_kronecker_mul` for quaternionic
semantics: mathlib correctly requires commutative coefficients for that
interchange law.  Ordered evaluation remains an explicit list/fold, which is
precisely where quaternionic order dependence is observable.

The first main theorem is proved by induction over the ordered list.  DAGs and
topological sorting are an extension layer used to connect the theorem to the
paper's “temporal chain” language and to exhibit order dependence.

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
