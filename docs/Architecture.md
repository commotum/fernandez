# Library Architecture

## Design objective

The library is organized by reusable mathematics rather than the paper's
section order.  Paper-specific statements will be thin packaging over general
scalar, matrix, state, and circuit results.

## Planned module layers

```text
QuaternionicComputing/
  Scalar/
    Quaternion.lean          complex/weird decomposition and scalar identities
  Matrix/
    BlockEmbedding.lean      reusable entrywise 2×2 block lift
    Realification.lean       complex matrices → real matrices
    Complexification.lean    quaternion matrices → complex matrices
  State/
    Basic.lean               finite vectors, norm-square weights, right phases
    Embeddings.lean          state maps and measurement preservation
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

Names may change after API probes, but the dependency direction must remain
scalar → matrix → state → minimal circuits → simulation → broader ordering and
resources.  Generic modules must not import paper-specific wrappers.

## Embedding implementation

The preferred implementation is a scalar ring homomorphism into `2 × 2`
matrices, followed by mathlib's entrywise matrix map and `Matrix.compRingEquiv`
to flatten a matrix of blocks.  A final `Matrix.reindexRingEquiv` puts the added
two-level coordinate first.  This architecture gives multiplication and
identity preservation compositionally rather than by repeating block sums.

The scalar maps still receive direct entry-level theorems and concrete sign
tests.  Star/adjoint compatibility is a separate proof obligation; it is not
assumed merely because the map is a ring homomorphism.

`Matrix.fromBlocks` remains useful for readable source-facing characterizations
of the same maps.  Equivalence between block and flattened forms should be
proved once.

## State implementation

State maps use the two columns suggested by each scalar representation, stated
as explicit functions on finite vectors.  They are not declared complex- or
quaternion-linear without the exact scalar action needed for that claim.

Outcome preservation is first proved coordinatewise:

```text
weight(source i) = weight(target (top=0, i)) + weight(target (top=1, i)).
```

Finite distribution and partial-trace corollaries then follow.  This avoids
building a density-operator hierarchy before the central theorem is stable.

## Circuit implementation

The minimum circuit layer stores:

- a finite source wire count;
- a local arity and injective support map;
- a square local matrix plus its validity proof where required;
- an ordered list of placed gates.

Placement is defined directly on bit-assignment basis indices.  This works over
noncommutative coefficients and isolates the exact central-entry facts needed
for permutation/padding lemmas.  The target translation adds one distinguished
wire shared by all translated gates.

The first main theorem is proved by induction over the ordered list.  DAGs and
topological sorting are an extension layer used to connect the theorem to the
paper's “temporal chain” language and to exhibit order dependence.

## Group and determinant scope

The simulations require multiplicativity, adjoint preservation, injectivity,
and unitarity preservation.  They do not require determinant one.  Therefore:

- unitary/orthogonal image theorems are established first;
- determinant-one assertions are kept as independent paper-coverage
  obligations;
- failure or delay of a special-unitary proof cannot be hidden inside a custom
  definition and cannot block the stronger useful operator simulation.

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

