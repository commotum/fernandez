# Mathlib API Decisions

These decisions were checked with compiling probes against Lean 4.31.0 and
mathlib v4.31.0 (commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`).

## Imports

Use narrow imports in substantive modules:

```lean
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker
```

The isolated determinant leaf additionally uses
`Mathlib.LinearAlgebra.Basis.SMul`, `Mathlib.RingTheory.Complex`, and
`Mathlib.RingTheory.Norm.Transitivity`; consumers of the basic embeddings do
not inherit that proof machinery.  Add `Mathlib.Algebra.QuaternionBasis` only where canonical `i,j,k` basis
machinery is useful, `Mathlib.Analysis.InnerProductSpace.PiL2` for complex/real
Euclidean spaces, and determinant imports only in determinant-specific modules.

## Quaternion scalars

`Mathlib.Analysis.Quaternion` supplies `ℍ = Quaternion ℝ`; generic notation
`ℍ[R]` is enabled by `open scoped Quaternion`.  Coordinates are
`q.re`, `q.imI`, `q.imJ`, and `q.imK`, with extensionality from
`Quaternion.ext`.

Useful proved APIs include:

```lean
Quaternion.re_mul
Quaternion.imI_mul
Quaternion.imJ_mul
Quaternion.imK_mul
Quaternion.re_star
Quaternion.imI_star
Quaternion.imJ_star
Quaternion.imK_star
Quaternion.normSq
Quaternion.normSq_def'
Quaternion.normSq_nonneg
Quaternion.normSq_eq_zero
Quaternion.normSq.map_mul
Quaternion.self_mul_star
Quaternion.star_mul_self
```

Mathlib provides `Quaternion.coeComplex : ℂ → ℍ` and
`Quaternion.ofComplex : ℂ →ₐ[ℝ] ℍ`, but no paper-style complex/“weird”
projections and no `Algebra ℂ ℍ` instance—the complex copy is not central.
The library therefore defines bundled real-linear maps
`complexPart, jPart : ℍ →ₗ[ℝ] ℂ`; `jPart` is the neutral public name for the
paper's “weird part.”

## Right quaternionic modules

Column-vector left multiplication is right quaternion-linear.  The exact API
is:

```lean
Matrix.mulVecBilin ℍ ℍᵐᵒᵖ :
  Matrix m n ℍ →ₗ[ℍ] (n → ℍ) →ₗ[ℍᵐᵒᵖ] (m → ℍ)
```

With `open scoped RightActions`, the library notation `v <• q` is pointwise
right multiplication.  Compiling probes established

```lean
M *ᵥ (v <• q) = (M *ᵥ v) <• q.
```

This is now the public theorem `State.quaternion_mulVec_right_smul`, proved
directly from the inner linear map in `Matrix.mulVecBilin`.  Together with
`Quaternion.normSq.map_mul`, it yields the public right-phase basis, total,
normalization, and evolution theorems in `State/Basic.lean`.

`Matrix.mulVecLin` and `Matrix.toLin'` require commutative coefficients and are
not quaternion APIs.

For a finite right-module state, define the quaternion-valued Hermitian form
explicitly as `star x ⬝ᵥ y` and the real state norm square as
`∑ i, Quaternion.normSq (x i)`.  The default norm on a plain function type is
not the desired finite `ℓ²` norm.

The library packages this convention through an explicit-weight
`State.NormalizedState`; it does not install a global norm-square instance or
identify the function-space default norm with the finite squared norm.

## Blocks, reindexing, and wires

The primary block API is:

```lean
Matrix.fromBlocks
Matrix.fromBlocks_inj
Matrix.fromBlocks_multiply
Matrix.fromBlocks_conjTranspose
Matrix.fromBlocks_mulVec
Matrix.fromBlocks_one
```

These multiplication lemmas require no commutativity and therefore support
quaternion matrices.  `Mᴴ` is `Matrix.conjTranspose`; `star M` on a square
matrix is the same operation.  Entrywise conjugation is `M.map star`, which is
distinct and is what the paper's `Co*`/`Wd*` blocks require.

Reindexing uses:

```lean
Matrix.reindex
Matrix.reindexRingEquiv
Matrix.conjTranspose_reindex
Matrix.submatrix_mulVec_equiv
Equiv.sumArrowEquivProdArrow
Equiv.sumCompl
```

`Matrix.reindexRingEquiv` works with noncommutative multiplication.  The
algebraic embeddings stay on `ι ⊕ ι`; the public `addedBasisEquiv` wrapper
reindexes `BitBasis W ⊕ BitBasis W` to `BitBasis (Unit ⊕ W)`, where the new
`Unit` wire's false/true assignments select the two blocks.

For arbitrary supports, `Equiv.sumCompl` plus
`Equiv.sumArrowEquivProdArrow` supplies a full-basis split into local and
complement assignments.  `Matrix.submatrix_mulVec_equiv` proves that the same
reindexing commutes with column action without expanding a brittle double sum.

## Unitary matrices and determinants

The generic definition works over quaternions:

```lean
U ∈ unitary (Matrix ι ι ℍ)
Unitary.mem_iff
Unitary.star_mul_self_of_mem
Unitary.mul_star_self_of_mem
```

Do not use `Matrix.unitaryGroup ι ℍ`; its coefficient ring must be commutative.
For complex and real matrices, mathlib additionally provides
`Matrix.unitaryGroup`, `Matrix.orthogonalGroup`,
`Matrix.specialUnitaryGroup`, and `Matrix.specialOrthogonalGroup`.

`Matrix.det` also requires commutative coefficients.  Quaternionic
determinant-one claims must be proved after complexification, not by applying
ordinary determinant to a quaternion matrix.  Unitarity and determinant one
remain separate proof obligations.

The bundled maps use:

```lean
StarMonoidHom
Unitary.map
Unitary.map_injective
MonoidHom.ofInjective
```

The determinant proof for realification uses the restricted-scalar linear map
rather than a block determinant division argument:

```lean
LinearMap.det_restrictScalars
LinearMap.restrictScalars_toMatrix
LinearMap.det_toLin'
Matrix.det_reindex_self
Algebra.norm_complex_apply
```

This proves `det (realify A) = Complex.normSq (det A)` even for an empty index
type.  For the quaternionic image, `Matrix.J`, `Matrix.isUnit_det_J`, and the
proved block intertwining show that the complex determinant is real; combined
with unitarity it is `1` or `-1`.  Pinned mathlib's symplectic-group module does
not yet prove determinant one, so no `SU` membership is inferred from
unitarity alone.

## Kronecker products and the noncommutative boundary

`Matrix.kronecker` (`A ⊗ₖ B`) is valid over quaternion coefficients, and
`Matrix.kronecker_mem_unitary` proves that the Kronecker product of two generic
unitaries is unitary without assuming coefficient commutativity.

By contrast, `Matrix.mul_kronecker_mul` requires `CommSemiring`; it is
intentionally unavailable over quaternions.  `Matrix.conjTranspose_kronecker'`
is the noncommutative adjoint formula and includes the required factor swap.
These API boundaries match the paper's ordering phenomenon and are preserved
rather than bypassed.

The project supplies the missing corrected boundary in
`Matrix/KroneckerCommute.lean`:

```lean
QuaternionicComputing.Matrix.EntrywiseCommute B C
QuaternionicComputing.Matrix.kronecker_mul_kronecker_of_entrywiseCommute A B C D h
QuaternionicComputing.Matrix.kronecker_mul_kronecker_commutative A B C D
QuaternionicComputing.Matrix.disjoint_kronecker_factors_commute_of_entrywiseCommute U V h
```

Here `EntrywiseCommute B C` means that every entry of the left product's
second factor commutes with every entry of the right product's first factor.
It is a sufficient hypothesis for the rectangular interchange law, not a
proved necessity characterization.  `IsZeroOneMatrix` supplies useful
sufficient special cases.  For the canonical disjoint factors `U ⊗ₖ 1` and
`1 ⊗ₖ V`, the custom commutation theorem takes `EntrywiseCommute V U`,
because the reverse product moves entries of `V` past entries of `U`.  The
quaternionic `oneByOne` declarations prove both that interchange can hold when
the paper's named right-hand factors are not zero–one and that it fails when
the relevant middle entries are `i` and `j`.

## Finite scheduling APIs

Mathlib's list permutation and pairwise-product lemmas support the finite
schedule layer:

```lean
List.Perm.prod_eq'
List.Nodup.pairwise_of_forall_ne
List.perm_of_nodup_nodup_toFinset_eq
```

The project bundles the semantic data as `Circuit.LegalSchedule`: its list is
noduplicate, complete for a finite identifier type, and certified to respect a
supplied precedence relation through `List.idxOf`.  No mathlib graph or
topological-sort object is silently inferred.  `order_perm` shows that legal
schedules enumerate the same occurrences, while
`scheduledEval_eq_of_pairwise_commute` uses `List.Perm.prod_eq'` to prove
evaluation equality under pairwise commutation of distinct global gate
denotations.  The proof explicitly transports the reversed factor list used by
the chronological evaluator.

## Finite resource and distribution APIs

The support-depth and conditional-compilation leaves reuse ordinary list
structure rather than introducing a second evaluator.  The relevant mathlib
surface includes:

```lean
List.length_flatten
List.sum_le_sum
List.mem_flatMap
List.length_append
Finset.sum_nonneg
Nat.le_log_of_pow_le
```

`Circuit.SupportLayering` stores chronological layers with
`layers.flatten = c`, nonempty layers, and within-layer `List.Pairwise`
support disjointness.  `sum_layerLengths`, `depth_le_gateCount`, and
`depth_eq_gateCount_of_commonWire` are purely finite resource theorems; none
invokes the evaluator or derives commutation from `Disjoint`.

`PlacedGate.denseEntrySlots_eq_four_pow` combines the already proved
`localBasisCard_eq_two_pow` with `Nat.mul_pow`.  The exact `4` and `16` total
translation factors are list-sum identities.  `Nat.le_log_of_pow_le` gives the
finite base-four logarithmic arity bound from a supplied slot bound; no
asymptotic or bit-encoding layer is inferred.

`ExactGateCompiler.compileCircuit` uses `List.flatMap`.  Its semantic theorem
reduces to `OrderedCircuit.eval_append` plus the compiler's supplied
per-gate evaluator equality.  `gateCount_compileCircuit` is an exact list sum,
and `gateCount_compileCircuit_le` calls the generic conditional additive-work
bound with an explicit `K` hypothesis.  There is intentionally no typeclass
instance producing an `ExactGateCompiler`.

Unconstrained schedule counting uses:

```lean
Finset.univ.toList
List.permutations
List.nodup_permutations
List.length_permutations
```

Thus `allChronologicalOrders ι` is duplicate-free and has exact length
`(Fintype.card ι)!`.  Only the empty precedence relation turns every
enumerated order into a `LegalSchedule`; general legal schedules merely map
into this enumeration.

The scalar-independent finite-distribution pushforward is the fiber sum

```lean
fun y ↦ ∑ x with f x = y, μ.weight x
```

and its normalization is exactly `Finset.sum_fiberwise`.  This keeps
`State/Distribution.lean` on finite sums and `State.Basic`, without importing
measure theory.  Pointwise distribution equality then gives finite-event and
deterministic-pushforward equality in `Simulation/Postprocessing.lean`.

## Promoted compiled APIs

The following formerly probed results now compile as public declarations
without placeholders:

- complex/`j`-component multiplication, conjugation, reconstruction, and norm-square
  scalar identities;
- right-linearity of quaternionic `mulVec`;
- preservation of `star x ⬝ᵥ x` and real/complex/quaternionic total weights by
  generic unitary matrix action;
- complex-to-real and quaternion-to-complex block-embedding multiplication and
  adjoint laws for arbitrary compatible finite shapes;
- injective star-monoid and unitary-group maps for both embeddings;
- orthogonal, special-orthogonal, unitary, and complex-symplectic image facts
  with the determinant boundary stated above;
- noncommutative-safe contextual placement, added-wire reindexing, and unitary
  preservation;
- corrected Kronecker interchange under entrywise commutation, its
  commutative/zero–one special cases, and explicit quaternionic success and
  failure checks;
- finite legal schedules, occurrence completeness/count/permutation laws,
  pairwise-commuting schedule independence, and an observable disjoint-gate
  order-dependence witness;
- whole ordered-circuit embedding, normalized state evolution, bottom
  probability preservation, and exact abstract count/width/arity results;
- exact quaternion-to-complex simulation for each supplied legal schedule,
  without schedule selection or schedule-independence assumptions;
- duplicate-free factorial enumeration of empty-precedence chronological
  orders, without a general factorial legal-schedule claim;
- support-layer depth bounds and exact shared-top serialization for the
  literal primary and composed translations;
- exact dense scalar-slot counts `4^d` and translation factors `4`/`16`, kept
  separate from bit complexity and runtime;
- conditional exact primitive compilation, exact summed compiled count, and
  `s*K` count/serial-depth bounds from a supplied compiler and per-gate premise;
- normalized finite distributions plus event and deterministic-pushforward
  preservation for both primary simulations; and
- the pinned project baseline and axiom smoke audit.

Their stable declarations live in the narrow scalar, matrix, state, circuit,
and simulation leaves documented by `docs/Architecture.md`.  Remaining probes
are temporary only and are not accepted as completion evidence under
`BUILD-PLAN.md`.
