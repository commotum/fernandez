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

`Matrix.mulVecLin` and `Matrix.toLin'` require commutative coefficients and are
not quaternion APIs.

For a finite right-module state, define the quaternion-valued Hermitian form
explicitly as `star x ⬝ᵥ y` and the real state norm square as
`∑ i, Quaternion.normSq (x i)`.  The default norm on a plain function type is
not the desired finite `ℓ²` norm.

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
Equiv.boolProdEquivSum
Fin.consEquiv
```

`Matrix.reindexRingEquiv` works with noncommutative multiplication.  The
algebraic embeddings stay on `ι ⊕ ι`; a wrapper reindexes to `Bool × ι`, and
`Fin.consEquiv` identifies `Bool × (Fin n → Bool)` with an `(n+1)`-wire basis.

For arbitrary supports, `Equiv.sumCompl` plus
`Equiv.sumArrowEquivProdArrow` supplies a full-basis split into local and
complement assignments.

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
These API boundaries match the paper's ordering phenomenon and will be
preserved rather than bypassed.

## Promoted compiled APIs

The following formerly probed results now compile as public declarations
without placeholders:

- complex/`j`-component multiplication, conjugation, reconstruction, and norm-square
  scalar identities;
- right-linearity of quaternionic `mulVec`;
- preservation of `star x ⬝ᵥ y` by a quaternionic unitary matrix;
- complex-to-real and quaternion-to-complex block-embedding multiplication and
  adjoint laws for arbitrary compatible finite shapes;
- injective star-monoid and unitary-group maps for both embeddings;
- orthogonal, special-orthogonal, unitary, and complex-symplectic image facts
  with the determinant boundary stated above;
- unitary preservation under reindexing; and
- the pinned project baseline and axiom smoke audit.

Their stable declarations live in `Scalar/Quaternion.lean` and the four
`Matrix/*.lean` leaves.  Remaining probes are temporary only and are not
accepted as completion evidence under `BUILD-PLAN.md`.
