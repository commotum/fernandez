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
import Mathlib.LinearAlgebra.Matrix.Permutation
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

For the real/complex operator-phase layer, the checked arithmetic route uses
`Complex.normSq_mul`, `Complex.mul_conj`, scalar matrix multiplication,
`Matrix.smul_mul`, `Matrix.mul_smul`, and `Matrix.smul_mulVec`. Row and column
phases factor through finite sums with `Finset.mul_sum` and `Finset.sum_mul`.
Chronological composition uses `Circuit.OrderedCircuit.eval_append`, while
global phase preserves square-matrix unitarity through `Unitary.mem_iff`.
These commutative-scalar proofs are not reused to commute quaternionic phases.

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
Matrix.reindexLinearEquiv_mul
Matrix.conjTranspose_reindex
Matrix.transpose_reindex
Matrix.det_reindex_self
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

Direct quaternionic realification uses simultaneous `Matrix.reindex` on four
nested sum sectors.  `Matrix.reindexLinearEquiv_mul` transports compatible
rectangular products, `Matrix.transpose_reindex` transports the adjoint law,
and `Matrix.det_reindex_self` proves that applying the same sector permutation
to rows and columns leaves the determinant unchanged.  These APIs support the
checked `[3,1,0,2]` Equation 63 permutation without a second block calculation.

Known basis preparation uses the permutation-matrix surface:

```lean
Equiv.Perm.permMatrix
Matrix.conjTranspose_permMatrix
Matrix.permMatrix_mul
PEquiv.toMatrix_apply
PEquiv.toMatrix_toPEquiv_mulVec
```

This makes XOR preparation scalar-generic and proves its action on the one-hot
ground column directly, without introducing a circuit synthesis algorithm.
The row/column orientation is explicit: `p.permMatrix R` sends input basis
label `x` to output `p.symm x`. Since `xorBasisEquiv b` is self-inverse, its
certified output permutation is again XOR by `b`.

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

## Goal 2 semantic representations

Stage 6 turns the earlier API probes into three stable public leaves. The
density core uses:

```lean
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
```

The effect and separation leaves add:

```lean
import Mathlib.Analysis.InnerProductSpace.Positive

open scoped ComplexOrder MatrixOrder Matrix
```

`DensityMatrix 𝕜 I` is generic over `RCLike 𝕜`, with explicit
`RealDensityMatrix` and `ComplexDensityMatrix` aliases. It stores the two
invariants

```lean
rho.PosSemidef
rho.trace = 1
```

and derives Hermiticity through `Matrix.PosSemidef.isHermitian`, rather than
storing it redundantly. Ket--bra positivity uses
`Matrix.posSemidef_vecMulVec_self_star`; the trace calculation reduces to
`star psi ⬝ᵥ psi`. Unitary evolution uses
`Matrix.PosSemidef.mul_mul_conjTranspose_same` for positivity and the generic
unitary facts plus trace cycling for normalization:

```lean
Matrix.PosSemidef.mul_mul_conjTranspose_same
Matrix.trace_mul_cycle
Unitary.star_mul_self_of_mem
Matrix.conjTranspose_mul
```

This proves `unitaryConjugate U hU rho` has matrix
`U * rho * Uᴴ`, preserves the density invariants, and composes in the exact
chronological order `V * U`. The pure-state compatibility theorem additionally
uses `Matrix.mul_vecMulVec`, `Matrix.vecMulVec_mul`, and
`Matrix.vecMul_conjTranspose`.

`Effect 𝕜 I` stores the genuine Loewner interval `0 ≤ E` and `E ≤ 1`.
`Matrix.nonneg_iff_posSemidef` and `Matrix.le_iff` expose the positivity of the
effect and its complement. Normalized rank-one projectors are constructed via

```lean
Matrix.toEuclideanLin
InnerProductSpace.rankOne
InnerProductSpace.isSymmetricProjection_rankOne_self
LinearMap.IsSymmetricProjection.isPositive
Matrix.isPositive_toEuclideanLin_iff
InnerProductSpace.symm_toEuclideanLin_rankOne
```

`LinearMap.IsSymmetricProjection.sub_of_range_le_range` proves that a normalized
rank-one projector is at most the identity, so it bundles as an actual
`Effect`. Computational-basis effects reuse `EuclideanSpace.basisFun` and are
identified with both `Matrix.single x x 1` and the corresponding basis-density
matrix.

The Born bounds do not rely on a positivity field stored in the result.
`CStarAlgebra.nonneg_iff_eq_star_mul_self` factors one positive-semidefinite
matrix; trace cycling turns the product into a positive conjugation sandwich;
and `Matrix.PosSemidef.trace_nonneg` gives the lower bound. Applying the same
argument to `1 - E` gives the upper bound. `RCLike.nonneg_iff` proves that the
scalar trace pairing has zero imaginary part, so coercing the real
`bornValue` back to 𝕜 recovers that scalar exactly.

Physical-effect separation is compiled, not merely probed. For a normalized
projector, `Effect.trace_rankOneProjector_mul_eq_inner` identifies the trace
pairing with the corresponding quadratic form. `quadratic_eq_of_unit_sphere`
extends equality from the unit sphere to every vector by a zero/nonzero split.
For the symmetric linear maps induced by positive-semidefinite matrices,
`LinearMap.IsSymmetric.inner_map_self_eq_zero` then identifies the maps, and
`Matrix.toEuclideanLin.injective` identifies the matrices. The exported result

```lean
DensityMatrix.eq_iff_forall_effect_bornValue_eq
```

therefore quantifies over actual `Effect` values. The implementation does not
use `Matrix.ext_iff_trace_mul_left/right` as if their arbitrary algebraic tests
were physical effects.

The Euclidean induced operator norm is the scoped L2 operator norm from
`Mathlib.Analysis.CStarAlgebra.Matrix`.  For square matrices the preferred
bundled map is `Matrix.toEuclideanCLM`; useful laws are
`Matrix.l2_opNorm_def`, `Matrix.l2_opNorm_mul`,
`Matrix.l2_opNorm_mulVec`, and `Matrix.l2_opNorm_conjTranspose`.  Rectangular
work can use `Matrix.toLpLin 2 2` followed by
`LinearMap.toContinuousLinearMap`.  `Matrix.toEuclideanLin` remains in some
bridge theorem names but is deprecated as a construction API.

Finite computational and Euclidean bases reuse the existing APIs
`Pi.basisFun`, `EuclideanSpace.basisFun`, `Fintype.equivFin`, and
`Matrix.mulVec_single_one`. The project keeps its computational index as
`Circuit.BitBasis W = W → Bool`; no second basis representation or cardinality
encoding is needed for the semantic core.

Five boundaries are mandatory:

- complex positive-semidefinite matrices require the `ComplexOrder` scope;
- Loewner order and the later matrix operator norm require `MatrixOrder` and
  `Matrix.Norms.L2Operator`, respectively, so no unscoped matrix norm may be
  assumed to be spectral;
- an empty index type has no trace-one density matrix; the Stage 7 matrix
  phase/channel converses therefore state `Nonempty I`, while the generic
  channel/all-measurement equivalence itself remains dimension-uniform;
- the `RCLike` proof core supplies the real and complex aliases only. It does
  not provide quaternionic Loewner positivity, density matrices, effects, or
  channels; and
- the Stage 6 leaves themselves have no channel API. Stage 7 consumes them but
  still adds no partial trace, Kraus map, instrument, or mixed-top simulation.

## Goal 2 unitary channels and phase kernels

`Semantics/Channel.lean` needs no external channel formalism. It bundles the
existing generic `unitary` predicate as `UnitaryOperator`, delegates evolution
to `DensityMatrix.unitaryConjugate`, and defines

```lean
ChannelEq U V := ∀ rho, U.evolve rho = V.evolve rho
AllMeasurementEq U V :=
  ∀ rho E, Effect.bornValue E (U.evolve rho) =
    Effect.bornValue E (V.evolve rho)
```

The reverse implication in `channelEq_iff_allMeasurementEq` is exactly
`DensityMatrix.eq_of_forall_effect_bornValue_eq` applied at every input. Thus
the implementation retains the genuine `Effect` quantifier and imports no
arbitrary trace-extensionality interface. Chronological operator composition
uses the generic unitary subgroup multiplication proof but exposes the
unambiguous API `U.followedBy V`, whose matrix is `V * U`.

The real/complex phase kernel in `Semantics/ChannelPhase.lean` reuses:

```lean
Matrix.mulVec_mulVec
Unitary.mul_star_self_of_mem
State.*TotalWeight_right_mul
State.star_dotProduct_mulVec_of_mem_unitary
Real.sqrt_ne_zero'
Real.sq_sqrt
Pi.single
```

Equality of normalized pure ket--bra matrices first yields real sign or complex
right phase. To pass from normalized projective action to every raw column,
the proof handles the zero column separately and rescales a nonzero column by
the inverse square root of its total weight. For an inhabited finite square
space, `Pi.single` basis columns and pairwise sums force all column phases to
coincide. Applying this to `V * star U` and cancelling with
`Unitary.mul_star_self_of_mem` proves the global kernel. No determinant,
connectedness, spectral theorem, or dimension-at-least-two lemma is hidden in
the result.

The exact public matrix boundary is:

- global real sign/complex phase implies `ChannelEq` in every finite
  dimension;
- `ChannelEq` implies raw and normalized projective action uniformly;
- the converses to one global scalar require `[Nonempty I]`; and
- on an empty index, separate theorems use `Subsingleton.elim` to prove exact
  matrix equality and then global phase, rather than using vacuous density
  quantification.

`Semantics/ChannelCircuit.lean` imports the existing evaluator-backed phase
relations and `Circuit.LocalUnitary`. A `UnitaryCircuit` derives its bundled
operator with `OrderedCircuit.eval_mem_unitary`; closure under append uses
`OrderedCircuit.IsLocallyUnitary.append`. The theorem
`UnitaryCircuit.toOperator_append` combines
`OrderedCircuit.eval_append` with `UnitaryOperator.followedBy`, preserving the
order `eval D * eval C`. The matrix-level `Nonempty` hypothesis is discharged
by the canonical inhabitant `fun _ ↦ false` of `BitBasis W`, including when
`W` is empty.

These APIs are finite same-space real/complex-style semantics only. Mathlib's
ordered-star matrix theory used here does not provide native quaternionic
densities or effects, and no partial trace, Kraus representation, instrument,
cross-model channel relation, or capacity theorem is imported or synthesized.

## Goal 2 hierarchy closure

`Semantics/Hierarchy/OutputPhase.lean` proves the converse from all-pure-input
basis measurement agreement to output-row phase directly over `ℝ`, `ℂ`, and
`ℍ[ℝ]`. The proof relies on small, stable APIs rather than a spectral theorem:

- `Fintype.sum_eq_zero_iff_of_nonneg` shows total weight zero exactly for the
  zero column;
- `Real.sqrt`, inverse cancellation, and the existing scalar total-weight laws
  normalize every nonzero raw input;
- `Pi.single`, `Matrix.mulVec_add`, and division-ring inverse laws build a
  two-coordinate input in the kernel of one output row;
- complex and quaternionic norm-square zero, multiplication, and inverse laws
  recover a unit row phase.

This yields arbitrary rectangular theorems with only `[Fintype I]`; no
`Fintype O`, `DecidableEq`, `Nonempty`, or unitarity premise survives in the
public signatures. The quaternionic conclusion retains the noncommutative
order `V y x = theta y * U y x`.

`Semantics/Hierarchy/State.lean` uses `FiniteDistribution.ext`, singleton
`Finset` events, and `FiniteDistribution.pushforward_id`. Distribution
equality is iff all event weights and iff all deterministic pushforwards to
finite target types in the source universe. The same-universe restriction is
the precise Lean scope that permits the identity target in one quantified
statement; the existing forward theorem accepts arbitrary target universes.
Empty outcome types are handled by constructive `IsEmpty` results for
`FiniteDistribution Empty` and normalized states, not by impossible test
arguments.

`Semantics/Hierarchy/Operator.lean` contains only compositions of the checked
phase, channel, circuit, and output-row APIs. It introduces no new analytic or
quantum-channel dependency.

## Goal 2 directional simulation certificates

`Semantics/Simulation.lean` is intentionally built from small core interfaces
rather than an external simulation framework. The exact state-encoding layer
uses `Function.LeftInverse`, derives injectivity through
`Function.LeftInverse.injective`, and composes encoders and decoders with
`Function.comp`. This is image reconstruction only: it does not use
`Function.RightInverse` or `Equiv` generically. The operator and intertwining
relations are transparent matrix equalities, and decoded finite-distribution
agreement uses the existing `FiniteDistribution.ext`, event, and pushforward
APIs.

The generic `AllTop...` predicates are ordinary universal quantifiers over
explicit `Top` and `Input` types. Lean therefore cannot silently manufacture a
normalization, purity, tensor-product, marginal, channel, or all-effect
interpretation. Concrete audit consumers instantiate `Top` with the normalized
`Rebit` and `Qubit` coefficient types only to verify that the generic API has
the intended usable scope.

`Semantics/SimulationEncoding.lean` separately uses
`Function.RightInverse`, `LinearEquiv`, and `Equiv` where the mathematics is
stronger. Direct sum-case calculations prove each displayed decoder is also a
right inverse to its canonical column. Together with the existing left
inverse, addition, and real-scalar laws, this yields
`realColumn0LinearEquiv`, `realColumn1LinearEquiv`,
`complexColumn0LinearEquiv`, and `complexColumn1LinearEquiv`. Total-weight
preservation then restricts these to the four `*StateEquiv` values on normalized
representatives. The stable allocation is `38 + 20 = 58` declarations.

These `LinearEquiv` and `Equiv` values are coordinate-carrier bijections. They
do not use quotient lifting and do not imply an ordinary target-ray map:
complex phase still requires `RealSectorOrbit`, while either canonical column
fails to respect `RealRay` on every nonempty source index. Nor does a normalized
`Rebit`/`Qubit` coefficient parameter create a product-state theorem;
`NonProductWitness.encodedState_not_pureTopBottomProduct` supplies the explicit
boundary. No partial-trace, mixed joint-density, circuit, channel, or
all-measurement API is imported by these two leaves.

## Goal 2 state phase, normalized ray quotients, and descent

The real sign characterization uses mathlib's `sq_eq_one_iff`; after rewriting
`pow_two`, it gives `s * s = 1 ↔ s = 1 ∨ s = -1` with no positivity or
nonzero side condition. Pointwise negation is the ordinary function `Neg`
instance, so function extensionality closes the corresponding column theorem.

For exact quaternion diagnostics, `QuaternionAlgebra.ext` separates the four
real components. Applying `congrArg` to `re`, `imI`, `imJ`, and `imK` is a
robust way to cancel a nonzero real coordinate without assuming quaternionic
commutativity. This is the route used by the normalized left-phase rejection
witness.

Stage 4A now installs the three representative relations as the explicit
`realRaySetoid`, `complexRaySetoid`, and `quaternionRaySetoid`. The public
`RealRay`, `ComplexRay`, and `QuaternionRay` types are ordinary Lean
`Quotient`s, not mathlib `Projectivization`: they quotient normalized states by
unit phase only, rather than quotienting arbitrary nonzero vectors by every
nonzero scalar.

The core quotient API is sufficient and keeps the implementation transparent:

```lean
Quotient.eq
Quotient.exists_rep
Quotient.inductionOn
Quotient.lift
```

Each ray namespace wraps these as `mk`, `mk_eq_mk_iff`, `exists_rep`,
`inductionOn`, `lift`, `lift_mk`, and `function_ext`. The real quotient also
uses `Real.signEquivalent_iff_eq_or_eq_neg` to expose the exact paper-facing
`±1` characterization. No wrapper exposes `Quotient.out` as a canonical
representative.

The finite-index boundary is proved in both directions. A normalized state on
an empty type would make its empty total-weight sum equal to one, which is
impossible; conversely `Pi.single i 1` supplies a normalized representative
when an index `i` exists. This yields the public `realRay_nonempty_iff`,
`complexRay_nonempty_iff`, and `quaternionRay_nonempty_iff` theorems plus
`Nonempty`/`IsEmpty` instances. `Classical.choice` is used only to select an
index from a supplied `Nonempty I` instance, not to choose a distinguished ray
representative.

Stage 4B uses those representative-level respectfulness theorems to define the
public quotient operations. `State/RayObservables.lean` lifts
`FiniteDistribution.ofNormalizedState` through each quotient, proving
well-definedness with `FiniteDistribution.ext` and the scalar-specific
basis-weight invariance theorem. The descended `basisWeight`, `eventWeight`,
and `pushforward` are projections or compositions of that distribution, so
their representative computation theorems reduce definitionally.

Deterministic pushforward functoriality is isolated in
`State/DistributionLaws.lean`. The identity proof reduces a filtered universe
to a singleton. The composition proof uses `Finset.sum_fiberwise` to rearrange
the finite fiber sums, preserving the explicit order first `f`, then `g`, as
`g ∘ f`. These are exact equalities of `FiniteDistribution`s and use no measure
or probability-kernel API.

`State/RayEvolution.lean` lifts the existing normalized `*State.evolveUnitary`
functions. Well-definedness uses `signEquivalent_real_mulVec`,
`rightPhaseEquivalent_complex_mulVec`, and
`rightPhaseEquivalent_mulVec`. Identity and composition reduce via
`Matrix.one_mulVec` and `Matrix.mulVec_mulVec`; multiplication order is
deliberately `V * U` for first `U`, then `V`. The unitary certificates come from
`Subgroup.one_mem` and `Subgroup.mul_mem` for `unitary (Matrix I I R)`.

Circuit evolution specializes this action to `OrderedCircuit.eval` and
`OrderedCircuit.eval_mem_unitary`. The helper
`OrderedCircuit.IsLocallyUnitary.append` follows directly from
`List.mem_append`; the ray append laws rewrite `OrderedCircuit.eval_append`,
whose evaluator order is `D.eval * C.eval`. `BitBasis Empty` remains inhabited,
so these laws include the zero-wire circuit boundary even though the bare ray
types indexed by `Empty` are empty.

`Semantics/Ray.lean` exposes three iff bridges from the normalized
representative predicates to quotient-constructor equality. No part of this
implementation chooses a representative or claims that an embedding column
respects an ordinary target-ray quotient. Arbitrary matrix evolution,
uncertified circuits, density/effect/channel semantics, and cross-model orbit
maps remain outside this descent API.

## Goal 2 realification sector orbits

Stage 4C uses an explicit coordinate action rather than importing a generic
projectivization or representation-theory hierarchy. For `eta : ℂ`, the
doubled real action is

```text
(x,y) ↦ (eta.re*x + eta.im*y, -eta.im*x + eta.re*y).
```

The proofs reduce by `Sum`-case extensionality, `Complex.mul_re`,
`Complex.mul_im`, `Complex.normSq_apply`, and `ring`. Identity and composition
are literal coordinate identities. Symmetry of the unit orbit uses complex
conjugation together with `Complex.mul_conj`; transitivity uses
`Complex.normSq_mul`. The source-right-order theorem records first `theta`,
then `eta`, as `theta * eta` even though complex multiplication is commutative.

`realSectorAction_realTotalWeight` proves arbitrary-scalar scaling before the
unit specialization. `RealState.sectorRotation` therefore packages a
normalized target without proof-irrelevance or a chosen representative.
Decoding by `complexOfRealColumn0` is a two-sided inverse of first-column
encoding and intertwines the sector action with complex right multiplication.
This gives the exact characterization

```text
RealSectorPhaseEquivalent x y ↔
  Complex.RightPhaseEquivalent
    (complexOfRealColumn0 x) (complexOfRealColumn0 y).
```

`RealSectorOrbit` is then an ordinary `Quotient`, with the same
`Quotient.eq`, `exists_rep`, `inductionOn`, and `lift` pattern as the scalar
ray types. The explicit normalized encoder and decoder prove
`ComplexRay I ≃ RealSectorOrbit I`; no `Quotient.out` or
`Classical.choose` representative is used for the equivalence.

The observable leaf uses `FiniteDistribution.ext` to descend only
`bottomRealWeight`, the sum of the two sector weights. Unit rotation preserves
that sum, while individual doubled-real basis weights generally change. The
ordinary-`RealRay` boundary instead uses
`RealRay.mk_eq_mk_iff_eq_or_eq_neg`, injectivity of each canonical column, and
existence of a nonzero coordinate in a normalized state. It proves phase
survival iff `±1` and the exact empty-index boundary for a
representative-compatible lift. These results add no density, effect, channel,
or arbitrary-matrix ray-action API.

## Goal 2 quaternionic operator phase

The quaternionic operator layer uses ordinary matrix entries plus the existing
opposite-ring right action; it does not assume a nonexistent commutative scalar
interface. The main scalar identities used to keep sides explicit are:

```lean
Quaternion.normSq.map_mul
Quaternion.normSq_inv
Quaternion.normSq_coe
Quaternion.normSq_ne_zero
Quaternion.coe_commutes
Quaternion.coe_mul_eq_smul
Quaternion.star_mul_self
Quaternion.self_mul_star
```

`Quaternion.coe_commutes` is crucial in the raw-to-normalized projective bridge:
normalization uses a positive real scalar embedded centrally in the
quaternions, so that scalar can be cancelled without commuting an arbitrary
quaternionic phase. `Matrix.mulVec_mulVec` and the existing right-phase
`State.rightPhaseEquivalent_mulVec` theorem then provide the side-correct
composition laws.

The dimension-sensitive kernel proof uses
`Fintype.exists_pair_of_one_lt_card`, `Pi.single`, and entrywise
`QuaternionAlgebra.ext`. The explicit `1 < Fintype.card I` supplies two
different coordinates; evaluating basis columns and their sums first makes all
diagonal ray phases equal, then inputs involving `Quaternion.i` and
`Quaternion.j` force that common quaternion to be real. The unitary cancellation
step uses:

```lean
Unitary.star_mul_self_of_mem
Unitary.mul_star_self_of_mem
Matrix.mulVec_mulVec
```

Only the first square matrix is assumed unitary. `[DecidableEq I]` is explicit
because identity matrices, `Pi.single`, and finite entry calculations need
decidable coordinate equality. No mathlib channel, projectivization, or
quaternionic Hilbert-space API is used to hide the kernel argument.

At rank one, `Quaternion.normSq` and the two self/star product identities prove
that the scalar matrix for `q` is unitary and projectively trivial exactly when
`normSq q = 1`. Component extensionality then proves the concrete `j` scalar is
not a central real sign. This is a theorem-level exception, not an artifact of
an omitted `Nonempty` hypothesis.

## Goal 2 certified basis behavior

The certified basis layer uses `Equiv.Perm I` as explicit data rather than
trying to infer a permutation from a matrix. The essential mathlib surface is:

```lean
Equiv.ext
Equiv.Perm.permMatrix
PEquiv.toMatrix_apply
Pi.single
Matrix.mulVec_single_one
Matrix.conjTranspose_permMatrix
Matrix.permMatrix_mul
Unitary.mem_iff
```

`BasisPermutationImplementation.ofPermMatrix` expands
`PEquiv.toMatrix_apply` to prove the exact one-hot entry formula and records
the induced permutation as `p.symm`. `BasisClassicalUnitaryOperator` uses the
two permutation-matrix adjoint products for unitarity. No generic mathlib
“monomial matrix classifier” is assumed, and no arbitrary function is accepted
in place of an equivalence.

Permutation uniqueness is proved internally from the certified nonzero entry:
if two certificates name outputs `p x` and `q x` for the same column, evaluating
one certificate at the other's output forces equality; `Equiv.ext` then gives
`p = q`. This works for an empty index type without introducing an inhabitant.
For circuits, the existing `OrderedCircuit.eval_mem_unitary` turns stored local
unitarity into the unitary field of the evaluated certified operator.

The real/complex/quaternionic equivalences with sided phase and basis
measurement reuse `State.realWeight`, `State.complexWeight`, and
`State.quaternionWeight`. Quaternionic phases are never commuted: equal
certified permutations yield input witness `star a * b` on the right and
output witness `b * star a` on the left. The exact rational vacuity witness is
checked with `Unitary.mem_iff`, finite Boolean extensionality, and `norm_num`;
it imports no numerical approximation API.

## Promoted compiled APIs

The following formerly probed results now compile as public declarations
without placeholders:

- complex/`j`-component multiplication, conjugation, reconstruction, and norm-square
  scalar identities;
- complex unit-right-phase equivalence, normalization/weight invariance, and
  preservation by arbitrary compatible matrix evolution;
- real sign equivalence with exact `±1` characterization, plus normalized
  real/complex/quaternion representative-phase equivalence, basis-distribution
  preservation, raw matrix/circuit naturality, and normalized unitary
  evolution;
- right-linearity of quaternionic `mulVec`;
- preservation of `star x ⬝ᵥ x` and real/complex/quaternionic total weights by
  generic unitary matrix action;
- complex-to-real and quaternion-to-complex block-embedding multiplication and
  adjoint laws for arbitrary compatible finite shapes;
- injective star-monoid and unitary-group maps for both primary doubled
  embeddings;
- orthogonal, special-orthogonal, unitary, and complex-symplectic image facts
  with the determinant boundary stated above;
- the direct four-sector Equation 63 map, all sixteen coordinates, exact
  `[3,1,0,2]` relation to the composed embedding, injective star homomorphism,
  and quaternionic-unitary embedding into `SO(4N)`;
- explicit `SO(4)`/`SU(4)` nonimage witnesses, including rank-one properness of
  the direct quaternion-to-real image;
- noncommutative-safe contextual placement, added-wire reindexing, and unitary
  preservation;
- unitary XOR preparation of any classically known computational-basis input,
  together with explicit all-input permutation certificates for its matrix,
  gate denotation, and singleton evaluator;
- corrected Kronecker interchange under entrywise commutation, its
  commutative/zero–one special cases, and explicit quaternionic success and
  failure checks;
- finite legal schedules, occurrence completeness/count/permutation laws,
  pairwise-commuting schedule independence, and an observable disjoint-gate
  order-dependence witness;
- a normalized product-input witness whose two outputs are distinct right-phase
  rays but have identical computational-basis weights;
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
  preservation for both primary simulations;
- finite `RCLike` density matrices with positive-semidefinite/trace-one
  invariants, real/complex aliases, pure and basis constructors, unitary
  conjugation, genuine Loewner effects, real Born values in `[0,1]`, and exact
  separation of densities by all physical effects;
- bundled finite unitary operators, exact channel/all-physical-measurement
  equivalence, real/complex raw and normalized projective kernels, inhabited
  global sign/phase characterizations, empty-index matrix boundaries, and
  evaluator-backed locally-unitary circuit channel wrappers;
- a normalized realification example whose added top wire does not factor as
  a pure product with the bottom system; and
- the pinned project baseline and axiom smoke audit.

Their stable declarations live in the narrow scalar, matrix, state, circuit,
and simulation leaves documented by `docs/Architecture.md`.  Remaining probes
are temporary only and are not accepted as completion evidence under
`BUILD-PLAN.md`.
