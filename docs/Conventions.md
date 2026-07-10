# Mathematical Conventions

This document fixes conventions for the Lean library.  It is authoritative when
the paper's prose or notation is ambiguous.

## Scalars and finite spaces

- Complex amplitudes use mathlib's `ℂ`.
- Quaternionic amplitudes use mathlib's `ℍ[ℝ]` (`Quaternion ℝ`).
- A finite column vector over `R` with basis index `ι` is represented by
  `ι → R`.  A matrix `A : Matrix ι κ R` acts from the left with
  `Matrix.mulVec`.
- Matrices compose in the usual functional order:
  `(A * B) *ᵥ ψ = A *ᵥ (B *ᵥ ψ)`.  If gates `g₁, …, gₛ` occur in chronological
  order, their semantic matrix is `gₛ * ⋯ * g₁`.
- General algebraic theorems use arbitrary finite index types.  A circuit on a
  finite wire type `W` has computational basis `BitBasis W := W → Bool`, not
  numerals whose binary encoding must be unfolded in every proof.

## Quaternionic scalar side

Quaternionic column vectors are treated as **right modules**.  Lean represents
this as a left module over the opposite ring `ℍᵐᵒᵖ`; with
`open scoped RightActions`, `ψ <• q` is the pointwise vector
`i ↦ ψ i * q`.  A quaternionic matrix acts from the left and therefore respects
right scaling by associativity.  This is exposed by
`Matrix.mulVecBilin ℍ ℍᵐᵒᵖ`:

```text
A *ᵥ (ψ · q) = (A *ᵥ ψ) · q.
```

Consequently, equality of quaternionic state/ray representatives up to phase is
represented using a unit quaternion on the **right**, `ψ = ψ' <• q`. The paper places the phase on
the left in Equation (45); that relation is not preserved by arbitrary left
matrix evolution and is corrected here.  Lean's ordinary `SMul` notation is not
silently confused with ordinary left scalar action.  The state API proves that
this right phase preserves every basis weight, total weight, normalization,
and arbitrary compatible matrix action.

Complex phase is also written on the right so the two state APIs have the same
shape.  Because `ℂ` is commutative, this is equivalent to the usual left-phase
convention.  `Complex.RightPhaseEquivalent` and
`Quaternion.RightPhaseEquivalent` are explicit relations on representative
columns; `ComplexState` and `QuaternionState` remain normalized-column
subtypes, not quotient types.

Real phase is written on the right as well. `Real.SignEquivalent x y` carries
a scalar witness `s` with `s*s=1` and `x i = y i*s`; the library proves this is
exactly `s=1` or `s=-1`, hence exactly equality or pointwise negation. The
normalized wrappers `RealStatePhaseEq`, `ComplexStatePhaseEq`, and
`QuaternionStatePhaseEq` remain relations on concrete representatives. They
are not quotient equality, operator global phase, or channel equality.

## Operator and circuit phase

State phase and operator phase are distinct. For same-typed real and complex
matrices the operator conventions are:

```text
global:       V = η • U
input column: V y x = U y x * φ x
output row:   V y x = θ y * U y x
projective:   Uψ and Vψ lie on the same state ray for every normalized ψ.
```

For real matrices every phase witness squares to one; for complex matrices it
has `Complex.normSq = 1`. Input phases stay visibly on the right and output
phases on the left even though real and complex multiplication commutes. This
keeps the API compatible with the quaternionic sided conventions proved in a
separate layer.

Circuit phase relations compare `OrderedCircuit.eval`, never gate lists,
schedules, resources, or embeddings. Because `eval (C ++ L) = eval L * eval C`,
input-column phase is preserved by a common later circuit and output-row phase
by a common earlier circuit. A common earlier projective evolution needs a
unitary certificate; arbitrary two-sided congruence is not assumed.

Projective action compares raw output rays and does not claim output
normalization. Its quantifier is vacuous when the finite input type has no
normalized state, so converse and kernel theorems must carry explicit
nonempty/cardinality and unitarity hypotheses. None of these phase relations
is channel equality or all-effect equality.

## Conjugation and adjoints

- Complex and quaternionic conjugation use `star`.
- Matrix adjoint uses `Matrix.conjTranspose`; for real matrices this reduces to
  transpose under the trivial star convention.
- Quaternionic unitarity is expressed using the generic star-monoid predicate
  `unitary (Matrix ι ι ℍ[ℝ])`, which requires both
  `Aᴴ * A = 1` and `A * Aᴴ = 1`.  Mathlib's convenience abbreviation
  `Matrix.unitaryGroup` assumes a commutative coefficient ring and therefore is
  not used for quaternion matrices.
- “Symplectic group” in the paper means the compact quaternionic unitary group.
  Its complexification is proved to preserve mathlib's canonical skew form
  `Matrix.J`, so the image also lies in `Matrix.symplecticGroup`.  This
  form-preservation result is not silently strengthened to determinant one;
  the pinned symplectic API does not yet supply that theorem.

## Scalar decompositions and embeddings

For `q = a₀ + a₁ i + a₂ j + a₃ k`, the paper's decomposition is retained:

```text
q = z + w j,   z = a₀ + a₁ i,   w = a₂ + a₃ i.
```

The complex-to-real scalar representation uses the paper's signs,

```text
z ↦ [[re z, im z], [-im z, re z]],
```

and the quaternion-to-complex representation is

```text
q = z + w j ↦ [[z, w], [-conj w, conj z]].
```

Matrix embeddings use `Matrix.fromBlocks`, so an index `ι` is doubled to
`ι ⊕ ι`.  At the circuit boundary `addedBasisEquiv` reindexes the two copies of
`BitBasis W` to `BitBasis (Unit ⊕ W)`.  The `Unit` summand is one shared,
distinguished leading/top wire; its `false` and `true` assignments select the
two matrix blocks.

Equation 63 uses a separate transparent four-sector order
`[Re, ImI, ImK, ImJ]`.  `DirectRealIndex ι` has cardinality `4 * card ι`, and
`eq63PaperToComposed` maps paper sectors to the nested composition in order
`[3,1,0,2]`.  Thus `directRealify A` is a simultaneous row/column reindexing of
`realify (complexify A)`, with no hidden diagonal sign change.  This is a
matrix-level convention; the canonical circuit corollary continues to use the
two explicit added wires of the compositional translators.

## States, phases, and measurements

The library keeps the following levels distinct:

1. literal vector equality;
2. literal same-type matrix equality (`ExactOperatorEq`);
3. literal equality of chronological circuit evaluations (`ExactCircuitEq`);
4. equality up to a unit scalar on the documented side;
5. equality of embedded operators or embedded state evolution;
6. one-input computational-basis output-weight agreement
   (`OutputWeightEqAt`);
7. all-basis-input agreement (`BasisMeasurementEq`);
8. all-normalized-pure-input basis agreement
   (`PureInputBasisMeasurementEq`); and
9. equality of packaged computational-basis distributions
   (`NormalizedDistributionEq`).

The three input scopes in items 6–8 are not interchangeable. The generic
weight function need not normalize basis kets, so the theorem from
all-normalized-pure-input agreement to all-basis-input agreement requires that
normalization as an explicit hypothesis. Channel and all-physical-effect
equality are stronger notions introduced separately; no basis-only relation
is treated as either one.

For a coordinate `ψ i`, its computational-basis weight is its scalar norm
square.  In a doubled target space, forgetting the top wire means summing the
two target weights above each bottom basis index.  The main simulation theorems
state this equality explicitly.  They do not define “simulation” to be
whatever relation the embedding happens to satisfy.

Normalized states are introduced only at the semantic boundary.  Algebraic
embedding and evolution lemmas should apply to arbitrary vectors whenever the
proof does not need normalization.  Density matrices and partial traces are
secondary formulations; direct outcome-weight theorems are the minimum needed
for the paper's computational claim.

Concretely, `NormalizedState ι α weight` is a finite amplitude column paired
with the equation `totalWeight weight ψ = 1`.  The scalar weight is an explicit
parameter, avoiding any global squared-norm instance.  `RealState`,
`ComplexState`, and `QuaternionState` specialize it, and `Rebit`, `Qubit`, and
`Quaterbit` use `Bool` as the two-level basis.  This makes the missing `= 1` in
the paper's quaterbit definition impossible to omit.

The arbitrary-top-wire results currently cover every normalized pure top
rebit/qubit and prove pointwise bottom-weight equality.  Claims about arbitrary
mixed top states require a density-state API and remain explicitly partial;
they are not silently inferred from the pure-state theorems.

`FiniteDistribution α` means a real weight on a finite type, pointwise
nonnegative and summing to one.  `eventWeight` is a finite sum, and
`pushforward f` sums weights over the fibers of a deterministic map `f`.
Equality of the primary bottom distributions therefore implies equality for
all finite events, marginals encoded as deterministic maps, and deterministic
finite postprocessing.  It does not include randomized machines or their cost.

## Circuits and wire placement

- The central semantic object is an ordered list of well-formed placed gates.
  This directly models a fixed evaluation order and supports induction.
- A placed gate stores a finite local type, a finite complement type, a split
  `Local ⊕ Complement ≃ W`, and a local matrix.  Its global operator is derived
  from these fields, so locality is not detachable metadata.
- A `LegalSchedule ι precedes` is a finite chronological list containing every
  gate-occurrence identifier exactly once, together with a proof that every
  supplied precedence constraint points forward in the list.  The relation is
  not assumed transitive or acyclic; existence of the schedule is itself the
  consistency certificate used by the finite semantics.
- Instantiating a legal schedule with a gate family produces an
  `OrderedCircuit`.  Different legal schedules remain different supplied
  chronological circuits unless an explicit independence theorem applies.
- A local gate is lifted to global basis states by restricting bit assignments
  to its support and requiring equality off that support.  Concretely, a split
  equivalence identifies the full basis with `local × rest`, forms
  `U ⊗ₖ 1`, and reindexes back.
- Quaternionic placement does not rely on the commutative Kronecker interchange
  identity.  Its multiplication law uses identity block diagonalization;
  permutations and contextual padding use only `0`, `1`, and explicit index
  equivalences, with multiplication order visible in definitions.
- For `(A ⊗ₖ B)(C ⊗ₖ D)`, entrywise commutation of `B` with `C` is
  a sufficient hypothesis for the usual interchange equality.  A zero–one
  middle factor is one sufficient special case, not a necessary
  characterization.  No interchange `iff` is asserted.
- Pairwise commutation of distinct placed-gate denotations is sufficient for
  every legal schedule of the same occurrence family to evaluate equally.
  Disjoint supports alone do not supply this hypothesis over quaternion
  coefficients.  The library's `i`/`j` example proves that some disjoint
  locally unitary pairs have order-dependent operators and observable weights;
  it does not say that all such pairs do.
- On the normalized ground product input, the same pair has outputs that are
  not related by unit right phase, yet all computational-basis weights agree.
  This is an explicit reminder that ray inequality, operator inequality, and
  equality for one measurement family are different conclusions.
- Semantic permutation matrices used to describe placement are not counted as
  physical swap gates unless a separate synthesis theorem constructs them.
- A chronological list `[g₁, …, gₛ]` evaluates to `Gₛ * ⋯ * G₁`.  The added
  target wire has type `Unit ⊕ W`, is shared by every translated gate, and is
  never duplicated per gate.
- The paper's temporal-cut poset is not represented as the gate-occurrence
  precedence relation.  In particular, the library does not identify one gate
  topological sort with a total order on every cut.
- `allChronologicalOrders ι` enumerates exactly the permutations of the
  canonical finite identifier list, without duplicates, and has length
  `(Fintype.card ι)!`.  Every such order is legal only for the empty
  precedence relation.  For a general relation this is an upper enumeration,
  not an assertion that all orders are legal or that the number of legal
  schedules is factorial or exponential.

## Simulation and abstract resources

- `realifyCircuit` and `complexifyCircuit` are literal gatewise list maps.  A
  simulation operator theorem has the typed form `eval target = wireEmbed
  (eval source)`; source and target operators are never asserted literally
  equal across scalar fields or dimensions.
- The direct Equation 63 map is proved only as a checked matrix reindexing of
  the same composition.  No distinct direct placed-gate or wire-facing circuit
  translator is part of the public semantics.
- Circuit-facing state columns are defined independently by transporting the
  sum-index columns through `addedBasisEquiv`.  Evolution theorems apply the
  actual translated evaluator to these columns and prove the resulting
  equality.
- A bottom probability is the sum of scalar basis weights over the actual
  false and true assignments of the distinguished top wire.  Generic theorems
  prove these marginalized weights are nonnegative and sum to the full total
  weight.  Named probability theorems use normalized source and target state
  subtypes, whose preservation follows from matrix unitarity.
- Gate count means chronological list length in the abstract-matrix gate
  model.  Width is `Fintype.card` of the wire type.  Local arity is the card of
  a placed gate's stored local wire type; `maxLocalArity [] = 0`, so exact
  maximum `+1`/`+2` theorems require a nonempty circuit.
- A `SupportLayering` is a resource certificate whose nonempty layers flatten
  to the exact chronological circuit and have pairwise support-disjoint gates.
  Its depth is the number of layers.  This syntactic condition does not change
  evaluation or imply quaternionic commutation.  Every literal primary image
  gate uses the same added top wire, so every valid support layering of that
  image has depth exactly the source gate count.  This says nothing about an
  alternative translation or the paper's unconstructed multi-top proposal.
- A dense local description counts scalar-entry slots: arity `d` gives exactly
  `4^d` slots.  The primary translations multiply total slots by `4`, and the
  visible composition multiplies them by `16`.  Slots are not scalar bits,
  encoded bytes, arithmetic operations, allocation work, or runtime.
- `translationWork` is an externally supplied additive natural-valued cost.
  The theorem `translationWork_le_gateCount_mul` is conditional on a proof
  that each occurrence costs at most `K`; it does not construct such a cost
  model or prove translation time.
- An `ExactGateCompiler` is supplied certified data, not a global instance: it
  includes a primitive predicate, an expansion circuit, primitive membership,
  and exact evaluator equality.  Compiled count is the exact sum of expansion
  counts and is at most `s*K` only under an explicit per-gate `K` premise.
  The compiler interface supplies no generic synthesis algorithm, finite
  universal set, discrete scalar encoding, or finite-precision approximation.
- For a supplied `LegalSchedule`, scheduled simulation applies the fixed-order
  theorem to exactly that chronological circuit.  It does not select a
  schedule, establish schedule independence, or implement Definition 5's
  uniform classical generator, runtime, discrete encoding, or postprocessing
  machine.  Separately, deterministic functions between finite outcome types
  are covered extensionally, without a computation-cost claim.

### Corrected Table 1 boundary

For either primary one-added-wire translation, the formal resource comparison
is the following.  Here `s` is source gate count, `D` is total source dense
scalar-entry slots, and `K` is an explicit premise about a separately supplied
compiler.

| Quantity | Source circuit | Literal abstract image | After a supplied `ExactGateCompiler` |
|---|---|---|---|
| Width | `n` | exactly `n + 1` | `n + 1` (the compiler uses the same target wires) |
| Gate count | `s` | exactly `s` | exact sum of expansion counts; at most `s*K` only with the per-image-gate bound `K` |
| Support depth | any chosen certificate has depth at most `s` | every valid layering has depth exactly `s` because all image gates use the top wire | the canonical serial certificate has depth equal to compiled count, hence at most `s*K` under the same premise; no optimal-depth claim |
| Local arity | bounded by `d`, when assumed | bounded by `d + 1` | bounded only if every supplied expansion carries a separate arity bound |
| Dense scalar slots | `D` | exactly `4*D` | no bound follows from `ExactGateCompiler` alone |
| Operator semantics | `eval c` | the typed embedded operator | exactly the same embedded operator by the compiler certificate |

For the visible quaternion-to-real composition, width and local arity increase
by `2`, dense slots by exactly `16`, and the newest shared top wire again forces
literal-image support depth equal to `s`.  None of these rows is a bit-cost,
preprocessing-time, elementary-synthesis, or BQP theorem.  In particular, the
paper's unconditional `2^(d+1)` primitive count and `t*2^(d+1)` depth entries
are not retained.

## Dimensions and empty types

An `N × N` source matrix embeds into a `2N × 2N` target matrix under either
primary embedding, represented by a sum index rather than informal arithmetic
on dimensions.  Direct quaternionic realification uses four sum sectors and
has target dimension `4N`.  Circuit basis types are nonempty even for zero
wires.  General matrix lemmas retain empty index types when true.  In
particular, the realification determinant identity and its special-orthogonal
consequence need no `Nonempty` hypothesis; both sides have determinant `1` in
dimension zero.
