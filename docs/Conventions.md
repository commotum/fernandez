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
- General algebraic theorems use arbitrary finite index types.  Circuit basis
  states will be bit assignments such as `Fin n → Fin 2`, not numerals whose
  binary encoding must be unfolded in every proof.

## Quaternionic scalar side

Quaternionic column vectors are treated as **right modules**.  For a vector
`ψ : ι → ℍ[ℝ]` and scalar `q`, right scaling means the pointwise vector
`i ↦ ψ i * q`.  A quaternionic matrix acts from the left and therefore respects
right scaling by associativity:

```text
A *ᵥ (ψ · q) = (A *ᵥ ψ) · q.
```

Consequently, equality up to global quaternionic phase is represented using a
unit quaternion on the **right**, `ψ = ψ' · q`.  The paper places the phase on
the left in Equation (45); that relation is not preserved by arbitrary left
matrix evolution and is corrected here.  Lean's ordinary `SMul` notation is not
silently reused for this right action; the library will give it a named
operation or an explicit opposite-ring formulation.

## Conjugation and adjoints

- Complex and quaternionic conjugation use `star`.
- Matrix adjoint uses `Matrix.conjTranspose`; for real matrices this reduces to
  transpose under the trivial star convention.
- Quaternionic unitarity is expressed using the generic star-monoid predicate
  `unitary (Matrix ι ι ℍ[ℝ])`, which requires both
  `Aᴴ * A = 1` and `A * Aᴴ = 1`.  Mathlib's convenience abbreviation
  `Matrix.unitaryGroup` assumes a commutative coefficient ring and therefore is
  not used for quaternion matrices.
- “Symplectic group” in the paper means the compact quaternionic unitary group,
  not a separately chosen bilinear-form matrix group.

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

Matrix embeddings will first map each source entry to its `2 × 2` scalar
matrix, flatten the matrix of blocks, and then reindex so the added two-level
coordinate is the leading/top coordinate.  The exact Lean index type selected
by the Stage 1 API probes must have a documented equivalence to this semantic
ordering.

## States, phases, and measurements

The library keeps four relations distinct:

1. literal vector equality;
2. equality up to a unit scalar on the documented side;
3. equality of embedded operators or embedded state evolution;
4. equality of observable computational-basis outcome weights/distributions.

For a coordinate `ψ i`, its computational-basis weight is its scalar norm
square.  In a doubled target space, forgetting the top wire means summing the
two target weights above each bottom basis index.  The main simulation theorem
will state this equality explicitly.  It will not define “simulation” to be
whatever relation the embedding happens to satisfy.

Normalized states are introduced only at the semantic boundary.  Algebraic
embedding and evolution lemmas should apply to arbitrary vectors whenever the
proof does not need normalization.  Density matrices and partial traces are
secondary formulations; direct outcome-weight theorems are the minimum needed
for the paper's computational claim.

## Circuits and wire placement

- The central semantic object is an ordered list of well-formed placed gates.
  This directly models a fixed evaluation order and supports induction.
- A later DAG/topological-sort layer may produce such lists, but it will not be
  required to prove the algebraic embedding theorem.
- A local gate is lifted to global basis states by restricting bit assignments
  to its support and requiring equality off that support.
- Quaternionic placement will not rely on the commutative Kronecker interchange
  identity.  Permutations and contextual padding use only `0`, `1`, and explicit
  index equivalences, with multiplication order visible in definitions.
- Semantic permutation matrices used to describe placement are not counted as
  physical swap gates unless a separate synthesis theorem constructs them.

## Dimensions and empty types

An `N × N` source matrix embeds into a `2N × 2N` target matrix, represented by a
product or sum index rather than informal arithmetic on dimensions.  Circuit
basis types are nonempty even for zero wires.  General matrix lemmas may retain
empty index types when true; determinant/group claims will state any required
`Nonempty` assumptions explicitly.

