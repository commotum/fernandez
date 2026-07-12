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
subtypes. Their quotient types are separately named `ComplexRay` and
`QuaternionRay`.

Real phase is written on the right as well. `Real.SignEquivalent x y` carries
a scalar witness `s` with `s*s=1` and `x i = y i*s`; the library proves this is
exactly `s=1` or `s=-1`, hence exactly equality or pointwise negation. The
normalized wrappers `RealStatePhaseEq`, `ComplexStatePhaseEq`, and
`QuaternionStatePhaseEq` remain relations on concrete representatives. They
are not themselves quotient types, operator global phase, or channel equality.
The quotients `RealRay`, `ComplexRay`, and `QuaternionRay` identify precisely
these relations. Their `RebitRay`, `QubitRay`, and `QuaterbitRay` aliases use
`Bool` as the two-level index.

A ray carries no canonical normalized representative. Public elimination uses
`exists_rep`, `inductionOn`, or a phase-invariant `lift`; choosing a quotient
representative must not be treated as additional mathematical data. A finite
normalized ray exists exactly when its index type is nonempty. Hence
`RealRay Empty`, `ComplexRay Empty`, and `QuaternionRay Empty` are empty, in
contrast to circuit basis types such as `BitBasis W`, which remain inhabited
even when `W` has no wires.

Stage 4B descends computational-basis weights, normalized finite
distributions, finite-event weights, deterministic pushforwards, supplied
unitary evolution, and locally-unitary circuit evolution to all three ray
types. Matrix evolution requires a finite index with decidable equality and an
explicit proof of unitarity. Circuit evolution requires an explicit
`IsLocallyUnitary` certificate; it is defined on `BitBasis W`, which remains
inhabited even for zero wires. No operation on normalized rays is defined for
an arbitrary matrix or an uncertified circuit.

Evolution order follows the matrix convention exactly: applying `U` and then
`V` is the action of `V * U`. For chronological circuits, `C ++ D` acts first
by `C` and then by `D`. Identity matrices and empty circuits act trivially.
Deterministic postprocessing is covariant in the classical direction:
pushforward by `id` is unchanged, and first `f` then `g` is pushforward by
`g ∘ f`.

These descended ray operations do not themselves provide a density matrix,
physical effect, channel, or approximation relation. The finite real/complex
density-and-effect layer is separate and does not identify distribution
equality with density equality. Cross-model phase is handled separately.
For realification, right multiplication by `eta : ℂ` acts on each doubled
real coordinate pair by

```text
(x,y) ↦ (eta.re*x + eta.im*y, -eta.im*x + eta.re*y).
```

For unit `eta` this is the relation defining `RealSectorOrbit`; it is not the
global-sign relation defining `RealRay`. The canonical equivalence
`ComplexRay I ≃ RealSectorOrbit I` is a representation equivalence onto the
correct phase-orbit space. Either individual column survives as the same
ordinary real ray exactly when `eta = ±1`, and a constructor-compatible map
from complex rays to ordinary real rays exists only when the index type is
empty. The bottom marginal distribution, obtained by summing the two sector
weights over each source coordinate, does descend and equals the source
complex-ray distribution. The full doubled-real basis distribution generally
does not. Quaternionic right phase analogously mixes the two complex encoding
columns, but its cross-model orbit classification remains outside Stage 4C.

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
phases on the left even though real and complex multiplication commutes.

For bundled square real/complex unitaries, the separate channel layer proves
that one global sign/phase and all-input projective action have the same
physical channel exactly when the finite matrix index is inhabited. This does
not promote input-column or output-row phase families: input-dependent phases
can change interference, and output-dependent phases can be exposed by a later
basis change.

Quaternionic operator phase uses five distinct predicates:

```text
central sign:        V = s • U, where s : ℝ and s*s = 1
input column:        V y x = U y x * φ x
output row:          V y x = θ y * U y x
raw projective:      Uψ and Vψ lie on the same right ray for every raw ψ
normalized projective: the same comparison for every normalized pure ψ.
```

Thus `QuaternionCentralSignEq` means only a central real `±1`, never an
arbitrary unit quaternion. The input family in
`QuaternionInputRightPhaseEq` acts on the right; the output family in
`QuaternionOutputLeftPhaseEq` acts on the left. This multiplication order is
part of the definitions and their composition theorems, not a cosmetic choice.
The raw and normalized projective relations are equivalent for every finite
rectangular input type without a unitarity or nonempty hypothesis.

Circuit phase relations compare `OrderedCircuit.eval`, never gate lists,
schedules, resources, or embeddings. Because `eval (C ++ L) = eval L * eval C`,
input-column phase is preserved by a common later circuit and output-row phase
by a common earlier circuit. A common earlier normalized-projective evolution
needs a unitary certificate; arbitrary two-sided congruence is not assumed.
The quaternionic layer exports exactly four circuit relations—central sign,
input-right phase, output-left phase, and normalized projective action—and no
raw-projective circuit wrapper.

Normalized projective action compares raw output rays and does not claim output
normalization. When a rectangular operator's finite input index is empty, its
normalized-state quantifier is vacuous. For quaternionic raw projective action,
the only raw input is the zero column and the relation is trivially true, so
the raw/normalized equivalence remains valid at the empty type. A circuit
wrapper instead acts on `BitBasis W = W → Bool`, which is inhabited and admits
normalized basis states even when `W` has zero wires; that quantifier is not
vacuous.

The quaternionic converse is dimension-sensitive. For finite square matrices,
`[DecidableEq I]`, explicit `1 < Fintype.card I`, and only `U` assumed unitary,
raw or normalized projective action between `U` and `V` is equivalent to one
central real sign. Rank one is excluded for a mathematical reason: every unit
quaternion defines a unitary, projectively trivial scalar matrix, and
`Quaternion.j` is not a central sign. None of these phase relations is channel
equality or all-effect equality.

## Certified computational-basis behavior

Classical reversible behavior is not defined by comparing an unqualified
predicate of the form “`U|x⟩` is `|y⟩` up to phase.” The raw
`BasisTransition` predicate records one such column transition, and
`BasisTransitionRelationEq` compares all of them, but both relations may be
empty for a nonmonomial unitary. The audit proves this with two everywhere-
nonzero rational real rotations whose raw relations agree while a basis
measurement probability differs.

A genuine implementation has the form

```text
BasisPermutationImplementation unitPhase U p
```

where `p : Equiv.Perm I` is explicit and every input column `x` has exactly one
unit-phase entry at output `p x`, with zeros elsewhere. The scalar predicates
are `RealUnitSign`, `ComplexUnitPhase`, and `QuaternionUnitPhase`.
`SameBasisBehavior hU hV` is available only after both certificates have been
supplied and means equality of their permutations. It is deliberately not a
relation on arbitrary matrices and is not defined from measurement equality.

On the certified real, complex, and quaternionic classes, same permutation is
equivalent to the corresponding input-column phase, output-row phase, and
computational-basis measurement relation. For quaternions, input phases act on
the right and output phases on the left; the proof witnesses retain the
noncommutative orders `star a * b` and `b * star a`. Exact equality and one
real/complex global phase or quaternionic central sign preserve certified
behavior, but no converse to a global phase is claimed. In particular,
input-dependent phases need not define the same action on superpositions, so
certified basis behavior is not projective, channel, or all-effect equality.

`BasisClassicalCircuit` applies the same convention to
`OrderedCircuit.eval`. Its stored permutation describes evaluator behavior,
not equality of gate lists, schedules, resource counts, or compilers. The
empty circuit has the identity certificate, including at zero wires.

Known basis preparation has two distinct scopes. The certified XOR matrix,
full-support gate, and singleton circuit implement `x ↦ x XOR b` for every
basis input. The ground-column and prepended-circuit theorems use only the one
known input `groundBasis W`; they do not synthesize an arbitrary quantum state
or provide a uniform preparation algorithm.

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

## Density matrices, effects, and Born values

The same-space finite mixed-state core is theorem-generic over `RCLike 𝕜`.
The library's physical model aliases instantiate it only for the intended real
and complex cases:

```text
RealDensityMatrix I     = DensityMatrix ℝ I
ComplexDensityMatrix I  = DensityMatrix ℂ I
RealEffect I            = Effect ℝ I
ComplexEffect I         = Effect ℂ I
```

A `DensityMatrix 𝕜 I` stores exactly

```text
ρ.PosSemidef
trace ρ = 1.
```

Hermiticity is derived from positive semidefiniteness and is not redundant
structure data. A finite empty index type supports no density matrix, because
its trace is zero. Constructors that require a basis vector expose the
inhabited case locally; no global `Nonempty I` assumption is hidden.

Pure densities use the ket--bra order

```text
|ψ⟩⟨ψ| = Matrix.vecMulVec ψ (star ψ),
(|ψ⟩⟨ψ|) i j = ψ i * star (ψ j).
```

The basis density is the pure density of `Pi.single x 1`. The real and
complex constructors from `RealState` and `ComplexState` preserve this exact
entry convention.

A physical `Effect 𝕜 I` is a square matrix in the Loewner interval
`0 ≤ E ≤ 1`. It is not an arbitrary Hermitian matrix and never denotes an
arbitrary algebraic trace test. Zero, identity, complements, normalized
rank-one projectors, and computational-basis projectors inhabit this
structure. The scalar pairing and real probability are

```text
bornScalar E ρ = trace (E * ρ)
bornValue  E ρ = RCLike.re (bornScalar E ρ).
```

The scalar pairing is proved real and nonnegative; the real Born value is
proved to lie in `[0,1]`. The complement law is
`bornValue (1-E) ρ = 1 - bornValue E ρ`, and basis effects on pure
densities recover the existing real/complex squared-modulus basis weights.

Unitary density evolution follows the same left-action chronology as columns:

```text
unitaryConjugate U ρ = U * ρ * Uᴴ.
```

Applying `U` and then `V` therefore gives conjugation by `V * U`, not by
`U * V` and not by `Uᴴ * ρ * U`. This construction is available only with a
supplied unitary certificate and is proved to preserve positivity and trace
one.

For two density matrices, literal equality is equivalent to equality of their
Born values against every genuine physical effect. The separation proof uses
normalized rank-one projector effects and quadratic-form polarization; it
does not relabel arbitrary matrices as physical effects. This is a fixed-pair
state extensionality theorem. It is not `ChannelEq` or `AllMeasurementEq` by
itself; the separate channel layer now adds those operator quantifiers and uses
this theorem for its converse.

No quaternionic density/effect positivity, generic partial trace, Kraus map,
instrument, or arbitrary mixed-top simulation is introduced by this layer.

## Unitary channels and all physical measurements

A `UnitaryOperator 𝕜 I` stores a square matrix and an actual membership proof
in `unitary (Matrix I I 𝕜)`. The theorem-generic core uses `RCLike 𝕜`; the
physical aliases supplied here are real and complex. Evolution is the Stage 6
density conjugation. Chronological composition is named rather than hidden in
a multiplication instance:

```text
U.followedBy V       means first U, then V
matrix (U.followedBy V) = V * U
(U.followedBy V).evolve ρ = V.evolve (U.evolve ρ).
```

The two physical comparison relations have different visible quantifiers:

```text
ChannelEq U V :=
  ∀ ρ : DensityMatrix 𝕜 I, U.evolve ρ = V.evolve ρ

AllMeasurementEq U V :=
  ∀ (ρ : DensityMatrix 𝕜 I) (E : Effect 𝕜 I),
    bornValue E (U.evolve ρ) = bornValue E (V.evolve ρ).
```

`Effect` here is always the genuine Loewner-bounded structure. No arbitrary
matrix, algebraic trace test, or basis-effect-only family is substituted for
the quantifier. Complete output equality directly implies all-measurement
agreement; genuine-effect separation proves the converse for each density
input. Thus `ChannelEq ↔ AllMeasurementEq` over the generic `RCLike` core.

The real and complex phase kernel uses the existing orientation
`V = η • U`. One global sign/phase cancels from conjugation without an
inhabited-index premise. Conversely, channel equality implies normalized and
raw projective action, and on `[Nonempty I]` either projective relation forces
one common global scalar. Consequently, for real and complex finite unitaries
on an inhabited matrix index,

```text
global sign/phase
  ↔ raw projective action
  ↔ normalized projective action
  ↔ ChannelEq
  ↔ AllMeasurementEq.
```

The normalization bridge splits the zero column from nonzero columns and uses
a positive real inverse square root; no determinant or dimension-at-least-two
argument occurs. The `Nonempty I` premise is essential for interpreting the
matrix converse: there is no density input on an empty index, so `ChannelEq`
is vacuous there. The separate empty-index theorems prove global phase from
exact equality of the unique empty square matrices, not from that vacuous
channel relation.

`UnitaryCircuit 𝕜 W` stores an `OrderedCircuit` and its local-unitarity
certificate, then derives the `UnitaryOperator` of its evaluator.
`C.append D` acts first by `C`, then by `D`, so

```text
(C.append D).toOperator = C.toOperator.followedBy D.toOperator
eval (C ++ D) = eval D * eval C.
```

`CircuitChannelEq` and `CircuitAllMeasurementEq` apply the corresponding
operator relations to these derived evaluators. They are equivalence relations
and preserve exact evaluator equality, global phase, projective action, and
chronological append. Matrix phase converses require `Nonempty I`, but the
circuit basis `BitBasis W = W → Bool` is canonically inhabited even when `W`
has no wires, so no redundant nonempty argument appears in the circuit API.

None of these definitions supplies quaternionic density/channel positivity,
cross-model channel equality, decoded marginal semantics, partial trace,
Kraus maps, instruments, mixed-top simulation, or channel capacity.

## Hierarchy and observation scope

All-pure-input computational-basis agreement has an exact row-functional
classification. For arbitrary rectangular matrices with finite input type,
it is equivalent to one unit phase per output row. Real rows differ by signs,
complex rows by unit complex phases, and quaternionic rows by unit quaternions
on the **left**:

```text
V y x = theta y * U y x.
```

This theorem does not require either matrix to be unitary and remains valid
for empty input or output types. It does not identify output-row phase with
projective action or a channel: output-dependent phases are invisible to the
final basis measurement but become observable after later interference.
Checked unitary twists satisfy output-row phase and every pure-input basis
statistic while failing both `ChannelEq` and `AllMeasurementEq`.

For finite distributions, equality is equivalent to equality of every finite
event weight. It is also equivalent to equality of every deterministic
pushforward whose finite target lives in the same universe as the source; the
converse uses the identity postprocessing. The forward pushforward theorem
remains universe-polymorphic. These equivalences do not recover an amplitude
ray: normalized complex and quaternionic witnesses have identical complete
basis distributions but no common scalar-correct phase.

The resulting real/complex unitary kernel is

```text
global phase <-> projective action <-> ChannelEq <-> AllMeasurementEq,
```

with the existing inhabited matrix-space premise on the converse kernel.
Input-column phase, output-row phase/all-pure basis agreement, and certified
basis-permutation behavior are weaker or incomparable branches. The final
branch is equivalent to input/output/basis agreement only when both operators
carry explicit `BasisPermutationImplementation` certificates.

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
4. equality of an explicitly certified computational-basis permutation
   (`SameBasisBehavior` or `SameCircuitBasisBehavior`);
5. representative equality up to a unit scalar on the documented side;
6. literal equality in `RealRay`, `ComplexRay`, or `QuaternionRay`, which is
   exactly the corresponding representative relation;
7. equality of embedded operators or embedded state evolution;
8. one-input computational-basis output-weight agreement
   (`OutputWeightEqAt`);
9. all-basis-input agreement (`BasisMeasurementEq`);
10. all-normalized-pure-input basis agreement
   (`PureInputBasisMeasurementEq`);
11. equality of packaged computational-basis distributions
   (`NormalizedDistributionEq`);
12. literal equality of finite real/complex density matrices, equivalently
    equality of Born values against every genuine physical effect for that
    fixed pair; and
13. equality of complete unitary-channel outputs for every density input
    (`ChannelEq`), equivalently equality of every genuine-effect Born value
    for every density input (`AllMeasurementEq`).

The three input scopes in items 8–10 are not interchangeable. The generic
weight function need not normalize basis kets, so the theorem from
all-normalized-pure-input agreement to all-basis-input agreement requires that
normalization as an explicit hypothesis. Stage 6 proves that all physical
effects separate one fixed pair of density matrices; Stage 7 quantifies that
result over every evolved density input and proves
`ChannelEq ↔ AllMeasurementEq`. No basis-only relation is treated as either
one.

For a coordinate `ψ i`, its computational-basis weight is its scalar norm
square.  In a doubled target space, forgetting the top wire means summing the
two target weights above each bottom basis index.  The main simulation theorems
state this equality explicitly.  They do not define “simulation” to be
whatever relation the embedding happens to satisfy.

Normalized states are introduced only at the semantic boundary. Algebraic
embedding and evolution lemmas should apply to arbitrary vectors whenever the
proof does not need normalization. The separate density/effect layer supports
same-space finite mixed states, but generic partial trace remains absent;
direct outcome-weight theorems continue to be the minimum used by the paper's
current simulation results.

Concretely, `NormalizedState ι α weight` is a finite amplitude column paired
with the equation `totalWeight weight ψ = 1`.  The scalar weight is an explicit
parameter, avoiding any global squared-norm instance.  `RealState`,
`ComplexState`, and `QuaternionState` specialize it, and `Rebit`, `Qubit`, and
`Quaterbit` use `Bool` as the two-level basis.  This makes the missing `= 1` in
the paper's quaterbit definition impossible to omit.

The arbitrary-top-wire results currently cover every normalized pure top
rebit/qubit and prove pointwise bottom-weight equality. Although finite
same-space real/complex density matrices now exist, claims about arbitrary
mixed top states still require a cross-model joint-density encoding, partial
trace or decoded-effect semantics, and preservation theorems. They remain
explicitly partial and are not silently inferred from the pure-state results.

`FiniteDistribution α` means a real weight on a finite type, pointwise
nonnegative and summing to one.  `eventWeight` is a finite sum, and
`pushforward f` sums weights over the fibers of a deterministic map `f`.
Equality of the primary bottom distributions therefore implies equality for
all finite events, marginals encoded as deterministic maps, and deterministic
finite postprocessing.  It does not include randomized machines or their cost.
For `RealRay`, `ComplexRay`, and `QuaternionRay`, `distribution`,
`basisWeight`, `eventWeight`, and `pushforward` are literal quotient descents of
these representative constructions. Equality of these observables is weaker
than ray equality in general and is not used as the quotient relation.

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
