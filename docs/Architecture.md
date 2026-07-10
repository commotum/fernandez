# Library Architecture

## Design objective

The library is organized by reusable mathematics rather than the paper's
section order.  Paper-specific statements are thin packaging over general
scalar, matrix, state, circuit, and simulation results.

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
    QuaternionRealification.lean         Equation 63 coordinates and algebra
    QuaternionRealificationUnitary.lean  direct unitary → SO(4N) image
    ProperImage.lean         explicit qualified non-surjectivity witnesses
    KroneckerCommute.lean    corrected noncommutative interchange boundary
  State/
    Basic.lean               normalized columns, weights, right phases
    RealPhase.lean           real `±1` ray relation and invariance
    ComplexPhase.lean        complex unit-phase equivalence and invariance
    Realification.lean       complex → real state columns and outcomes
    Complexification.lean    quaternion → complex state columns and outcomes
    Unitary.lean             normalized state evolution under unitary matrices
    Distribution.lean        finite events and deterministic pushforwards
  Semantics/
    Core.lean                literal operator and chronological-circuit equality
    Measurement.lean         fixed-input, basis-input, pure-input, and distribution agreement
    CoreAudit.lean           edge-index examples and semantic axiom spot checks
    StatePhase.lean          normalized exact/sign/right-phase relations
    StatePhaseAudit.lean     normalized left-phase rejection and API consumers
  Circuit/
    Placement.lean           noncommutative-safe contextual gate placement
    AddedWire.lean           shared distinguished-wire equivalences/reindexing
    Basic.lean               locality-certified gates and ordered semantics
    BasisPreparation.lean    known basis input as a unitary XOR permutation
    OrderSanity.lean         concrete noncommuting evaluator audit
    Cost.lean                generic width/arity bounds and maxima
    Realification.lean       one-gate complex-to-real translation
    Complexification.lean    one-gate quaternion-to-complex translation
    Ordering.lean            finite legal schedules and independence criterion
    OrderingWitness.lean     disjoint unitary order-dependence witness
    ProductInputOrderingWitness.lean  ray dependence with equal basis weights
    Depth.lean               support-disjoint layering certificates
    DescriptionCost.lean     dense scalar-slot and conditional work measures
    Compilation.lean         supplied exact primitive-compiler interface
    ScheduleCount.lean       factorial unconstrained-order enumeration
  Simulation/
    Basic.lean               generic sum-index → added-wire state transport
    ComplexToReal.lean       corrected Theorem 2 family
    QuaternionToComplex.lean corrected Theorem 4 family
    QuaternionToReal.lean    corrected Corollary 1 family
    NonProductWitness.lean   high-level pure nonfactorization example
    Scheduled.lean           fixed legal-schedule simulation bridge
    OrderingWitness.lean     translated observable ordering witness
    Resources.lean           shared-top depth and dense-slot consequences
    CompiledResources.lean   conditional compiled count/depth consequences
    Postprocessing.lean      finite event and deterministic-output closure
    Examples.lean            exact non-real and quaternionic end-to-end checks
  AxiomAudit.lean
QuaternionicComputing.lean   stable public root import
```

The dependency direction remains acyclic: scalar and matrix infrastructure
support states and the circuit core; primary fixed-order simulations and the
finite scheduling layer both build on that core; scheduled simulation joins
those two branches; resource models and paper-specific wrappers sit above
them.  Generic modules must not import paper-specific wrappers.

## Embedding implementation

The canonical embedding definitions use `Matrix.fromBlocks` on sum indices.
This matches the paper's displayed matrices exactly, keeps the added sectors
visible, and lets multiplication and adjoint proofs use
`Matrix.fromBlocks_multiply` and `Matrix.fromBlocks_conjTranspose`, both valid
over noncommutative coefficient rings where applicable.

For square matrices, complexification is bundled as a ring homomorphism and
both primary doubled embeddings are bundled as injective star-monoid
homomorphisms.  At the
circuit boundary, `addedBasisEquiv` identifies `BitBasis W ⊕ BitBasis W` with
`BitBasis (Unit ⊕ W)`: the two sum sectors are exactly the false and true
assignments of one distinguished top wire.  This keeps wire bookkeeping out of
the scalar/matrix proofs while making the shared added wire explicit.

`Matrix/QuaternionRealification.lean` gives Equation 63 a transparent
four-sector index ordered `[Re, ImI, ImK, ImJ]`.  All sixteen component entries
are proved, and `directRealify_eq_reindex` identifies the map with
`realify (complexify A)` after the same pure sector permutation `[3,1,0,2]` on
rows and columns.  Algebraic laws are inherited through that checked equality.
The heavier unitary leaf packages the injective star homomorphism into
`SO(4N)` and an equivalence only with its image.  `ProperImage.lean` keeps
finite counterexamples out of the embedding core and proves explicitly that
the direct image is already proper in `SO(4)`.

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
weight and commute with arbitrary matrix action, and
`Quaternion.rightPhaseEquivalent_equivalence` packages it as an equivalence
relation.  `State/ComplexPhase.lean` provides the commutative complex analogue,
including basis-weight, total-weight, and arbitrary-matrix invariance.  Neither
relation is silently identified with equality of representative columns.

`State/RealPhase.lean` completes the scalar-level picture: its unit-sign
condition is proved equivalent to `s = 1 ∨ s = -1`, and real sign equivalence
is exactly literal equality or pointwise negation. `Semantics/StatePhase.lean`
then restricts exact equality and the three phase relations to normalized
representatives. It proves their equivalence laws, exact-to-phase implications,
computational-basis distribution consequences, raw rectangular matrix and
ordered-circuit naturality, and normalized unitary-evolution preservation.
These are representative relations; quotient state spaces and descended
operations are owned by the separate ray layer.

Outcome preservation is proved coordinatewise:

```text
weight(source i) = weight(target (top=0, i)) + weight(target (top=1, i)).
```

Total-weight and normalized-state corollaries then follow.  For the real case,
`reducedRealOuter` also proves the paper's rank-one reduced-matrix equality
directly.  A general density-operator hierarchy remains optional and is not a
dependency of the central theorem.

`State/Distribution.lean` packages any finite nonnegative real weight function
of total mass one as a `FiniteDistribution`.  Generic normalized states map to
their basis distributions.  Finite-event sums and deterministic pushforwards
are normalized, nonnegative, and congruent under pointwise equality.  This is
a finite semantic API, not a measure-theory, randomized-computation, or
runtime layer.

## Semantic comparison implementation

`Semantics/Core.lean` names literal equality separately from every weaker or
cross-model comparison. `ExactOperatorEq` compares matrices with the same row,
column, and scalar types. `ExactCircuitEq` compares only the chronological
evaluations of two ordered circuits; it does not require equal gate lists and
does not record resource, schedule, phase, or embedding information.

`Semantics/Measurement.lean` keeps observation quantifiers explicit.
`OutputWeightEqAt` concerns one supplied input column,
`BasisMeasurementEq` concerns every computational-basis input, and
`PureInputBasisMeasurementEq` concerns every normalized pure input.
`BasisWeightEq` compares one pair of output columns coordinatewise, while
`NormalizedDistributionEq` compares the finite distributions packaged from
normalized states. Pointwise basis-weight agreement is equivalent to that
packaged distribution equality and therefore preserves all finite events and
deterministic finite pushforwards.

These relations do not assert ray equality, channel equality, equality under
all physical effects, or cross-model simulation. In particular, deriving
basis-input agreement from the all-normalized-pure-input relation requires an
explicit proof that the chosen scalar weight normalizes every basis ket.

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

`Circuit/BasisPreparation.lean` handles only a classically known
computational-basis assignment.  XOR by that assignment is a self-inverse
permutation whose matrix is unitary over a compatible star semiring; as a
full-support placed gate it maps the all-zero basis column to the requested
column.  Prepending the gate obeys the established chronological evaluator.
There is no unknown-state preparation, primitive synthesis, or uniform cost
claim.

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

`Circuit/ProductInputOrderingWitness.lean` reuses the same gates on the
normalized pointwise-factorized ground input.  The resulting normalized
columns agree at three basis coordinates and have opposite `k` components at
the fourth.  Their common nonzero `00` coordinate proves that they are not
related by any unit right phase, while a separate theorem proves equality of
every computational-basis weight.  This leaf therefore audits the distinction
between ray-level state dependence and the observable chosen by the model; it
does not assert signaling, entanglement, causality violation, or security.

The paper's cut-poset language is not identified with this occurrence-order
API.  No type of temporal cuts, theorem that one topological sort totally
orders all cuts, topological-sorting algorithm, or uniform circuit-family
generator is supplied.  Those graph, runtime, and Definition 5 uniformity
claims remain outside the finite core.

`Circuit/ScheduleCount.lean` enumerates the permutations of the canonical
finite identifier list without duplicates.  Its length is exactly
`(Fintype.card ι)!`, and every enumerated order is legal for the empty
precedence relation.  Every legal schedule for any relation lies in this
all-orders enumeration, but the factorial is exact only for empty precedence;
it is not a count of the legal schedules of a general relation.

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
bottom probability sum.  Equation 63's `directRealify` is a matrix-level
reindexing theorem supplementing this canonical compositional circuit API; no
second wire-facing circuit translator is introduced.

`Simulation/NonProductWitness.lean` sits deliberately above the primary
simulator because it uses the actual added-wire encoding.  A normalized source
with rational amplitudes `3/5` and `(4/5)i` has canonical real coordinates
`(3/5,0,0,-4/5)`, which cannot factor even into unnormalized pure top and
bottom columns.  The neutral module name reflects its exact theorem surface:
no density-state, signaling, or cryptographic conclusion is drawn.

`Simulation/Postprocessing.lean` upgrades the pointwise normalized outcome
equalities to equality of the complete finite bottom distributions.  It then
proves equal weight for every finite event and equal pushforward distribution
for every deterministic map to another finite type, for both primary
simulations.  It does not implement classical-machine uniformity or charge for
postprocessing.

## Resource implementation

`Circuit/Depth.lean` defines `SupportLayering c` as chronological layers, each
nonempty, whose flattening is exactly `c` and whose distinct gates have
pairwise disjoint certified supports within a layer.  It is a cost certificate,
not an alternative evaluator: disjoint support is never used to infer
quaternionic commutation.  Any layering has depth at most gate count.  If every
gate uses a common wire, every layer is a singleton and every valid layering
has depth exactly gate count.  `Simulation/Resources.lean` applies this to the
literal realified, complexified, and composed circuits; their shared added top wire
forces support depth exactly equal to the source occurrence count.  This is
not a lower bound for other encodings or multi-top constructions.  Although a
real-valued source matrix has a proved block-diagonal realification identity,
the literal uniform gate translator does not implement the optional
real-gate/top-wire elimination.

`Circuit/DescriptionCost.lean` counts scalar-entry slots in explicit dense
local matrices.  A `d`-wire gate has exactly `4^d` slots, and a finite slot
bound yields the exact base-four logarithmic arity bound.  Gatewise `+1` and
`+2` arity translations multiply total slots by exactly `4` and `16`;
`Simulation/Resources.lean` instantiates these results.  Slot count omits
scalar bit length, compression, arithmetic, allocation, and primitive-gate
synthesis, so it is not a time or bit-complexity measure.

`Circuit/Compilation.lean` defines an `ExactGateCompiler` only as supplied
data: a primitive predicate, a chronological expansion of each gate, a
primitive-membership certificate, and exact evaluator equality.  It proves
whole-circuit semantic preservation, exact compiled count as the sum of the
per-gate counts, and `compiledCount ≤ sourceGateCount * K` from an explicit
per-source-gate bound `K`.  `Simulation/CompiledResources.lean` transports
these conditional theorems to both primary image circuits and gives a
canonical serial-depth bound under the same premise.  No instance asserts a
compiler or universal primitive library for arbitrary unitaries.

## Group and determinant scope

The simulations require multiplicativity, adjoint preservation, injectivity,
and unitarity preservation.  They do not require determinant one.  The current
determinant boundary is therefore explicit:

- `realify_det` proves `detℝ(realify A) = normSq(detℂ A)`, so a complex
  unitary maps to `SO(2N)`;
- a quaternionic unitary maps injectively to a complex unitary preserving the
  canonical symplectic form;
- simultaneous reindexing of the composed embedding proves that direct
  realification sends a quaternionic unitary to `SO(4N)` with determinant one;
  the induced group map is injective and equivalent to its image, and an
  explicit rank-one witness proves that image is not all of `SO(4)`;
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
