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
    Ray.lean                 normalized phase quotients and index boundary
    RayAudit.lean            non-root quotient consumers and edge examples
    RayObservables.lean      basis distributions, events, and pushforwards on rays
    RayEvolution.lean        unitary and locally-unitary circuit actions on rays
    RayDescentAudit.lean     non-root descent consumers and boundary examples
    Realification.lean       complex → real state columns and outcomes
    RealificationOrbit.lean  complex phase as doubled-real sector rotation/orbit
    RealificationOrbitObservables.lean  descended bottom marginal distribution
    RealificationOrbitBoundary.lean  exact obstruction to ordinary RealRay descent
    RealificationOrbitAudit.lean  non-root complete consumers and strictness checks
    Complexification.lean    quaternion → complex state columns and outcomes
    Unitary.lean             normalized state evolution under unitary matrices
    Distribution.lean        finite events and deterministic pushforwards
    DistributionLaws.lean    identity and composition laws for pushforwards
  Semantics/
    Core.lean                literal operator and chronological-circuit equality
    Measurement.lean         fixed-input, basis-input, pure-input, and distribution agreement
    CoreAudit.lean           edge-index examples and semantic axiom spot checks
    StatePhase.lean          normalized exact/sign/right-phase relations
    StatePhaseAudit.lean     normalized left-phase rejection and API consumers
    Ray.lean                 representative phase iff quotient-constructor equality
    OperatorPhase/
      ComplexReal.lean       global, basis-sided, and projective operator phase
      ComplexRealCircuit.lean  sided composition and evaluator-backed circuits
      ComplexRealAudit.lean  unitary strictness witnesses and API consumers
      Quaternion.lean        side-correct five-relation quaternionic operator phase
      QuaternionCircuit.lean sided composition and four evaluator-backed circuits
      QuaternionKernel.lean  dimension-sensitive kernel and rank-one exception
      QuaternionAudit.lean   non-root order, vacuity, kernel, and API diagnostics
    BasisBehavior.lean       certified reversible computational-basis action
    BasisBehaviorCircuit.lean evaluator-backed certified circuit behavior
    BasisBehaviorAudit.lean  non-root complete consumers and vacuity witness
    Density.lean             finite RCLike PSD, trace-one density matrices
    Effect.lean              Loewner effects, Born values, and probability laws
    EffectSeparation.lean    separation of densities by genuine physical effects
    DensityAudit.lean        non-root complete consumers and mixed-state checks
    Channel.lean             bundled unitaries and channel/all-effect equality
    ChannelPhase.lean        real/complex projective and global-phase kernels
    ChannelCircuit.lean      evaluator-backed locally-unitary channel wrappers
    ChannelAudit.lean        non-root complete consumers and boundary examples
    Hierarchy/
      OutputPhase.lean       all-pure basis agreement iff output-row phase
      State.lean             ray/distribution/event/postprocessing arrows
      Operator.lean          unitary channel and circuit covering arrows
    HierarchyAudit.lean      non-root hierarchy strictness and exact coverage
    Simulation.lean          directional cross-model relation vocabulary
    SimulationEncoding.lean  representative coordinate equivalences
    SimulationWrappers.lean  exact matrix/circuit/schedule/compiler wrappers
    SimulationOutcomes.lean  decoded weights/distributions/events/pushforwards
    SimulationAudit.lean     non-root allocations and concrete scope checks
    Approximation/
      Operator.lean          scoped RCLike Euclidean induced operator distance
      OperatorPhase.lean     real sign and complex one-global-phase budgets
      Quaternion.lean        native underlying-real quaternion operator norm
      State.lean             finite L2 columns and right-state-ray budgets
      Distribution.lean      half-L1 total variation and deterministic contraction
      Strictness.lean        exact fixed-budget nontransitivity witnesses
    ApproximationAudit.lean  non-root allocation and concrete metric checks
  Circuit/
    Placement.lean           noncommutative-safe contextual gate placement
    AddedWire.lean           shared distinguished-wire equivalences/reindexing
    Basic.lean               locality-certified gates and ordered semantics
    LocalUnitary.lean        locally-unitary closure under chronological append
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
    OutcomeDecoder.lean      explicit one/two-added-wire outcome decoders
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
`Semantics/SimulationEncoding.lean` packages the strongest checked coordinate
facts: each of the four raw canonical columns is an `ℝ`-linear equivalence with
an explicit decoder, and each restriction to normalized representatives is an
ordinary `Equiv`. These are bijections of representative coordinate carriers,
not equivalences of ordinary ray spaces or behaviors.

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
These remain useful representative relations.

`State/Ray.lean` installs those same scalar-correct relations as three explicit
setoids and defines `RealRay`, `ComplexRay`, and `QuaternionRay` as quotients of
normalized states. It stays below the semantic layer: the real quotient is
built from `Real.SignEquivalent`, the complex quotient from
`Complex.RightPhaseEquivalent`, and the quaternionic quotient from
`Quaternion.RightPhaseEquivalent` with the phase strictly on the right.
`RebitRay`, `QubitRay`, and `QuaterbitRay` are the `Bool`-indexed aliases.
Each namespace supplies `mk`, exact constructor equality, representative
existence, induction, invariant-function lifting, and function extensionality;
the real API additionally identifies constructor equality with literal
equality or pointwise negation. There is deliberately no chosen
`Ray → NormalizedState` representative.

The index boundary is exact: `realRay_nonempty_iff`,
`complexRay_nonempty_iff`, and `quaternionRay_nonempty_iff` prove that a ray is
inhabited exactly when its finite index type is inhabited, while explicit
`IsEmpty` instances rule out normalized rays on `Empty`.
`State/RayAudit.lean` stays outside the public root and exercises the full
stable quotient surface through scalar-specific aggregate consumers, the
inhabitation boundary, and concrete rebit `-1`, qubit `I`, and quaterbit
right-`j` equalities.

`State/RayObservables.lean` descends computational-basis weights, normalized
`FiniteDistribution`s, finite-event weights, and deterministic pushforwards to
each ray type. Every definition has a representative computation theorem;
pushforward by `id` is the original ray distribution and successive maps
compose as `g ∘ f`. `State/DistributionLaws.lean` owns the two scalar-neutral
pushforward laws so they can be reused without importing ray semantics.

`State/RayEvolution.lean` descends only normalization-preserving dynamics. A
supplied unitary matrix acts on each ray when the finite index has decidable
equality; identity and composition are exact, with first `U` then `V` equal to
the action of `V * U`. A chronological circuit acts only with an explicit
`IsLocallyUnitary` certificate. The empty circuit is the identity, and
`C ++ D` acts first by `C` and then by `D`; `Circuit/LocalUnitary.lean` proves
that the appended certificate exists. These circuit theorems remain meaningful
for zero wires because `BitBasis Empty` has one element. No arbitrary matrix
or uncertified circuit is lifted to normalized rays.

`Semantics/Ray.lean` identifies each normalized representative phase predicate
with equality of the corresponding quotient constructors. The non-root
`State/RayDescentAudit.lean` consumes the complete descent surface and checks
representatives, chronological order, proof irrelevance, and the zero-wire
boundary. Stage 4B introduces no density matrix, effect, channel,
approximation, or cross-model embedding claim.

Stage 4C resolves the separate complex-to-real ray boundary in three narrow
leaves. `State/RealificationOrbit.lean` defines the direct two-sector action of
a complex scalar, independently proves the unit-action relation is an
equivalence, and forms `RealSectorOrbit`. Its encoder and decoder give
`ComplexRay I ≃ RealSectorOrbit I`; this is a representation equivalence,
not ordinary real-ray, operator, circuit, or channel equality. The second
canonical column and every normalized pure `realTopState` are in the same
orbit as the first. `State/RealificationOrbitObservables.lean` descends only
the bottom marginal distribution and identifies it with the source complex
ray distribution. `State/RealificationOrbitBoundary.lean` proves that either
canonical column survives in `RealRay` exactly for phases `±1`, and that a
constructor-compatible source-ray-to-ordinary-real-ray lift exists exactly on
an empty index type. The raw representative intertwining theorems remain the
correct layer for arbitrary matrices. `State/RealificationOrbitAudit.lean`
stays outside the public root and consumes the three stable leaves through
aggregate APIs plus `1`/`I`, full-versus-bottom-distribution, arbitrary-top,
and empty-index diagnostics.

Outcome preservation is proved coordinatewise:

```text
weight(source i) = weight(target (top=0, i)) + weight(target (top=1, i)).
```

Total-weight and normalized-state corollaries then follow.  For the real case,
`reducedRealOuter` also proves the paper's rank-one reduced-matrix equality
directly.  The separate finite density/effect core described below is now
available, but it is not a dependency of this representative-level theorem
and does not turn `reducedRealOuter` into a generic partial trace.

`State/Distribution.lean` packages any finite nonnegative real weight function
of total mass one as a `FiniteDistribution`.  Generic normalized states map to
their basis distributions.  Finite-event sums and deterministic pushforwards
are normalized, nonnegative, and congruent under pointwise equality;
`State/DistributionLaws.lean` additionally proves identity and compositional
functoriality for deterministic pushforwards. This is a finite semantic API,
not a measure-theory, randomized-computation, or runtime layer.

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

`Semantics/Density.lean` supplies the finite mixed-state core used by later
same-space channel semantics. `DensityMatrix 𝕜 I` stores exactly a
positive-semidefinite matrix and a proof that its trace is one; Hermiticity is
derived. The implementation is theorem-generic over `RCLike 𝕜`, while
`RealDensityMatrix` and `ComplexDensityMatrix` are the model aliases exposed by
this project. Pure densities use the ket--bra matrix
`Matrix.vecMulVec ψ (star ψ)`, and computational-basis densities are its
`Pi.single` specializations. Existing `RealState` and `ComplexState` values
embed as pure densities. An explicit impossibility theorem rules out a
trace-one density on an empty index type.

Unitary mixed-state evolution is
`DensityMatrix.unitaryConjugate U hU ρ`, whose matrix is exactly
`U * ρ * Uᴴ`. Positivity, Hermiticity, and trace one are proved from the
stored density invariants and the supplied unitary certificate. Identity fixes
every density, pure evolution agrees with ket evolution, and chronological
composition is explicit: first `U`, then `V`, is conjugation by `V * U`.

`Semantics/Effect.lean` defines a genuine physical `Effect 𝕜 I` by the
Loewner bounds `0 ≤ E` and `E ≤ 1`; arbitrary matrices and arbitrary
trace-test functionals are not effects. Zero, identity, complement, normalized
rank-one projectors, and basis effects are constructed with their bounds.
`Effect.bornScalar E ρ` is `trace (E * ρ)`, and
`Effect.bornValue E ρ` is its real part. The scalar pairing is proved real
and nonnegative, while the real value is proved to lie in `[0,1]` and to obey
the expected zero, identity, complement, pure, and basis formulas. Basis
effects on pure real and complex densities recover the existing
computational-basis weights exactly.

`Semantics/EffectSeparation.lean` proves the nontrivial extensionality result

```text
ρ = σ ↔ ∀ E : Effect 𝕜 I, bornValue E ρ = bornValue E σ.
```

The reverse implication uses only normalized rank-one projector effects. It
identifies their trace pairings with quadratic forms, extends equality from
unit vectors through an explicit zero/nonzero split, and applies
symmetric/Hermitian polarization. Thus the final quantifier is over genuine
physical effects, not algebraic test matrices. The theorem needs no artificial
nonempty assumption; density values themselves cannot inhabit the empty
index case.

The non-root `Semantics/DensityAudit.lean` imports only the separation leaf.
Eight exact-allocation aggregates consume all 97 stable declarations
(`40 + 52 + 5`) once, and concrete `Bool` examples check pure/basis
compatibility, the mixed state `(1/2) I`, Born bounds and complements, unitary
conjugation, physical separation, and empty-index impossibility. Among these
Stage 6 leaves, the public root imports only `Density`, `Effect`, and
`EffectSeparation`. This layer
itself deliberately has no `ChannelEq` or `AllMeasurementEq`; the separate
Stage 7 leaves consume it. Neither layer supplies quaternionic
density/positivity theory, partial trace, Kraus maps, instruments, or
cross-model mixed-top simulation.

`Semantics/BasisBehavior.lean` separates a raw transition diagnostic from
certified classical reversible behavior. `BasisTransition unitPhase U x y`
says only that one input column is a unit-phased basis ket at `y`, and
`BasisTransitionRelationEq` compares those predicates extensionally. Either
relation can be empty for a unitary matrix. A genuine
`BasisPermutationImplementation unitPhase U p` instead supplies an explicit
`Equiv.Perm I` and proves the designated transition for every input. Unit
phase implies nonzero phase, so the implemented permutation is unique rather
than stored with an extra uniqueness axiom.

`SameBasisBehavior` is defined only from two implementation certificates and
means equality of their certified permutations. The real, complex, and
quaternionic specializations prove exact equivalences, on this certified class
only, with the correctly sided input phase, output phase, and
`BasisMeasurementEq` relations. Exact equality and real/complex global phase
or quaternionic central sign give only the justified forward preservation
arrows. Quaternionic column witnesses multiply on the right and row witnesses
on the left; their order is proved with `star a * b` and `b * star a`,
respectively.

`Semantics/BasisBehaviorCircuit.lean` stores a locally unitary chronological
circuit, its explicit basis permutation, and an implementation proof for
`OrderedCircuit.eval`. It derives evaluated unitarity and lifts the same
certified equivalences, exact-evaluator implication, and global/central-phase
arrows. The generic empty circuit implements the identity permutation,
including on zero wires. This layer says nothing about gate-list equality,
resources, schedule certificates, cross-model embeddings, channels, or all
effects.

The non-root `Semantics/BasisBehaviorAudit.lean` consumes the entire stable
core and circuit API. Its strictness witness uses two exact rational real
rotations, both unitary and everywhere nonzero, with no phased basis
transition and hence equal empty raw relations, but unequal
`false → false` basis weights. Neither matrix admits a certified basis
permutation. This proves that a raw transition biconditional cannot replace
the explicit certificate even on unitaries.

`Semantics/OperatorPhase/ComplexReal.lean` separates four same-space operator
relations for each commutative scalar. `RealGlobalSignEq` and
`ComplexGlobalPhaseEq` use one scalar for the complete matrix. Input-basis
phase attaches a right phase to each input column; output-basis phase attaches
a left phase to each output row. Projective action quantifies over every
normalized pure input but compares the resulting raw output rays, so it does
not assert that an arbitrary rectangular matrix preserves normalization. All
eight definitions are intentionally transparent and have complete equivalence
laws. The input relations imply `BasisMeasurementEq`; the output and
projective relations imply `PureInputBasisMeasurementEq`.

`ComplexRealCircuit.lean` wraps those relations through
`OrderedCircuit.eval`. Chronology determines the valid congruences: a common
later circuit preserves input-column phase, a common earlier circuit preserves
output-row phase, and projective action permits a common earlier circuit only
when local unitarity certifies normalized-input surjectivity. There is no
generic two-sided congruence. `ComplexRealAudit.lean` remains outside the root;
its rational `3/5,4/5` unitary family proves the advertised strictness and
incomparability results are not singular-matrix artifacts.

`OperatorPhase/Quaternion.lean` keeps five noncommutative comparisons
separate. `QuaternionCentralSignEq` permits only one central real scalar
`s` with `s*s=1`; it is not arbitrary unit-quaternion phase.
`QuaternionInputRightPhaseEq` attaches a unit quaternion on the right of each
input column, while `QuaternionOutputLeftPhaseEq` attaches one on the left of
each output row. `QuaternionRawProjectiveActionEq` quantifies over every raw
input column and `QuaternionProjectiveActionEq` over every normalized pure
input. Normalizing by a positive central real scalar, with the zero column
handled separately, proves these last two relations equivalent for every
finite rectangular input type without unitarity or nonemptiness assumptions.
For an empty operator input type the normalized quantifier is vacuous and the
raw relation tests only the unique zero column, so both sides are trivially
true.

`QuaternionCircuit.lean` owns the side-correct matrix composition laws and
exactly four evaluator-backed wrappers: central sign, input-right phase,
output-left phase, and normalized projective action. There is deliberately no
raw-projective circuit predicate. A common later evolution preserves input
phase, a common earlier evolution preserves output phase, raw projective
action admits arbitrary compatible evolution on either side, and normalized
projective action needs unitarity only for a common earlier evolution. Circuit
projective action is nonvacuous even on zero wires because `BitBasis W` is
always inhabited and has normalized basis columns.

`QuaternionKernel.lean` isolates the heavier converse. For finite square
matrices with `[DecidableEq I]`, explicit `1 < Fintype.card I`, and only `U`
assumed unitary, either raw or normalized all-right-ray action is equivalent
to `QuaternionCentralSignEq U V`; no unitarity premise on `V` is needed. The
dimension hypothesis is sharp. At rank one, the scalar matrix for `q` is
projectively trivial exactly when `Quaternion.normSq q = 1`, equivalently when
that scalar matrix is unitary. `Quaternion.j` is a checked unitary,
projectively trivial, noncentral witness. No theorem in this three-leaf public
layer promotes projective, basis-measurement, or central-sign equality to
channel or all-effect equality. `QuaternionAudit.lean` is a non-root diagnostic
consumer that checks multiplication order, consumes the generic
raw/normalized bridge, and exercises the dimension-two kernel and rank-one
exception. The bridge theorem itself covers the empty-input boundary through
the zero-column branch of its proof; the audit does not add a separate `Empty`
specialization.

`Semantics/Channel.lean` bundles a square `RCLike` matrix and its unitary proof
as `UnitaryOperator 𝕜 I`, with explicit real and complex aliases. Its
chronological `followedBy` operation is intentionally not an ambiguous
multiplication instance: `U.followedBy V` means first `U`, then `V`, and stores
`V * U`. `UnitaryOperator.evolve` delegates to Stage 6 conjugation and satisfies
the corresponding identity and composition laws.

`ChannelEq U V` quantifies over every `DensityMatrix 𝕜 I` and compares the
complete evolved density outputs. `AllMeasurementEq U V` quantifies over every
density input and every genuine `Effect 𝕜 I`; arbitrary trace-test matrices
never inhabit this definition. Both are equivalence relations and are
congruent under chronological composition. The forward implication is direct,
and the converse applies Stage 6 physical-effect separation to the two evolved
density matrices for each input, proving
`channelEq_iff_allMeasurementEq`.

`Semantics/ChannelPhase.lean` adds raw real and complex projective-action
relations and proves them equivalent to the existing normalized relations by
an explicit zero/nonzero normalization argument. Channel equality implies
normalized and raw projective action, while one real global sign or complex
global phase cancels from unitary conjugation. For `[Nonempty I]`, basis
columns and their pairwise sums prove that a ray-fixing unitary has one common
scalar, yielding

```text
global sign/phase ↔ raw projective action ↔ normalized projective action
                  ↔ ChannelEq ↔ AllMeasurementEq.
```

These inhabited-space kernel theorems need neither a determinant argument nor
a dimension-at-least-two premise. The nonempty hypothesis is mathematically
essential at the matrix API: no density exists on an empty index, so
`ChannelEq` is then vacuous. Separate `realGlobalSignEq_of_isEmpty` and
`complexGlobalPhaseEq_of_isEmpty` theorems derive phase equality from exact
subsingleton matrix equality instead of misrepresenting vacuous channel
quantification as physical evidence.

`Semantics/ChannelCircuit.lean` stores a chronological gate list and its
local-unitarity certificate in `UnitaryCircuit 𝕜 W`, then derives the
`UnitaryOperator` of `OrderedCircuit.eval`. Identity, append, associativity,
extensionality, and evaluator laws are exact. In particular,
`C.append D` maps to `C.toOperator.followedBy D.toOperator`, whose matrix is
`eval D * eval C`. `CircuitChannelEq` and `CircuitAllMeasurementEq` are honest
equivalence relations on these certified bundles; exact evaluator equality,
global phase, projective action, two-pair append, and common earlier/later
congruences all lift through the evaluator. Although the matrix converses need
`Nonempty I`, `BitBasis W = W → Bool` is canonically inhabited even at zero
wires, so the circuit characterizations discharge that premise internally.

The non-root `Semantics/ChannelAudit.lean` imports only `ChannelCircuit` and
allocates all 139 stable declarations exactly as `41 + 40 + 58` through 23
aggregate consumers. Its concrete checks distinguish a genuinely different
identity/swap channel using one physical basis effect, verify real `-1` and
complex `I` global phases, record the empty-index matrix/vacuous-channel
boundary, and exercise the inhabited zero-wire circuit case. Among the Stage 7
leaves, the public root imports only `Channel`, `ChannelPhase`, and
`ChannelCircuit`. No channel leaf
defines quaternionic positivity, partial trace, a Kraus map, an instrument,
cross-model channel equality, or mixed-top simulation.

The Stage 8 hierarchy is split into three stable leaves. `Hierarchy/State.lean`
characterizes finite-distribution equality by singleton events, all finite
events, and all deterministic pushforwards to finite targets in the same
universe. It then exposes the exact-representative-to-ray and
ray-constructor-to-basis-weight arrows for all three scalar systems.
`Hierarchy/OutputPhase.lean` proves the stronger rectangular theorem: with
only a finite input type,

```text
real output-row sign       ⇔ all-pure-input real basis weights
complex output-row phase  ⇔ all-pure-input complex basis weights
quaternion output-left phase ⇔ all-pure-input quaternion basis weights.
```

The proof needs no output finiteness, unitarity, decidable equality, nonzero
row, or nonempty-index assumption. It extends normalized agreement to raw
inputs and separates each row through a zero-row/nonzero-pivot cancellation
argument; quaternion multiplication remains on the left. Empty input and
output types are covered by the same theorem.

`Hierarchy/Operator.lean` composes those results with the existing channel
kernel and evaluator APIs. On inhabited real/complex unitary spaces it gives
the direct global-phase/projective iff, while channel and all-effect equality
have named pure-input and basis-measurement consequences. The circuit wrappers
compare only `OrderedCircuit.eval`. The three stable leaves export exactly
`9 + 13 + 27 = 49` declarations. The non-root `HierarchyAudit.lean` allocates
all 49 exactly, packages the rational unitary twists as channel/all-effect
counterexamples, separates complex and quaternionic distributions from rays,
and consumes the certified-classical iff theorems only under their permutation
certificates. Its 33 local axiom endpoints are diagnostic rather than imports
of the public root. It also records that empty finite-distribution and
normalized-state types are uninhabited instead of testing theorems through
impossible values. No hierarchy leaf adds a quaternionic channel, cross-model
certificate, metric, or resource claim.

## Directional cross-model semantics

`Semantics/Simulation.lean` supplies the generic vocabulary for comparisons
whose scalar, index, or carrier type changes. The definitions are oriented from
source to target and keep every policy argument explicit:

- `ExactStateEncoding encode decode` is exactly
  `Function.LeftInverse decode encode`; it constrains no target value outside
  the encoder image.
- `LosslessStateEncoding` adds equality of supplied source and target
  total-weight functionals.
- `ExactOperatorEmbedding` states `target = embed source`, while
  `StateIntertwining` states exact matrix action after supplied input and output
  encoders.
- `DecodedBasisWeightAgreement` and `DecodedDistributionAgreement` state exact
  equality after an explicit decoder. Their `AllTop...` variants quantify
  explicit `Top` and `Input` parameter types rather than hiding an ancilla
  convention.

These predicates have composition and specialization theorems, but no
`Equivalence` instances: direction, decoding, and changed spaces are part of
their meaning. The stable generic leaf exports 38 declarations.
`Semantics/SimulationEncoding.lean` adds 20 concrete declarations for the four
canonical columns: left- and right-inverse facts, losslessness, four raw
real-linear equivalences, and four normalized representative equivalences.
The Stage 9A portion of non-root `SimulationAudit.lean` allocates all
`38 + 20 = 58` declarations and instantiates the generic top policy with
normalized `Rebit` and `Qubit` coefficient parameter types.

`Semantics/SimulationWrappers.lean` adds 16 stable proof-bearing wrappers. Two
classify rectangular matrix action for every raw `ℝ × ℝ` or `ℂ × ℂ`
coefficient pair; three classify Equation 63 reindexing and both translated
placed-gate denotations; four classify the two primary circuit operators and
their raw-coefficient state actions; three classify one supplied legal
schedule and injective preservation of an explicit schedule-operator gap; two
classify the composed quaternion-to-real operator and nested coefficient
action; and two classify exact compilation under supplied compiler data.
`SimulationAudit.lean` allocates these as `2 + 3 + 4 + 3 + 2 + 2`, exercises
both canonical coefficient pairs, rectangular and raw-empty indices, the
existing unequal-schedule witness, inhabitable identity compilers, and
zero-wire circuits, and remains outside the public root.

This representative-level strength does not erase the previously checked
boundaries. Complex phase does not descend through a canonical realification
column to ordinary `RealRay`; `RealSectorOrbit` is the correct target quotient.
The concrete top parameters select linear combinations of the two canonical
columns; they do not assert a factorized target state, mixed joint density, or
partial trace. Indeed `NonProductWitness.encodedState_not_pureTopBottomProduct`
refutes that factorization reading for one normalized realified state. Stage 9B
does not weaken that boundary: its coefficient pairs are raw coordinates, not
pure or product top states. Equation 63 remains a named row/column reindexing,
not another wire-facing translator; a schedule is supplied without choice or
independence; and conditional compiler wrappers do not prove compiler
existence, synthesis, approximation, or runtime.

`Simulation/OutcomeDecoder.lean` exposes one-wire point/distribution decoders
and their two-wire compositions without importing circuit evolution. The
one-wire distribution decoder is proved equal to
`FiniteDistribution.pushforward tailBits`. The two-wire decoder first removes
the outer realification wire, yielding the intermediate complex outcome
carrier, and then removes the inner complexification wire. Updated
`Simulation/Postprocessing.lean` retains the full target distributions until
those decoders are applied, including the missing composed quaternion-to-real
distribution, event, and deterministic-pushforward closure.

`Semantics/SimulationOutcomes.lean` adds exactly 18 proof-bearing wrappers:
two representative decoded-weight wrappers and four each for complex-to-real,
quaternion-to-complex, one supplied scheduled quaternion-to-complex circuit,
and composed quaternion-to-real outcomes. Each four-theorem family separates
raw point weights from normalized distributions, finite events, and
deterministic pushforwards. Point-weight wrappers require no local unitarity;
the three normalized levels require locally unitary circuits. The non-root
audit allocates the semantic surface as `2 + 4 + 4 + 4 + 4` and separately
allocates the ten decoder and eight concrete postprocessing declarations in two
infrastructure aggregates. No wrapper asserts product/mixed-top structure,
partial trace, a channel/all-effect relation, randomized postprocessing, or a
resource theorem.

`Semantics/Approximation` is a separate semantic metric layer. Real and
complex matrices use mathlib's explicitly scoped Euclidean induced L2 norm.
Quaternionic matrices remain unbundled: their norm is the operator norm of the
underlying-real continuous linear action on finite `PiLp 2` columns, and a
theorem identifies it with the L2 norm of canonical complexification. No
quaternionic matrix `Norm`, `Metric`, `RCLike`, or C⋆ instance is installed.
The operator, one-global-phase/central-sign, normalized right-state-ray, and
finite-distribution relations have separate names, zero-budget exact bridges,
and additive-budget composition laws. Total variation is exactly half L1 and
contracts under deterministic pushforward. The strictness leaf gives exact
real, complex-unitary, raw-phase-sensitive, and Boolean-distribution
counterexamples to fixed-budget equivalence. These modules compare exact
mathematical values; finite scalar encodings, rounding, accumulated circuit
error, approximate compiler/synthesis construction, runtime, and uniformity
remain Goal 3 work. Goal 2 registry and release stages remain pending until
their independent coverage and build gates close.

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
`Semantics/BasisBehaviorCircuit.lean` additionally certifies the matrix, gate,
and singleton circuit as implementing `x ↦ x XOR b` for every basis input.
That all-input classification is distinct from the original ground-column and
prepended-circuit theorems, which each concern one known external input. There
is no unknown-state preparation, primitive synthesis, or uniform cost claim.

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

Any two legal schedules give gate lists that are permutations of the same
occurrence identifiers,
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
`LegalSchedule`.  It preserves occurrence count, local unitarity of every gate
occurrence, the stated arity bounds, operator embedding, and bottom probability
equality separately for that schedule.  It neither chooses among legal
schedules nor equates them.
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
no density-state, signaling, or cryptographic conclusion is drawn. It also
prevents the normalized top-sector coefficient parameter in the generic
pure-state formulas from being misread as a product-factor certificate.

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
  the induced group map is injective and `MulEquiv`-isomorphic to its explicitly
  defined range, and an
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
- Heavy semantic diagnostics stay outside the public root; in particular,
  `OperatorPhase/QuaternionAudit.lean` consumes all three public quaternionic
  operator-phase leaves, and `Semantics/BasisBehaviorAudit.lean` consumes the
  certified-basis leaves and their raw-transition strictness witness, while
  `Semantics/DensityAudit.lean` consumes the complete density/effect/separation
  surface and `Semantics/ChannelAudit.lean` consumes the complete
  channel/phase/circuit lift. None becomes a transitive dependency.
- Small exact examples guard signs, multiplication order, placement, and
  outcome semantics.
- `docs/Traceability.md` and `docs/Corrections.md` are updated in the same stage
  as corresponding declarations.
- Release verification includes a downstream import module that imports only
  `QuaternionicComputing`.
