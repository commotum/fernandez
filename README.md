# Quaternionic Computing — Lean 4 formalization

This repository reconstructs and independently verifies José M. Fernandez and
William A. Schneeberger's paper *Quaternionic Computing*
(`quant-ph/0307017v2`) as a reusable Lean library.

The source extraction is in `Fernandez/fernandez-2003.md`. Goal 1's completed
paper reconstruction is recorded under `goal-1/`; the active semantic
classification retrofit is staged under `goal-2/`, and the remaining frontier
is reindexed under `goal-3/`. Lean-changing stages follow the authoritative
incremental workflow in `BUILD-PLAN.md`.

The project is pinned to Lean 4.31.0 and mathlib v4.31.0.  Once dependencies are
available, build it with:

```sh
lake build
```

The public import is:

```lean
import QuaternionicComputing
```

Narrow consumers can instead import one of these selected leaves:

```lean
import QuaternionicComputing.Scalar.Quaternion
import QuaternionicComputing.Scalar.Phase
import QuaternionicComputing.Matrix.Realification
import QuaternionicComputing.Matrix.Complexification
import QuaternionicComputing.Matrix.Unitary
import QuaternionicComputing.Matrix.Determinant
import QuaternionicComputing.Matrix.QuaternionRealification
import QuaternionicComputing.Matrix.QuaternionRealificationUnitary
import QuaternionicComputing.Matrix.ProperImage
import QuaternionicComputing.Matrix.KroneckerCommute
import QuaternionicComputing.State.Basic
import QuaternionicComputing.State.RealPhase
import QuaternionicComputing.State.ComplexPhase
import QuaternionicComputing.State.Ray
import QuaternionicComputing.State.DistributionLaws
import QuaternionicComputing.State.RayObservables
import QuaternionicComputing.State.RayEvolution
import QuaternionicComputing.State.Realification
import QuaternionicComputing.State.RealificationOrbit
import QuaternionicComputing.State.RealificationOrbitObservables
import QuaternionicComputing.State.RealificationOrbitBoundary
import QuaternionicComputing.State.Complexification
import QuaternionicComputing.State.Unitary
import QuaternionicComputing.State.Distribution
import QuaternionicComputing.Semantics.Core
import QuaternionicComputing.Semantics.Measurement
import QuaternionicComputing.Semantics.StatePhase
import QuaternionicComputing.Semantics.Ray
import QuaternionicComputing.Semantics.Hierarchy.OutputPhase
import QuaternionicComputing.Semantics.Hierarchy.State
import QuaternionicComputing.Semantics.BasisBehavior
import QuaternionicComputing.Semantics.BasisBehaviorCircuit
import QuaternionicComputing.Semantics.Density
import QuaternionicComputing.Semantics.Effect
import QuaternionicComputing.Semantics.EffectSeparation
import QuaternionicComputing.Semantics.Channel
import QuaternionicComputing.Semantics.ChannelPhase
import QuaternionicComputing.Semantics.ChannelCircuit
import QuaternionicComputing.Semantics.Hierarchy.Operator
import QuaternionicComputing.Semantics.Simulation
import QuaternionicComputing.Semantics.SimulationEncoding
import QuaternionicComputing.Semantics.SimulationWrappers
import QuaternionicComputing.Semantics.SimulationOutcomes
import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal
import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit
import QuaternionicComputing.Semantics.OperatorPhase.Quaternion
import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit
import QuaternionicComputing.Semantics.OperatorPhase.QuaternionKernel
import QuaternionicComputing.Circuit.Placement
import QuaternionicComputing.Circuit.AddedWire
import QuaternionicComputing.Circuit.Basic
import QuaternionicComputing.Circuit.LocalUnitary
import QuaternionicComputing.Circuit.BasisPreparation
import QuaternionicComputing.Circuit.OrderSanity
import QuaternionicComputing.Circuit.Realification
import QuaternionicComputing.Circuit.Complexification
import QuaternionicComputing.Circuit.Cost
import QuaternionicComputing.Circuit.Ordering
import QuaternionicComputing.Circuit.OrderingWitness
import QuaternionicComputing.Circuit.ProductInputOrderingWitness
import QuaternionicComputing.Circuit.Depth
import QuaternionicComputing.Circuit.DescriptionCost
import QuaternionicComputing.Circuit.Compilation
import QuaternionicComputing.Circuit.ScheduleCount
import QuaternionicComputing.Simulation.Basic
import QuaternionicComputing.Simulation.ComplexToReal
import QuaternionicComputing.Simulation.QuaternionToComplex
import QuaternionicComputing.Simulation.QuaternionToReal
import QuaternionicComputing.Simulation.NonProductWitness
import QuaternionicComputing.Simulation.Examples
import QuaternionicComputing.Simulation.Scheduled
import QuaternionicComputing.Simulation.OrderingWitness
import QuaternionicComputing.Simulation.Resources
import QuaternionicComputing.Simulation.CompiledResources
import QuaternionicComputing.Simulation.OutcomeDecoder
import QuaternionicComputing.Simulation.Postprocessing
```

The matrix layer exports dimension-safe, injective, multiplicative,
adjoint-preserving embeddings on sum indices.  Complex unitaries realify to
special orthogonal matrices.  Quaternionic unitaries complexify injectively to
complex unitary and symplectic matrices; the available formal proof narrows
their determinant to `1` or `-1`, while selecting the positive sign remains a
documented paper-proof obligation that is not needed by the simulation.
Equation 63's direct four-real-sector map is also formalized: all sixteen
coordinate formulas compile, its `4N` dimension is explicit, and it is exactly
the composed embedding after the checked sector permutation `[3,1,0,2]`.
Quaternionic unitaries embed into `SO(4N)` and are equivalent to their image,
while at rank one an explicit witness proves that the image is proper in
`SO(4)`.  Separate `SO(4)` and `SU(4)` witnesses record the other qualified
non-surjectivity results without inferring operational lower bounds.

The state layer supplies explicitly normalized finite real, complex, and
quaternionic states. Real sign, complex unit right phase, and quaternionic unit
right phase are explicit equivalence relations on normalized representatives.
They preserve computational-basis weights and finite distributions, commute
with compatible raw matrix/circuit action, and are preserved by normalized
unitary evolution; no channel or all-effect conclusion is inferred.
Quaternionic phase is corrected to act strictly on the right.
`RealRay`, `ComplexRay`, and `QuaternionRay` now quotient the normalized
representatives by exactly those relations; `RebitRay`, `QubitRay`, and
`QuaterbitRay` are their two-level aliases. Constructor equality is exactly
the scalar-correct phase relation, and real-ray equality is exactly equality
or pointwise negation. Every ray can be eliminated through a normalized
representative, but no canonical representative is selected. These quotients
exist exactly when their finite index type is nonempty; in particular there is
no normalized ray on `Empty`. Computational-basis weights, normalized finite
distributions, finite-event weights, and deterministic pushforwards descend to
all three ray types, with exact representative computation, identity, and
composition laws. Supplied unitaries act on rays; identity acts trivially and
applying `U` then `V` is exactly the action of `V * U`. Locally-unitary
chronological circuits act as well: the empty circuit is the identity and
`C ++ D` acts first by `C` and then by `D`, including on the inhabited
zero-wire basis. These operations require explicit finite-index, decidable-
equality where matrix evolution needs it, unitarity, and local-unitarity
premises. They do not define arbitrary-matrix evolution, channels, or a
canonical quaternion-to-complex target-ray map. Complex-to-real realification
has a separate checked boundary: unit complex phase acts on the two real
sectors by
`(x,y) ↦ (re(η)x + im(η)y, -im(η)x + re(η)y)`.
`RealSectorOrbit` quotients normalized doubled-real states by exactly this
action, and `complexRayEquivRealSectorOrbit` proves it equivalent to
`ComplexRay`. Both canonical columns and every normalized `Rebit` top-sector
coefficient encoding give the same orbit, whose bottom marginal distribution
is exactly the source ray distribution. Each canonical complex-to-real or
quaternion-to-complex raw column is also an explicit real-linear coordinate
equivalence, and its restriction is an equivalence of normalized
representatives. These representative bijections are not ray equivalences.
In particular, the realification result is not ordinary `RealRay` equality:
either canonical column preserves the target real ray only for phases `±1`, and a
representative-compatible `ComplexRay I → RealRay (I ⊕ I)` lift exists only
in the vacuous `IsEmpty I` case. Thus rays precede representative embeddings;
the raw column intertwining and decoded bottom outcomes remain valid. Both
representation-column evolution identities and pointwise bottom
computational-basis weight preservation hold for every normalized `Rebit` or
`Qubit` top-sector coefficient. The scalar-independent `FiniteDistribution`
API packages finite events and deterministic pushforwards of normalized
outcome weights.

The semantic layer gives these comparisons explicit, noninterchangeable
names. `ExactOperatorEq` is literal same-type matrix equality and
`ExactCircuitEq` is literal equality of chronological circuit evaluations.
`OutputWeightEqAt`, `BasisMeasurementEq`, and
`PureInputBasisMeasurementEq` respectively quantify over one supplied input,
all computational-basis inputs, and all normalized pure inputs.
`NormalizedDistributionEq` is equality of packaged finite outcome
distributions. None of these basis-observation relations is silently promoted
to ray or channel equality.

Classical reversible basis behavior is certified rather than inferred from a
possibly empty transition predicate. `BasisPermutationImplementation` carries
an explicit `Equiv.Perm` and proves that every input column is a unit-phased
basis ket at its designated output. `SameBasisBehavior` can therefore be
formed only from two certificates and means equality of their permutations.
For certified real, complex, and quaternionic operators this is equivalent to
the correctly sided input phase, output phase, and `BasisMeasurementEq`
relations. The evaluator-backed `BasisClassicalCircuit` supplies the same
classification for locally unitary circuits. These equivalences are confined
to the certified class: they are not generic matrix, global-phase, projective,
channel, or all-effect equalities.

Finite mixed states and physical effects have a separate same-space API.
`DensityMatrix 𝕜 I` stores a positive-semidefinite matrix of trace one,
and `Effect 𝕜 I` stores a matrix in the Loewner interval `0 ≤ E ≤ 1`.
The core is proved uniformly for `RCLike` scalars; the supported model aliases
are `RealDensityMatrix`, `ComplexDensityMatrix`, `RealEffect`, and
`ComplexEffect`. Pure and basis densities recover the existing normalized
real/complex state weights. `Effect.bornValue` is the real part of
`trace (E * ρ)` and is proved to lie in `[0,1]`, with exact zero, identity,
complement, pure, and basis laws. Unitary evolution is
`U * ρ * Uᴴ`, and applying `U` then `V` is conjugation by `V * U`.
Most importantly, equality of Born values against every genuine physical
effect is equivalent to equality of density matrices; the proof uses
normalized rank-one projector effects rather than arbitrary trace tests.
There is no density matrix on an empty index type. This state/effect layer is
consumed by the separate unitary-channel semantics; neither layer introduces
quaternionic positivity, partial trace, Kraus maps, instruments, or mixed-top
simulation.

`UnitaryOperator 𝕜 I` bundles a finite `RCLike` square matrix with its unitary
certificate. `ChannelEq U V` requires equality of the complete evolved
density matrix for every density input. `AllMeasurementEq U V` requires equal
Born values for every density input and every genuine physical `Effect`, and
`channelEq_iff_allMeasurementEq` proves these notions equivalent through
physical-effect separation. Chronological composition is explicit:
`U.followedBy V` stores `V * U` and evolves first by `U`, then by `V`.

For finite real and complex unitary operators on an explicitly nonempty matrix
index, global sign/phase, raw projective action, normalized projective action,
and channel equality have the same kernel. Global phase implies channel
equality without a nonempty premise; the premise is required for the converse
because density quantification is vacuous on an empty index. Named empty-index
theorems instead record exact equality of the empty square matrices. The
`UnitaryCircuit` wrapper stores a chronological circuit and local-unitarity
certificate and derives its evaluated operator. `CircuitChannelEq` and
`CircuitAllMeasurementEq` are evaluator-backed equivalence relations with
exact and append congruences. Since `BitBasis W = W → Bool` is canonically
inhabited, their real/complex phase characterizations remain nonvacuous even
at zero wires and need no extra caller-supplied nonempty evidence. No
quaternionic, cross-model, decoded-marginal, or mixed-top channel theorem is
claimed.

The hierarchy leaves close the remaining same-space arrows. For arbitrary
rectangular matrices with only a finite input type, agreement of every
normalized pure input's computational-basis output weights is equivalent to
one unit phase on each output row: a real sign, a complex phase, or a
quaternionic phase multiplying on the left. No unitarity, nonempty-index, or
finite-output premise is needed. Finite-distribution equality is likewise
equivalent to agreement on every finite event and on every deterministic
pushforward to a finite target in the same universe. Together with the ray and
channel kernels, this gives, on an inhabited finite space, the checked
real/complex unitary chain
`global phase ↔ projective action ↔ ChannelEq ↔ AllMeasurementEq`, while
output-row phase is only
`PureInputBasisMeasurementEq`. Exact unitary twists prove that neither
output-row nor basis-only agreement implies channel equality; normalized
complex and quaternionic examples prove that equal basis distributions need
not determine a ray. The certified `SameBasisBehavior` equivalences remain
restricted to supplied basis-permutation certificates.

Cross-model comparisons use a separate directional API.
`ExactStateEncoding` exposes an encoder and decoder and means only that the
decoder is a left inverse on encoded source values. `LosslessStateEncoding`
also preserves an explicit total-weight functional;
`ExactOperatorEmbedding`, `StateIntertwining`, and the decoded weight and
distribution relations keep source, target, encoder, decoder, and observation
scope visible. Their `AllTop...` forms quantify an explicitly supplied
top-sector parameter type. They are not reflexive/symmetric/transitive
same-space equivalence relations, and they assert no ray, channel, product,
partial-trace, or all-effect semantics. `SimulationWrappers` now gives the
existing matrix, placed-gate, primary-circuit, scheduled, composed, and
conditional-compiler results 16 proof-bearing directional classifications.
Its state theorems quantify raw coefficient pairs, not normalized top states
or product subsystems. Its schedule is supplied rather than chosen, and its
compiler is explicit input data rather than an existence or synthesis result.
`SimulationOutcomes` now classifies decoded point weights, normalized full-
target distributions, finite events, and deterministic pushforwards for the
primary, supplied-schedule, and composed simulations. One- and two-added-wire
decoders remain visible, and one-wire decoding is proved equal to pushforward
by `tailBits`.

Real and complex matrices have four separate phase comparisons:
`RealGlobalSignEq`/`ComplexGlobalPhaseEq`, input-column phase, output-row
phase, and `RealProjectiveActionEq`/`ComplexProjectiveActionEq`. Matching
circuit predicates compare only `OrderedCircuit.eval`. Global phase implies
both basis-phase relations and projective action. Input-column phase preserves
all basis-input weights; output-row phase and projective action preserve
all-normalized-pure-input basis weights. Input phase is stable under a common
later evolution, output phase under a common earlier evolution, and a common
earlier projective evolution requires unitarity. These relations do not assert
cross-model simulation, and input- or output-dependent basis phase is not
promoted to channel equality. The separate channel layer proves that, for
bundled real/complex square unitaries on an inhabited finite space, one global
phase and all-input projective action are each exactly `ChannelEq`.

Quaternionic matrices have a side-sensitive five-relation layer. One global
operator phase is restricted to `QuaternionCentralSignEq`, a real central
`±1`; input-column phases multiply on the right, output-row phases on the
left, and raw versus normalized all-input right-ray action are stated
separately. The raw and normalized projective relations are equivalent on
every finite input type, including the empty case where both are trivial.
Four circuit wrappers compare evaluator semantics (there is deliberately no
raw-projective wrapper); because `BitBasis W` is always inhabited, their
normalized-input quantifier is nonvacuous even for zero wires. In square
dimension at least two, with decidable finite indices and only the first
operator assumed unitary, projective action is equivalent to one central real
sign. Rank one is the sharp exception: every unit quaternion gives a
projectively trivial scalar operator, and `j` is an explicit noncentral
witness. None of these results is upgraded to channel or all-effect equality.

The circuit layer supplies locality-certified gates on arbitrary finite wire
types, noncommutative-safe placement on arbitrary injected supports, explicit
chronological evaluation, and unitarity preservation.  A finite
`LegalSchedule` lists every gate occurrence exactly once and certifies the
supplied precedence constraints; it does not assume that the relation was
generated by a DAG.  Pairwise commutation of distinct global gate denotations
is sufficient for all legal schedules to agree.  Conversely, an explicit pair
of disjoint, locally unitary quaternionic one-wire gates has two legal orders
with unequal operators and unequal normalized output weights.  This is an
existential witness, not a claim that every disjoint quaternionic pair is
order-sensitive.  On the normalized ground product input, the same orders
instead yield distinct right-phase rays while agreeing on every
computational-basis weight; this is not a signaling or entanglement theorem.
A known computational-basis input can be prepared from the ground column by a
certified XOR permutation gate. Its matrix, full-support gate, and singleton
circuit implement the XOR permutation on every basis input; the separate
ground-column and prepended-circuit theorems remain one-known-input statements,
not arbitrary-state preparation or uniform synthesis. One-gate realification and complexification
reuse one shared distinguished top wire, commute with actual contextual
placement, preserve local unitarity, and increase local arity by exactly one.

The resource layer measures only explicitly stated finite structures.  A
`SupportLayering` consists of nonempty, support-disjoint layers whose flattening
retains the chronological circuit.  Every layering of either literal
one-added-wire image has depth exactly the source gate count because every
image gate uses the shared top wire.  Empty-precedence occurrence families
have exactly `(Fintype.card ι)!` chronological orders; no factorial or
exponential count is asserted for general precedence relations.  Dense local
matrices have exactly `4^d` scalar-entry slots at arity `d`, with total factors
`4` for either primary translation and `16` for their composition.  These are
slot counts, not bit complexity or runtime.

The simulation layer proves corrected constructive forms of the paper's
Theorems 2 and 4 for arbitrary ordered finite circuits.  It separately exports
whole-operator embedding, canonical and arbitrary top-sector-coefficient state
evolution laws, and equality of normalized bottom computational-basis
probabilities.
Abstract gate count is unchanged, width grows by exactly one, and every local
gate grows by exactly one wire; maximum-arity theorems handle the empty circuit
explicitly.  Composing the two translations proves the corrected
quaternion-to-real corollary with two added wires and exact `+2` arity.
The direct Equation 63 API is a matrix-level reindexing theorem supplementing
this canonical compositional circuit construction; it does not introduce a
second wire-facing translator.  A high-level `NonProductWitness` gives a
normalized realified state whose added top wire cannot be factored from the
bottom system, without upgrading that fact to a mixed-state or signaling
claim. Consequently the normalized `Rebit`/`Qubit` top-sector parameters used
by the pure-state formulas must not be read as certificates that the encoded
target state factors into an independent top subsystem and bottom subsystem.
The proof-bearing wrapper leaf classifies the primary and composed evaluator
equalities as `ExactOperatorEmbedding` and their arbitrary raw-coefficient
amplitude laws as `AllTopStateIntertwining`. Equation 63 remains equality only
after its named row/column reindexing and is not a circuit translator.
For a supplied finite legal schedule, the scheduled bridge applies the same
exact quaternion-to-complex theorem to that schedule's chronological circuit
without selecting a schedule or asserting schedule independence.  The
order-sensitive witness remains operator-distinct after this translation.
The normalized output equality also extends to every finite event and every
deterministic finite classical postprocessing map.
The stable outcome layer starts from the full added-wire target distributions,
then applies `addedWireDistributionDecoder` or
`twoAddedWireDistributionDecoder`; the composed decoder removes the outer
realification wire before the inner complexification wire. Raw point-weight
wrappers need no unitarity premise and do not call unnormalized weights
probabilities. Packaged distribution, event, and pushforward wrappers require
locally unitary circuits and normalized source states. Scheduled forms retain
one supplied schedule and do not choose or identify schedules. None of these
results asserts a product or mixed top state, partial trace, channel/all-effect
equality, randomized postprocessing, or a resource bound.

Primitive compilation is deliberately conditional.  A supplied
`ExactGateCompiler` must provide a primitive predicate, exact chronological
expansions, primitive membership, and evaluator equality.  Only then does the
library prove exact compiled count and a bound `s * K` from an explicit
per-image-gate bound `K`; the corresponding canonical serial depth has the
same conditional bound.  No generic synthesis algorithm or compiler instance
is postulated.

The finite scheduling API formalizes the mathematical core of the paper's
Definition 5, but not its classical uniform circuit generator, runtime,
discrete encoding, randomized postprocessing, or finite-precision model.
Accordingly, the finite results do not establish polynomial-time compilation
or BQP containment.

See `docs/Traceability.md`, `docs/Corrections.md`,
`docs/Conventions.md`, and `docs/Architecture.md` for exact source mappings and
mathematical conventions.  `docs/ReleaseReport.md` is the complete handoff,
and `docs/AxiomAudit.md` explains the executable audit.  No completed module
may contain `sorry`, `admit`, or an unexplained project-specific axiom.
