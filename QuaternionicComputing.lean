module

public import QuaternionicComputing.Scalar.Phase
public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.Matrix.QuaternionRealificationUnitary
public import QuaternionicComputing.Matrix.ProperImage
public import QuaternionicComputing.State.ComplexPhase
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification
public import QuaternionicComputing.State.Ray
public import QuaternionicComputing.State.RayObservables
public import QuaternionicComputing.State.RayEvolution
public import QuaternionicComputing.State.RealificationOrbit
public import QuaternionicComputing.State.RealificationOrbitObservables
public import QuaternionicComputing.State.RealificationOrbitBoundary
public import QuaternionicComputing.Semantics.Measurement
public import QuaternionicComputing.Semantics.StatePhase
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Semantics.Hierarchy.State
public import QuaternionicComputing.Semantics.BasisBehavior
public import QuaternionicComputing.Semantics.BasisBehaviorCircuit
public import QuaternionicComputing.Semantics.Density
public import QuaternionicComputing.Semantics.Effect
public import QuaternionicComputing.Semantics.EffectSeparation
public import QuaternionicComputing.Semantics.Channel
public import QuaternionicComputing.Semantics.ChannelPhase
public import QuaternionicComputing.Semantics.ChannelCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionKernel
public import QuaternionicComputing.Semantics.Hierarchy.Operator
public import QuaternionicComputing.Semantics.SimulationEncoding
public import QuaternionicComputing.Semantics.SimulationWrappers
public import QuaternionicComputing.Semantics.SimulationOutcomes
public import QuaternionicComputing.Circuit.OrderSanity
public import QuaternionicComputing.Circuit.BasisPreparation
public import QuaternionicComputing.Circuit.Realification
public import QuaternionicComputing.Circuit.Complexification
public import QuaternionicComputing.Matrix.KroneckerCommute
public import QuaternionicComputing.Circuit.Ordering
public import QuaternionicComputing.Circuit.ScheduleCount
public import QuaternionicComputing.Circuit.ProductInputOrderingWitness
public import QuaternionicComputing.Simulation.QuaternionToReal
public import QuaternionicComputing.Simulation.Examples
public import QuaternionicComputing.Simulation.NonProductWitness
public import QuaternionicComputing.Simulation.Scheduled
public import QuaternionicComputing.Simulation.OrderingWitness
public import QuaternionicComputing.Simulation.CompiledResources
public import QuaternionicComputing.Simulation.Postprocessing

/-!
# Quaternionic Computing

Public root module for the verified formalization of Fernandez and
Schneeberger's *Quaternionic Computing*.

The current public surface includes the quaternion component algebra, the
explicit correction of the paper's left-phase convention, complex and
quaternionic right-phase APIs, the two doubled finite-matrix embeddings, and
the direct four-sector quaternion-to-real embedding of Equation 63.  The
direct map is proved to be the composed embedding in a checked sector order,
and quaternionic unitaries embed into `SO(4N)`.  At rank one an explicit
`SO(4)` witness proves that this direct image is proper; separate `SO(4)` and
`SU(4)` matrices certify the other qualified non-surjectivity claims.  The
library also exports the embedding determinant results,
normalized finite states, both state-column measurement-preservation APIs,
and a checked non-product realification example.

The semantic layer names literal same-type operator equality, exact
chronological-circuit equality, fixed-input output-weight agreement,
all-basis-input agreement, all-normalized-pure-input basis agreement, and
packaged finite-distribution equality as separate relations.  Exact equality
has the expected congruence lifts, while distribution equality supplies finite
event and deterministic-pushforward consequences without being mislabeled as
ray or channel equality.

Normalized state representatives have a parallel phase layer: real states are
identified up to a proved `±1` sign relation, complex states up to unit right
phase, and quaternionic states strictly up to unit right phase.  Each is an
equivalence relation, follows from exact representative equality, preserves
the complete computational-basis distribution, and is natural under raw
matrix/circuit action and normalized unitary evolution. Quotient state spaces
are exported as `RealRay`, `ComplexRay`, and `QuaternionRay`. Their
computational-basis distributions, finite events, deterministic
postprocessing, unitary evolution, and locally-unitary chronological circuit
evolution descend to the quotients with representative, identity, and ordered-
composition laws. These operations do not assert channel equality or identify
equal basis distributions with equal rays.

Complex-to-real state realification has a separate, phase-correct quotient:
complex right phase becomes a rotation of the two doubled-real sectors, giving
`RealSectorOrbit` and a canonical equivalence `ComplexRay ≃ RealSectorOrbit`.
The bottom marginal distribution descends through that equivalence, whereas
the full doubled-real basis distribution and the ordinary sign quotient
`RealRay` generally do not.  In fact, either canonical realification column
defines a constructor-compatible map to `RealRay` exactly in the empty-index
case; for a normalized state, a unit complex phase preserves its column's
ordinary real ray exactly when the phase is `1` or `-1`.

Real and complex evaluated operators and chronological circuits additionally
have distinct global, input-column, output-row, and projective-action phase
relations. Global phase implies both sided basis-phase relations and
projective action; input-column phase guarantees basis-input measurement
agreement, while output-row phase and projective action guarantee
all-normalized-pure-input basis agreement. Chronological congruences preserve
the multiplication side, and common-earlier projective evolution carries an
explicit local-unitarity premise. These relations are neither channel equality
nor cross-model simulation. Quaternionic operators have a side-correct
parallel layer: input phases act on the right, output phases act on the left,
and global operator phase means only a central real sign. Raw and normalized
all-input projective action coincide; for unitary square spaces of dimension
at least two their kernel is exactly the central signs, while rank one has the
full unit-quaternion scalar family as an explicit exception.

Classical reversible computational-basis behavior is exported only through an
explicit permutation certificate: every input column must be a unit-phased
basis ket at its certified output. Equality of certified behavior means
equality of those permutations. On the certified real, complex, and
quaternionic classes it is equivalent to the corresponding input-phase,
output-phase, and basis-measurement relations, with quaternionic input phases
on the right and output phases on the left. The raw transition biconditional
remains a diagnostic predicate because two nonmonomial unitaries can satisfy
it vacuously. Certified circuit wrappers compare evaluations rather than gate
lists or resources, and the basis-preparation circuit separately exposes its
all-input XOR permutation and its known-ground-input preparation theorem.

Finite real and complex mixed states are represented by positive-semidefinite,
trace-one density matrices. Physical effects occupy the Loewner interval from
zero to identity, and their Born values are proved to lie in `[0, 1]`.
Normalized pure and computational-basis densities recover the existing state
weights, unitary evolution is the conjugation `U * ρ * Uᴴ`, and genuine
rank-one physical effects separate arbitrary density matrices. This layer does
not introduce quaternionic density matrices, partial trace, or Kraus channels.

Finite real and complex unitary operators and locally unitary chronological
circuits have a separate physical-channel layer. `ChannelEq` means equality of
the complete evolved density for every density input, while
`AllMeasurementEq` quantifies over every density input and every genuine
physical effect; the two are proved equivalent. On explicitly inhabited
matrix spaces, real global sign, complex global phase, raw and normalized
projective action, and channel equality have exact checked characterizations.
The evaluator-backed circuit versions inherit the canonically inhabited
computational basis even at zero wires. No result asserts a quaternionic
channel, cross-model channel equality, partial trace, or mixed-top semantics.

The same-space hierarchy is closed at its exact observation scopes. For
arbitrary rectangular real, complex, and quaternionic matrices with only a
finite input type, equality of computational-basis output weights for every
normalized pure input is equivalent to one unit phase per output row; the
quaternionic phase multiplies on the left. Finite-distribution equality is
equivalent to equality of every finite-event weight and of every deterministic
pushforward to a finite target in the same universe. These results compose
with the real/complex channel kernels and certified-classical APIs without
identifying output-row phase, basis statistics, finite distributions, rays,
or channels. Counterexamples and exhaustive allocation checks remain in the
non-root hierarchy audit.

Cross-model results use a separate source-to-target vocabulary with every map
visible. `ExactStateEncoding` is a left-inverse certificate on the encoder
image, `LosslessStateEncoding` additionally preserves an explicit total
weight, and the operator-embedding, state-intertwining, decoded-weight, and
decoded-distribution predicates retain their encoders, decoders, and
top-sector policies. They are deliberately not same-space equivalence
relations. For the four canonical state columns the library proves the
stronger concrete fact that the raw coordinate maps are real-linear
equivalences and their normalized representative maps are equivalences. Those
are representative-coordinate bijections, not ordinary ray, circuit, channel,
mixed-state, product-state, partial-trace, or all-effect equivalences.
The separate proof-bearing wrapper layer classifies exact rectangular matrix
action, Equation 63 reindexing, translated placed-gate and circuit evaluators,
one supplied legal schedule, the composed quaternion-to-real translation, and
conditional compilation. Its amplitude statements quantify raw coefficient
pairs, not normalized or product top states. Equation 63 is not a second
circuit translator; schedules are not selected or identified; and a supplied
`ExactGateCompiler` is not a compiler-existence, synthesis, approximation, or
runtime theorem. The decoded-outcome layer retains full one- or two-added-wire
target distributions until explicit decoders are applied; one-wire decoding
equals deterministic pushforward by `tailBits`, and composed decoding removes
the outer realification wire before the inner complexification wire. Raw
point-weight wrappers need no unitarity premise, whereas normalized
distribution, event, and deterministic-pushforward wrappers require locally
unitary circuits. Supplied schedules remain explicit. No result upgrades these
facts to product/mixed-state, partial-trace, channel/all-effect, randomized-
postprocessing, or resource semantics.

The circuit surface provides noncommutative-safe gate placement,
locality-certified chronological circuits, preparation of a known basis input
from the ground column, a fixed-value quaternionic order audit, and the
one-added-wire gate translations for both doubled matrix embeddings.  A
separate product-input diagnostic proves ray-level order dependence while all
computational-basis weights agree, deliberately separating state and
observable equality.  The whole-circuit layer proves corrected exact
complex-to-real and quaternion-to-complex simulations, their normalized
bottom-probability semantics and exact structural overhead, and the composed
quaternion-to-real corollary.  The ordering layer adds corrected Kronecker
interchange hypotheses, certified legal schedules, an explicit commuting-gate
independence theorem, scheduled exact simulation, and a disjoint locally
unitary witness whose two legal orders have different observable outcomes.
The resource layer gives support-certified depth, dense-description slot
counts, factorial unconstrained schedules, conditional exact primitive
compilation, and preservation under arbitrary finite events and deterministic
postprocessing, while keeping encoding, runtime, synthesis existence, and
complexity-class claims outside the unconditional API.
-/
