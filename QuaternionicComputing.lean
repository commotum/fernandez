module

public import QuaternionicComputing.Scalar.Phase
public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.Matrix.QuaternionRealificationUnitary
public import QuaternionicComputing.Matrix.ProperImage
public import QuaternionicComputing.State.ComplexPhase
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification
public import QuaternionicComputing.State.Ray
public import QuaternionicComputing.Semantics.Measurement
public import QuaternionicComputing.Semantics.StatePhase
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionKernel
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
matrix/circuit action and normalized unitary evolution.  Quotient state spaces
are now exported as `RealRay`, `ComplexRay`, and `QuaternionRay`; descended
ray dynamics and outcome maps remain a separate layer.

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
