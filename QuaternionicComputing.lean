module

public import QuaternionicComputing.Scalar.Phase
public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.Matrix.QuaternionRealificationUnitary
public import QuaternionicComputing.Matrix.ProperImage
public import QuaternionicComputing.State.ComplexPhase
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification
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
and quaternionic unitaries embed into `SO(4N)` only through its proper image.
Explicit `SO(4)`/`SU(4)` matrices certify the corrected non-surjectivity
claims.  The library also exports the embedding determinant results,
normalized finite states, both state-column measurement-preservation APIs,
and a checked non-product realification example.

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
