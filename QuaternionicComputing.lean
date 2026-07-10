module

public import QuaternionicComputing.Scalar.Phase
public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification
public import QuaternionicComputing.Circuit.OrderSanity
public import QuaternionicComputing.Circuit.Realification
public import QuaternionicComputing.Circuit.Complexification
public import QuaternionicComputing.Matrix.KroneckerCommute
public import QuaternionicComputing.Circuit.Ordering
public import QuaternionicComputing.Circuit.ScheduleCount
public import QuaternionicComputing.Simulation.QuaternionToReal
public import QuaternionicComputing.Simulation.Examples
public import QuaternionicComputing.Simulation.Scheduled
public import QuaternionicComputing.Simulation.OrderingWitness
public import QuaternionicComputing.Simulation.CompiledResources
public import QuaternionicComputing.Simulation.Postprocessing

/-!
# Quaternionic Computing

Public root module for the verified formalization of Fernandez and
Schneeberger's *Quaternionic Computing*.

The current public surface includes the quaternion component algebra, the
explicit correction of the paper's left-phase convention, both finite-matrix
embeddings, their injective unitary/group consequences, the realification
determinant identity, the precisely bounded quaternion determinant result,
normalized finite states, corrected right phase, and both state-column
measurement-preservation APIs.  It also exports noncommutative-safe gate
placement, locality-certified chronological circuits, a fixed-value
quaternionic order audit, and the one-added-wire gate translations for both
matrix embeddings.  The whole-circuit layer proves corrected exact
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
