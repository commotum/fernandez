module

public import QuaternionicComputing.Scalar.Phase
public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.State.Complexification
public import QuaternionicComputing.Circuit.OrderSanity
public import QuaternionicComputing.Circuit.Realification
public import QuaternionicComputing.Circuit.Complexification

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
matrix embeddings.
-/
