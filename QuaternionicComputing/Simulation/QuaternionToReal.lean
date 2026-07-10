module

public import QuaternionicComputing.Simulation.QuaternionToComplex
public import QuaternionicComputing.Simulation.ComplexToReal

/-!
# Quaternionic circuits simulated by real circuits

This module proves the corrected form of the paper's Corollary 1 by visibly
composing the quaternion-to-complex and complex-to-real simulations.  Every
definition and proof factors through `complexifyCircuit` and then
`realifyCircuit`; no direct quaternion-to-real gate or matrix embedding is
introduced.

The composite simulation uses two shared distinguished wires.  The inner
wire carries the complex top qubit from quaternionic complexification, and
the outer wire carries the real top rebit from complex realification.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe v

/--
Translate a quaternionic circuit first to complex gates and then realify that
entire translated circuit.
-/
def quaternionToRealCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit ℝ (AddedWire (AddedWire W)) :=
  realifyCircuit (complexifyCircuit c)

@[simp]
theorem quaternionToRealCircuit_nil {W : Type v} [Fintype W] :
    quaternionToRealCircuit ([] : OrderedCircuit ℍ[ℝ] W) = [] :=
  rfl

/-- The composite circuit operator is the composition of the two public embeddings. -/
@[simp]
theorem eval_quaternionToRealCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.eval (quaternionToRealCircuit c) =
      wireRealify (wireComplexify (OrderedCircuit.eval c)) := by
  rw [quaternionToRealCircuit, eval_realifyCircuit, eval_complexifyCircuit]

/-- Local unitarity survives both gatewise translations. -/
theorem isLocallyUnitary_quaternionToRealCircuit
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W}
    (hc : c.IsLocallyUnitary) :
    (quaternionToRealCircuit c).IsLocallyUnitary :=
  isLocallyUnitary_realifyCircuit (isLocallyUnitary_complexifyCircuit hc)

/-- The composed real circuit operator is unitary when every source gate is local-unitary. -/
theorem eval_quaternionToRealCircuit_mem_unitary
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W}
    (hc : c.IsLocallyUnitary) :
    OrderedCircuit.eval (quaternionToRealCircuit c) ∈
      unitary
        (Matrix (BitBasis (AddedWire (AddedWire W)))
          (BitBasis (AddedWire (AddedWire W))) ℝ) :=
  OrderedCircuit.eval_mem_unitary
    (isLocallyUnitary_quaternionToRealCircuit hc)

/-- Both translations preserve abstract gate count, so their composite does too. -/
@[simp]
theorem gateCount_quaternionToRealCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.gateCount (quaternionToRealCircuit c) =
      OrderedCircuit.gateCount c := by
  simp [quaternionToRealCircuit]

/-- The twice-translated circuit has exactly two more global wires. -/
theorem width_quaternionToRealCircuit (W : Type v) [Fintype W] :
    Fintype.card (AddedWire (AddedWire W)) = Fintype.card W + 2 := by
  rw [card_addedWire, card_addedWire]

/-- A source local-arity bound `d` becomes the composed bound `d + 2`. -/
theorem arityBound_quaternionToRealCircuit
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W} {d : ℕ}
    (hc : c.ArityBound d) :
    (quaternionToRealCircuit c).ArityBound (d + 2) := by
  have hComplex := arityBound_complexifyCircuit hc
  have hReal := arityBound_realifyCircuit hComplex
  simpa [quaternionToRealCircuit, Nat.add_assoc] using hReal

/-- The composite maximum local arity is universally at most the source maximum plus two. -/
theorem maxLocalArity_quaternionToRealCircuit_le
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) :
    (quaternionToRealCircuit c).maxLocalArity ≤ c.maxLocalArity + 2 := by
  change (realifyCircuit (complexifyCircuit c)).maxLocalArity ≤
    c.maxLocalArity + 2
  calc
    (realifyCircuit (complexifyCircuit c)).maxLocalArity ≤
        (complexifyCircuit c).maxLocalArity + 1 :=
      maxLocalArity_realifyCircuit_le (complexifyCircuit c)
    _ ≤ (c.maxLocalArity + 1) + 1 :=
      Nat.add_le_add_right (maxLocalArity_complexifyCircuit_le c) 1
    _ = c.maxLocalArity + 2 := by omega

/-- Every nonempty source circuit has composite maximum local arity exactly two larger. -/
theorem maxLocalArity_quaternionToRealCircuit_of_nonempty
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W}
    (hc : c ≠ []) :
    (quaternionToRealCircuit c).maxLocalArity = c.maxLocalArity + 2 := by
  have hcComplex : complexifyCircuit c ≠ [] := by
    simpa [complexifyCircuit] using hc
  change (realifyCircuit (complexifyCircuit c)).maxLocalArity =
    c.maxLocalArity + 2
  rw [maxLocalArity_realifyCircuit_of_nonempty hcComplex,
    maxLocalArity_complexifyCircuit_of_nonempty hc]

/-! ## Nested normalized states and the two-wire observable -/

/--
The normalized real initial state obtained by first adjoining the complex top
qubit and then adjoining the real top rebit.
-/
def quaternionToRealInitialState {W : Type v} [Fintype W]
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    RealState (BitBasis (AddedWire (AddedWire W))) :=
  wireRealTopState realTop (wireComplexTopState complexTop psi)

/--
The normalized output of the literally composed translated circuit, starting
from the nested normalized initial state.
-/
def quaternionToRealCircuitOutput
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    RealState (BitBasis (AddedWire (AddedWire W))) :=
  realifyCircuitOutput (complexifyCircuit c)
    (isLocallyUnitary_complexifyCircuit hc) realTop
    (wireComplexTopState complexTop psi)

/-- The composed normalized output is evolution of the nested normalized initial state. -/
@[simp]
theorem quaternionToRealCircuitOutput_apply
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire (AddedWire W))) :
    quaternionToRealCircuitOutput c hc complexTop realTop psi x =
      (OrderedCircuit.eval (quaternionToRealCircuit c) *ᵥ
        (quaternionToRealInitialState complexTop realTop psi :
          BitBasis (AddedWire (AddedWire W)) → ℝ)) x :=
  rfl

/--
The composed real output is the nested state encoding of the evolved
quaternionic source.  This is the state-intertwining content of the composed
corollary, not merely an unfolding of `quaternionToRealCircuitOutput`.
-/
theorem quaternionToRealCircuitOutput_nestedEncoding_apply
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire (AddedWire W))) :
    quaternionToRealCircuitOutput c hc complexTop realTop psi x =
      wireRealTopCombination (realTop false) (realTop true)
        (wireComplexTopCombination (complexTop false) (complexTop true)
          (OrderedCircuit.eval c *ᵥ
            (psi : BitBasis W → ℍ[ℝ]))) x := by
  rw [quaternionToRealCircuitOutput, realifyCircuitOutput_apply]
  exact congrFun
    (congrArg (wireRealTopCombination (realTop false) (realTop true))
      (eval_complexifyCircuit_mulVec_wireComplexTopCombination
        c (complexTop false) (complexTop true) psi)) x

/--
Bottom real weight after two added wires: first sum the realification weight
over the outer real top wire, then sum those results over the false/true
assignments of the inner complex top wire.
-/
def wireQuaternionToRealBottomWeight {W : Type v}
    (phi : BitBasis (AddedWire (AddedWire W)) → ℝ)
    (x : BitBasis W) : ℝ :=
  wireRealBottomWeight phi (addedBasisEquiv W (Sum.inl x)) +
    wireRealBottomWeight phi (addedBasisEquiv W (Sum.inr x))

@[simp]
theorem wireQuaternionToRealBottomWeight_apply {W : Type v}
    (phi : BitBasis (AddedWire (AddedWire W)) → ℝ)
    (x : BitBasis W) :
    wireQuaternionToRealBottomWeight phi x =
      wireRealBottomWeight phi (addedBasisEquiv W (Sum.inl x)) +
        wireRealBottomWeight phi (addedBasisEquiv W (Sum.inr x)) :=
  rfl

/--
The normalized twice-translated real output has the same probability on every
original bottom basis assignment as the normalized quaternionic source
output.
-/
theorem quaternionToRealCircuitOutput_bottomProbability
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) (x : BitBasis W) :
    wireQuaternionToRealBottomWeight
        (quaternionToRealCircuitOutput c hc complexTop realTop psi).1 x =
      quaternionBasisWeight (quaternionCircuitOutput c hc psi) x := by
  let hcComplex := isLocallyUnitary_complexifyCircuit hc
  simp only [quaternionToRealCircuitOutput]
  rw [wireQuaternionToRealBottomWeight,
    realifyCircuitOutput_bottomProbability
      (complexifyCircuit c) hcComplex realTop
      (wireComplexTopState complexTop psi)
      (addedBasisEquiv W (Sum.inl x)),
    realifyCircuitOutput_bottomProbability
      (complexifyCircuit c) hcComplex realTop
      (wireComplexTopState complexTop psi)
      (addedBasisEquiv W (Sum.inr x))]
  change
    wireComplexBottomWeight (complexifyCircuitOutput c hc complexTop psi) x =
      quaternionBasisWeight (quaternionCircuitOutput c hc psi) x
  exact complexifyCircuitOutput_bottomProbability c hc complexTop psi x

/--
Corrected constructive form of paper Corollary 1 in the exact abstract-matrix
model.  The two primary simulations remain visible in every conclusion.
-/
theorem quaternionToReal_exactSimulation
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W} {d : ℕ}
    (hc : c.IsLocallyUnitary) (hArity : c.ArityBound d)
    (complexTop : Qubit) (realTop : Rebit)
    (psi : QuaternionState (BitBasis W)) :
    OrderedCircuit.eval (quaternionToRealCircuit c) =
        wireRealify (wireComplexify (OrderedCircuit.eval c)) ∧
      OrderedCircuit.gateCount (quaternionToRealCircuit c) =
        OrderedCircuit.gateCount c ∧
      Fintype.card (AddedWire (AddedWire W)) = Fintype.card W + 2 ∧
      (quaternionToRealCircuit c).ArityBound (d + 2) ∧
      ∀ x : BitBasis W,
        wireQuaternionToRealBottomWeight
            (quaternionToRealCircuitOutput c hc complexTop realTop psi).1 x =
          quaternionBasisWeight (quaternionCircuitOutput c hc psi) x := by
  refine ⟨eval_quaternionToRealCircuit c,
    gateCount_quaternionToRealCircuit c,
    width_quaternionToRealCircuit W,
    arityBound_quaternionToRealCircuit hArity, ?_⟩
  exact quaternionToRealCircuitOutput_bottomProbability
    c hc complexTop realTop psi

end QuaternionicComputing.Simulation
