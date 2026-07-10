module

public import QuaternionicComputing.Circuit.Complexification
public import QuaternionicComputing.Circuit.Cost
public import QuaternionicComputing.State.Complexification
public import QuaternionicComputing.State.Unitary
public import QuaternionicComputing.Simulation.Basic

/-!
# Ordered quaternionic circuits simulated by complex circuits

This module maps every locality-certified quaternionic gate to its
one-added-wire complexification and lifts the gatewise denotation theorem
through the public chronological evaluator.  Operator embedding, state
evolution, observable preservation, and resource facts remain separate
theorems.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe v

/-- Translate a chronological quaternionic circuit gate by gate to complex matrices. -/
def complexifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) : OrderedCircuit ℂ (AddedWire W) :=
  c.map complexifyPlacedGate

@[simp]
theorem complexifyCircuit_nil {W : Type v} [Fintype W] :
    complexifyCircuit ([] : OrderedCircuit ℍ[ℝ] W) = [] :=
  rfl

@[simp]
theorem complexifyCircuit_cons {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) (c : OrderedCircuit ℍ[ℝ] W) :
    complexifyCircuit (g :: c) =
      complexifyPlacedGate g :: complexifyCircuit c :=
  rfl

/-- Paper Lemma 8, corrected to a typed wire-facing operator equality. -/
@[simp]
theorem eval_complexifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.eval (complexifyCircuit c) =
      wireComplexify (OrderedCircuit.eval c) := by
  exact OrderedCircuit.eval_map_of_denote_eq
    (wireComplexifyStarMonoidHom W).toMonoidHom complexifyPlacedGate
    complexifyPlacedGate_denote c

/-- Abstract gate count is exactly preserved by complexification. -/
@[simp]
theorem gateCount_complexifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.gateCount (complexifyCircuit c) =
      OrderedCircuit.gateCount c := by
  simp [complexifyCircuit]

/-- The target circuit has exactly one more global wire than the source. -/
theorem width_complexifyCircuit (W : Type v) [Fintype W] :
    Fintype.card (AddedWire W) = Fintype.card W + 1 :=
  card_addedWire W

/-- Every target gate comes from one source gate with exactly one more local wire. -/
theorem mem_complexifyCircuit_arity {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (k : PlacedGate ℂ (AddedWire W)) :
    k ∈ complexifyCircuit c ↔
      ∃ g, g ∈ c ∧ complexifyPlacedGate g = k ∧
        k.localArity = g.localArity + 1 := by
  exact OrderedCircuit.mem_map_arity_provenance complexifyPlacedGate
    localArity_complexifyPlacedGate c k

/-- A source arity bound `d` becomes the exact abstract bound `d+1`. -/
theorem arityBound_complexifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℍ[ℝ] W} {d : ℕ}
    (hc : c.ArityBound d) :
    (complexifyCircuit c).ArityBound (d + 1) := by
  exact OrderedCircuit.arityBound_map_add_one complexifyPlacedGate
    localArity_complexifyPlacedGate hc

/-- The corresponding `d+1` target bound also reflects the source bound. -/
theorem arityBound_complexifyCircuit_iff {W : Type v} [Fintype W]
    {c : OrderedCircuit ℍ[ℝ] W} {d : ℕ} :
    (complexifyCircuit c).ArityBound (d + 1) ↔ c.ArityBound d := by
  exact OrderedCircuit.arityBound_map_add_one_iff complexifyPlacedGate
    localArity_complexifyPlacedGate

/-- The target maximum local arity is at most the source maximum plus one. -/
theorem maxLocalArity_complexifyCircuit_le {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    (complexifyCircuit c).maxLocalArity ≤ c.maxLocalArity + 1 := by
  exact OrderedCircuit.maxLocalArity_map_le_add_one complexifyPlacedGate
    localArity_complexifyPlacedGate c

/-- A nonempty circuit's maximum local arity increases by exactly one. -/
theorem maxLocalArity_complexifyCircuit_of_nonempty
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W} (hc : c ≠ []) :
    (complexifyCircuit c).maxLocalArity = c.maxLocalArity + 1 := by
  exact OrderedCircuit.maxLocalArity_map_eq_add_one_of_nonempty
    complexifyPlacedGate localArity_complexifyPlacedGate hc

/-- Local unitarity is preserved gatewise by circuit complexification. -/
theorem isLocallyUnitary_complexifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℍ[ℝ] W} (hc : c.IsLocallyUnitary) :
    (complexifyCircuit c).IsLocallyUnitary := by
  intro g hg
  simp only [complexifyCircuit, List.mem_map] at hg
  rcases hg with ⟨source, hsource, rfl⟩
  exact isLocallyUnitary_complexifyPlacedGate source (hc source hsource)

/-- The translated whole-circuit operator is unitary whenever every source gate is. -/
theorem eval_complexifyCircuit_mem_unitary {W : Type v} [Fintype W]
    {c : OrderedCircuit ℍ[ℝ] W} (hc : c.IsLocallyUnitary) :
    OrderedCircuit.eval (complexifyCircuit c) ∈
      unitary (Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℂ) :=
  OrderedCircuit.eval_mem_unitary (isLocallyUnitary_complexifyCircuit hc)

/-! ## Circuit-facing state columns -/

/-- The first complex state column on the explicit added-wire basis. -/
def wireComplexColumn0 {W : Type v} (psi : BitBasis W → ℍ[ℝ]) :
    BitBasis (AddedWire W) → ℂ :=
  transportAddedColumn (complexColumn0 psi)

/-- The second complex state column on the explicit added-wire basis. -/
def wireComplexColumn1 {W : Type v} (psi : BitBasis W → ℍ[ℝ]) :
    BitBasis (AddedWire W) → ℂ :=
  transportAddedColumn (complexColumn1 psi)

/-- An arbitrary complex top-sector combination on the explicit added-wire basis. -/
def wireComplexTopCombination {W : Type v} (a b : ℂ)
    (psi : BitBasis W → ℍ[ℝ]) : BitBasis (AddedWire W) → ℂ :=
  transportAddedColumn (complexTopCombination a b psi)

/-- The first canonical wire-facing embedding of a normalized quaternionic state. -/
def wireComplexColumn0State {W : Type v} [Fintype W]
    (psi : QuaternionState (BitBasis W)) :
    ComplexState (BitBasis (AddedWire W)) :=
  transportAddedState (complexColumn0State psi)

/-- The second canonical wire-facing embedding of a normalized quaternionic state. -/
def wireComplexColumn1State {W : Type v} [Fintype W]
    (psi : QuaternionState (BitBasis W)) :
    ComplexState (BitBasis (AddedWire W)) :=
  transportAddedState (complexColumn1State psi)

/-- Every normalized pure top qubit gives a normalized wire-facing target state. -/
def wireComplexTopState {W : Type v} [Fintype W]
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    ComplexState (BitBasis (AddedWire W)) :=
  transportAddedState (complexTopState top psi)

@[simp]
theorem wireComplexColumn0State_apply {W : Type v} [Fintype W]
    (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire W)) :
    wireComplexColumn0State psi x = wireComplexColumn0 psi x :=
  rfl

@[simp]
theorem wireComplexColumn1State_apply {W : Type v} [Fintype W]
    (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire W)) :
    wireComplexColumn1State psi x = wireComplexColumn1 psi x :=
  rfl

@[simp]
theorem wireComplexTopState_apply {W : Type v} [Fintype W]
    (top : Qubit) (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire W)) :
    wireComplexTopState top psi x =
      wireComplexTopCombination (top false) (top true) psi x :=
  rfl

/-- Wire-facing complexification intertwines the first state column. -/
theorem wireComplexify_mulVec_wireComplexColumn0
    {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ])
    (psi : BitBasis W → ℍ[ℝ]) :
    wireComplexify A *ᵥ wireComplexColumn0 psi =
      wireComplexColumn0 (A *ᵥ psi) := by
  rw [wireComplexify, wireComplexColumn0,
    reindex_mulVec_transportAddedColumn,
    complexify_mulVec_complexColumn0]
  rfl

/-- Wire-facing complexification intertwines the second state column. -/
theorem wireComplexify_mulVec_wireComplexColumn1
    {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ])
    (psi : BitBasis W → ℍ[ℝ]) :
    wireComplexify A *ᵥ wireComplexColumn1 psi =
      wireComplexColumn1 (A *ᵥ psi) := by
  rw [wireComplexify, wireComplexColumn1,
    reindex_mulVec_transportAddedColumn,
    complexify_mulVec_complexColumn1]
  rfl

/-- Wire-facing complexification intertwines every complex top-state combination. -/
theorem wireComplexify_mulVec_wireComplexTopCombination
    {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) (a b : ℂ)
    (psi : BitBasis W → ℍ[ℝ]) :
    wireComplexify A *ᵥ wireComplexTopCombination a b psi =
      wireComplexTopCombination a b (A *ᵥ psi) := by
  rw [wireComplexify, wireComplexTopCombination,
    reindex_mulVec_transportAddedColumn,
    complexify_mulVec_complexTopCombination]
  rfl

/-- Sum complex target weights over the actual false/true values of the added wire. -/
def wireComplexBottomWeight {W : Type v}
    (phi : BitBasis (AddedWire W) → ℂ) (x : BitBasis W) : ℝ :=
  addedWireBottomWeight complexWeight phi x

/-- The first wire-facing column preserves every bottom basis weight. -/
@[simp]
theorem wireComplexColumn0_bottomWeight {W : Type v}
    (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight (wireComplexColumn0 psi) x =
      quaternionBasisWeight psi x := by
  change bottomComplexWeight (complexColumn0 psi) x =
    quaternionBasisWeight psi x
  exact complexColumn0_bottomWeight psi x

/-- The second wire-facing column preserves every bottom basis weight. -/
@[simp]
theorem wireComplexColumn1_bottomWeight {W : Type v}
    (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight (wireComplexColumn1 psi) x =
      quaternionBasisWeight psi x := by
  change bottomComplexWeight (complexColumn1 psi) x =
    quaternionBasisWeight psi x
  exact complexColumn1_bottomWeight psi x

/-- Every normalized pure top qubit preserves every bottom basis weight. -/
theorem wireComplexTopCombination_bottomWeight_of_qubit {W : Type v}
    (top : Qubit) (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight
        (wireComplexTopCombination (top false) (top true) psi) x =
      quaternionBasisWeight psi x := by
  change
    bottomComplexWeight
        (complexTopCombination (top false) (top true) psi) x =
      quaternionBasisWeight psi x
  exact complexTopCombination_bottomWeight_of_qubit top psi x

/-! ## Whole-circuit state evolution and observables -/

/-- The translated circuit intertwines the first canonical state column. -/
theorem eval_complexifyCircuit_mulVec_wireComplexColumn0
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W)
    (psi : BitBasis W → ℍ[ℝ]) :
    OrderedCircuit.eval (complexifyCircuit c) *ᵥ wireComplexColumn0 psi =
      wireComplexColumn0 (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_complexifyCircuit, wireComplexify_mulVec_wireComplexColumn0]

/-- The translated circuit intertwines the second canonical state column. -/
theorem eval_complexifyCircuit_mulVec_wireComplexColumn1
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W)
    (psi : BitBasis W → ℍ[ℝ]) :
    OrderedCircuit.eval (complexifyCircuit c) *ᵥ wireComplexColumn1 psi =
      wireComplexColumn1 (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_complexifyCircuit, wireComplexify_mulVec_wireComplexColumn1]

/-- The translated circuit intertwines every normalized or unnormalized top combination. -/
theorem eval_complexifyCircuit_mulVec_wireComplexTopCombination
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) (a b : ℂ)
    (psi : BitBasis W → ℍ[ℝ]) :
    OrderedCircuit.eval (complexifyCircuit c) *ᵥ
        wireComplexTopCombination a b psi =
      wireComplexTopCombination a b (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_complexifyCircuit,
    wireComplexify_mulVec_wireComplexTopCombination]

/-- Corrected observable part of Theorem 4 for the first canonical top state. -/
theorem complexifyCircuit_bottomWeight_column0
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W)
    (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight
        (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
          wireComplexColumn0 psi) x =
      quaternionBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_complexifyCircuit_mulVec_wireComplexColumn0,
    wireComplexColumn0_bottomWeight]

/-- Corrected observable part of Theorem 4 for the second canonical top state. -/
theorem complexifyCircuit_bottomWeight_column1
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W)
    (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight
        (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
          wireComplexColumn1 psi) x =
      quaternionBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_complexifyCircuit_mulVec_wireComplexColumn1,
    wireComplexColumn1_bottomWeight]

/-- Corrected observable part of Theorem 4 for every normalized pure top qubit. -/
theorem complexifyCircuit_bottomWeight_of_qubit
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) (top : Qubit)
    (psi : BitBasis W → ℍ[ℝ]) (x : BitBasis W) :
    wireComplexBottomWeight
        (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
          wireComplexTopCombination (top false) (top true) psi) x =
      quaternionBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_complexifyCircuit_mulVec_wireComplexTopCombination]
  exact wireComplexTopCombination_bottomWeight_of_qubit top _ x

/-! ## Normalized outputs and corrected Theorem 4 -/

/-- The normalized output of the source quaternionic circuit. -/
def quaternionCircuitOutput {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (psi : QuaternionState (BitBasis W)) : QuaternionState (BitBasis W) :=
  QuaternionState.evolveUnitary psi (OrderedCircuit.eval c)
    (OrderedCircuit.eval_mem_unitary hc)

/-- The normalized complex output produced from a normalized pure top qubit. -/
def complexifyCircuitOutput {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary) (top : Qubit)
    (psi : QuaternionState (BitBasis W)) :
    ComplexState (BitBasis (AddedWire W)) :=
  ComplexState.evolveUnitary (wireComplexTopState top psi)
    (OrderedCircuit.eval (complexifyCircuit c))
    (eval_complexifyCircuit_mem_unitary hc)

@[simp]
theorem quaternionCircuitOutput_apply {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary)
    (psi : QuaternionState (BitBasis W)) (x : BitBasis W) :
    quaternionCircuitOutput c hc psi x =
      (OrderedCircuit.eval c *ᵥ (psi : BitBasis W → ℍ[ℝ])) x :=
  rfl

@[simp]
theorem complexifyCircuitOutput_apply {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary) (top : Qubit)
    (psi : QuaternionState (BitBasis W))
    (x : BitBasis (AddedWire W)) :
    complexifyCircuitOutput c hc top psi x =
      wireComplexTopCombination (top false) (top true)
        (OrderedCircuit.eval c *ᵥ (psi : BitBasis W → ℍ[ℝ])) x := by
  change
    (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
      wireComplexTopCombination (top false) (top true) psi) x = _
  exact congrFun
    (eval_complexifyCircuit_mulVec_wireComplexTopCombination
      c (top false) (top true) psi) x

/--
For normalized input and locally unitary gates, the equal bottom weights are
actual probabilities: both source and target outputs are normalized states.
-/
theorem complexifyCircuitOutput_bottomProbability
    {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) (hc : c.IsLocallyUnitary) (top : Qubit)
    (psi : QuaternionState (BitBasis W)) (x : BitBasis W) :
    wireComplexBottomWeight (complexifyCircuitOutput c hc top psi) x =
      quaternionBasisWeight (quaternionCircuitOutput c hc psi) x := by
  change
    wireComplexBottomWeight
        (OrderedCircuit.eval (complexifyCircuit c) *ᵥ
          wireComplexTopCombination (top false) (top true) psi) x =
      quaternionBasisWeight (OrderedCircuit.eval c *ᵥ psi) x
  exact complexifyCircuit_bottomWeight_of_qubit c top psi x

/--
Corrected constructive form of paper Theorem 4 in the exact abstract-matrix
model.  The conclusions separately expose operator embedding, gate count,
width, local-arity bound, and equality of normalized bottom probabilities.
-/
theorem quaternionToComplex_exactSimulation
    {W : Type v} [Fintype W] {c : OrderedCircuit ℍ[ℝ] W} {d : ℕ}
    (hc : c.IsLocallyUnitary) (hArity : c.ArityBound d)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    OrderedCircuit.eval (complexifyCircuit c) =
        wireComplexify (OrderedCircuit.eval c) ∧
      OrderedCircuit.gateCount (complexifyCircuit c) =
        OrderedCircuit.gateCount c ∧
      Fintype.card (AddedWire W) = Fintype.card W + 1 ∧
      (complexifyCircuit c).ArityBound (d + 1) ∧
      ∀ x : BitBasis W,
        wireComplexBottomWeight (complexifyCircuitOutput c hc top psi) x =
          quaternionBasisWeight (quaternionCircuitOutput c hc psi) x := by
  refine ⟨eval_complexifyCircuit c, gateCount_complexifyCircuit c,
    card_addedWire W, arityBound_complexifyCircuit hArity, ?_⟩
  exact complexifyCircuitOutput_bottomProbability c hc top psi

end QuaternionicComputing.Simulation
