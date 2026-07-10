module

public import QuaternionicComputing.Circuit.Realification
public import QuaternionicComputing.Circuit.Cost
public import QuaternionicComputing.State.Realification
public import QuaternionicComputing.Simulation.Basic

/-!
# Ordered complex circuits simulated by real circuits

This module maps every locality-certified complex gate to its one-added-wire
realification and lifts the gatewise denotation theorem through the public
chronological evaluator.  Operator embedding, state evolution, observable
preservation, and resource facts are kept as separate theorems.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe v

/-- Translate a chronological complex circuit gate by gate to real matrices. -/
def realifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) : OrderedCircuit ℝ (AddedWire W) :=
  c.map realifyPlacedGate

@[simp]
theorem realifyCircuit_nil {W : Type v} [Fintype W] :
    realifyCircuit ([] : OrderedCircuit ℂ W) = [] :=
  rfl

@[simp]
theorem realifyCircuit_cons {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) (c : OrderedCircuit ℂ W) :
    realifyCircuit (g :: c) = realifyPlacedGate g :: realifyCircuit c :=
  rfl

/-- Paper Lemma 3, corrected to a typed wire-facing operator equality. -/
@[simp]
theorem eval_realifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) :
    OrderedCircuit.eval (realifyCircuit c) =
      wireRealify (OrderedCircuit.eval c) := by
  exact OrderedCircuit.eval_map_of_denote_eq
    (wireRealifyStarMonoidHom W).toMonoidHom realifyPlacedGate
    realifyPlacedGate_denote c

/-- Abstract gate count is exactly preserved by realification. -/
@[simp]
theorem gateCount_realifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) :
    OrderedCircuit.gateCount (realifyCircuit c) =
      OrderedCircuit.gateCount c := by
  simp [realifyCircuit]

/-- The target circuit has exactly one more global wire than the source. -/
theorem width_realifyCircuit (W : Type v) [Fintype W] :
    Fintype.card (AddedWire W) = Fintype.card W + 1 :=
  card_addedWire W

/-- Every target gate comes from one source gate with exactly one more local wire. -/
theorem mem_realifyCircuit_arity {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) (k : PlacedGate ℝ (AddedWire W)) :
    k ∈ realifyCircuit c ↔
      ∃ g, g ∈ c ∧ realifyPlacedGate g = k ∧
        k.localArity = g.localArity + 1 := by
  exact OrderedCircuit.mem_map_arity_provenance realifyPlacedGate
    localArity_realifyPlacedGate c k

/-- A source arity bound `d` becomes the exact abstract bound `d+1`. -/
theorem arityBound_realifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℂ W} {d : ℕ}
    (hc : c.ArityBound d) :
    (realifyCircuit c).ArityBound (d + 1) := by
  exact OrderedCircuit.arityBound_map_add_one realifyPlacedGate
    localArity_realifyPlacedGate hc

/-- The corresponding `d+1` target bound also reflects the source bound. -/
theorem arityBound_realifyCircuit_iff {W : Type v} [Fintype W]
    {c : OrderedCircuit ℂ W} {d : ℕ} :
    (realifyCircuit c).ArityBound (d + 1) ↔ c.ArityBound d := by
  exact OrderedCircuit.arityBound_map_add_one_iff realifyPlacedGate
    localArity_realifyPlacedGate

/-- The target maximum local arity is at most the source maximum plus one. -/
theorem maxLocalArity_realifyCircuit_le {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) :
    (realifyCircuit c).maxLocalArity ≤ c.maxLocalArity + 1 := by
  exact OrderedCircuit.maxLocalArity_map_le_add_one realifyPlacedGate
    localArity_realifyPlacedGate c

/-- A nonempty circuit's maximum local arity increases by exactly one. -/
theorem maxLocalArity_realifyCircuit_of_nonempty
    {W : Type v} [Fintype W] {c : OrderedCircuit ℂ W} (hc : c ≠ []) :
    (realifyCircuit c).maxLocalArity = c.maxLocalArity + 1 := by
  exact OrderedCircuit.maxLocalArity_map_eq_add_one_of_nonempty
    realifyPlacedGate localArity_realifyPlacedGate hc

/-- Local unitarity is preserved gatewise by circuit realification. -/
theorem isLocallyUnitary_realifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℂ W} (hc : c.IsLocallyUnitary) :
    (realifyCircuit c).IsLocallyUnitary := by
  intro g hg
  simp only [realifyCircuit, List.mem_map] at hg
  rcases hg with ⟨source, hsource, rfl⟩
  exact isLocallyUnitary_realifyPlacedGate source (hc source hsource)

/-- The translated whole-circuit operator is unitary whenever every source gate is. -/
theorem eval_realifyCircuit_mem_unitary {W : Type v} [Fintype W]
    {c : OrderedCircuit ℂ W} (hc : c.IsLocallyUnitary) :
    OrderedCircuit.eval (realifyCircuit c) ∈
      unitary (Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℝ) :=
  OrderedCircuit.eval_mem_unitary (isLocallyUnitary_realifyCircuit hc)

/-! ## Circuit-facing state columns -/

/-- The first real state column on the explicit added-wire basis. -/
def wireRealColumn0 {W : Type v} (psi : BitBasis W → ℂ) :
    BitBasis (AddedWire W) → ℝ :=
  transportAddedColumn (realColumn0 psi)

/-- The second real state column on the explicit added-wire basis. -/
def wireRealColumn1 {W : Type v} (psi : BitBasis W → ℂ) :
    BitBasis (AddedWire W) → ℝ :=
  transportAddedColumn (realColumn1 psi)

/-- An arbitrary real top-sector combination on the explicit added-wire basis. -/
def wireRealTopCombination {W : Type v} (a b : ℝ)
    (psi : BitBasis W → ℂ) : BitBasis (AddedWire W) → ℝ :=
  transportAddedColumn (realTopCombination a b psi)

/-- The first canonical wire-facing embedding of a normalized complex state. -/
def wireRealColumn0State {W : Type v} [Fintype W]
    (psi : ComplexState (BitBasis W)) : RealState (BitBasis (AddedWire W)) :=
  transportAddedState (realColumn0State psi)

/-- The second canonical wire-facing embedding of a normalized complex state. -/
def wireRealColumn1State {W : Type v} [Fintype W]
    (psi : ComplexState (BitBasis W)) : RealState (BitBasis (AddedWire W)) :=
  transportAddedState (realColumn1State psi)

/-- Every normalized pure top rebit gives a normalized wire-facing target state. -/
def wireRealTopState {W : Type v} [Fintype W]
    (top : Rebit) (psi : ComplexState (BitBasis W)) :
    RealState (BitBasis (AddedWire W)) :=
  transportAddedState (realTopState top psi)

@[simp]
theorem wireRealColumn0State_apply {W : Type v} [Fintype W]
    (psi : ComplexState (BitBasis W)) (x : BitBasis (AddedWire W)) :
    wireRealColumn0State psi x = wireRealColumn0 psi x :=
  rfl

@[simp]
theorem wireRealColumn1State_apply {W : Type v} [Fintype W]
    (psi : ComplexState (BitBasis W)) (x : BitBasis (AddedWire W)) :
    wireRealColumn1State psi x = wireRealColumn1 psi x :=
  rfl

@[simp]
theorem wireRealTopState_apply {W : Type v} [Fintype W]
    (top : Rebit) (psi : ComplexState (BitBasis W))
    (x : BitBasis (AddedWire W)) :
    wireRealTopState top psi x =
      wireRealTopCombination (top false) (top true) psi x :=
  rfl

/-- Wire-facing realification intertwines the first state column. -/
theorem wireRealify_mulVec_wireRealColumn0 {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) (psi : BitBasis W → ℂ) :
    wireRealify A *ᵥ wireRealColumn0 psi =
      wireRealColumn0 (A *ᵥ psi) := by
  rw [wireRealify, wireRealColumn0, reindex_mulVec_transportAddedColumn,
    realify_mulVec_realColumn0]
  rfl

/-- Wire-facing realification intertwines the second state column. -/
theorem wireRealify_mulVec_wireRealColumn1 {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) (psi : BitBasis W → ℂ) :
    wireRealify A *ᵥ wireRealColumn1 psi =
      wireRealColumn1 (A *ᵥ psi) := by
  rw [wireRealify, wireRealColumn1, reindex_mulVec_transportAddedColumn,
    realify_mulVec_realColumn1]
  rfl

/-- Wire-facing realification intertwines every real top-state combination. -/
theorem wireRealify_mulVec_wireRealTopCombination
    {W : Type v} [Finite W]
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) (a b : ℝ)
    (psi : BitBasis W → ℂ) :
    wireRealify A *ᵥ wireRealTopCombination a b psi =
      wireRealTopCombination a b (A *ᵥ psi) := by
  rw [wireRealify, wireRealTopCombination,
    reindex_mulVec_transportAddedColumn,
    realify_mulVec_realTopCombination]
  rfl

/-- Sum real target weights over the actual false/true values of the added wire. -/
def wireRealBottomWeight {W : Type v}
    (phi : BitBasis (AddedWire W) → ℝ) (x : BitBasis W) : ℝ :=
  addedWireBottomWeight realWeight phi x

/-- The first wire-facing column preserves every bottom basis weight. -/
@[simp]
theorem wireRealColumn0_bottomWeight {W : Type v}
    (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight (wireRealColumn0 psi) x =
      complexBasisWeight psi x := by
  change bottomRealWeight (realColumn0 psi) x = complexBasisWeight psi x
  exact realColumn0_bottomWeight psi x

/-- The second wire-facing column preserves every bottom basis weight. -/
@[simp]
theorem wireRealColumn1_bottomWeight {W : Type v}
    (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight (wireRealColumn1 psi) x =
      complexBasisWeight psi x := by
  change bottomRealWeight (realColumn1 psi) x = complexBasisWeight psi x
  exact realColumn1_bottomWeight psi x

/-- Every normalized pure top rebit preserves every bottom basis weight. -/
theorem wireRealTopCombination_bottomWeight_of_rebit {W : Type v}
    (top : Rebit) (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight
        (wireRealTopCombination (top false) (top true) psi) x =
      complexBasisWeight psi x := by
  change
    bottomRealWeight
        (realTopCombination (top false) (top true) psi) x =
      complexBasisWeight psi x
  exact realTopCombination_bottomWeight_of_rebit top psi x

/-! ## Whole-circuit state evolution and observables -/

/-- The translated circuit intertwines the first canonical state column. -/
theorem eval_realifyCircuit_mulVec_wireRealColumn0
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W)
    (psi : BitBasis W → ℂ) :
    OrderedCircuit.eval (realifyCircuit c) *ᵥ wireRealColumn0 psi =
      wireRealColumn0 (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_realifyCircuit, wireRealify_mulVec_wireRealColumn0]

/-- The translated circuit intertwines the second canonical state column. -/
theorem eval_realifyCircuit_mulVec_wireRealColumn1
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W)
    (psi : BitBasis W → ℂ) :
    OrderedCircuit.eval (realifyCircuit c) *ᵥ wireRealColumn1 psi =
      wireRealColumn1 (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_realifyCircuit, wireRealify_mulVec_wireRealColumn1]

/-- The translated circuit intertwines every normalized or unnormalized top combination. -/
theorem eval_realifyCircuit_mulVec_wireRealTopCombination
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W) (a b : ℝ)
    (psi : BitBasis W → ℂ) :
    OrderedCircuit.eval (realifyCircuit c) *ᵥ
        wireRealTopCombination a b psi =
      wireRealTopCombination a b (OrderedCircuit.eval c *ᵥ psi) := by
  rw [eval_realifyCircuit, wireRealify_mulVec_wireRealTopCombination]

/-- Corrected observable part of Theorem 2 for the first canonical top state. -/
theorem realifyCircuit_bottomWeight_column0
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W)
    (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight
        (OrderedCircuit.eval (realifyCircuit c) *ᵥ wireRealColumn0 psi) x =
      complexBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_realifyCircuit_mulVec_wireRealColumn0,
    wireRealColumn0_bottomWeight]

/-- Corrected observable part of Theorem 2 for the second canonical top state. -/
theorem realifyCircuit_bottomWeight_column1
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W)
    (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight
        (OrderedCircuit.eval (realifyCircuit c) *ᵥ wireRealColumn1 psi) x =
      complexBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_realifyCircuit_mulVec_wireRealColumn1,
    wireRealColumn1_bottomWeight]

/-- Corrected observable part of Theorem 2 for every normalized pure top rebit. -/
theorem realifyCircuit_bottomWeight_of_rebit
    {W : Type v} [Fintype W] (c : OrderedCircuit ℂ W) (top : Rebit)
    (psi : BitBasis W → ℂ) (x : BitBasis W) :
    wireRealBottomWeight
        (OrderedCircuit.eval (realifyCircuit c) *ᵥ
          wireRealTopCombination (top false) (top true) psi) x =
      complexBasisWeight (OrderedCircuit.eval c *ᵥ psi) x := by
  rw [eval_realifyCircuit_mulVec_wireRealTopCombination]
  exact wireRealTopCombination_bottomWeight_of_rebit top _ x

end QuaternionicComputing.Simulation
