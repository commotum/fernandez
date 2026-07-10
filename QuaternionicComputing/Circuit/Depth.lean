module

public import QuaternionicComputing.Circuit.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Support-layer depth for finite circuits

This file provides a deliberately syntactic parallel-depth model.  A
`SupportLayering c` partitions the chronological list `c` into nonempty
layers.  Gates in one layer have pairwise disjoint certified supports, and
flattening the layers recovers the original chronology exactly.

The layering is a resource certificate, not a second circuit semantics.  In
particular, disjoint support does not by itself imply commutation over
quaternionic coefficients.  Evaluation always remains that of the flattened
`OrderedCircuit`.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

universe u v

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/--
A partition of a chronological circuit into nonempty, support-disjoint
parallel layers.

`flatten_eq` fixes the chronology.  `pairwiseDisjoint` is only the conventional
syntactic resource constraint for gates sharing no certified wire.
-/
structure SupportLayering (c : OrderedCircuit R W) where
  /-- Parallel layers, retained in chronological order. -/
  layers : List (List (PlacedGate R W))
  /-- Flattening the layers recovers the exact chronological circuit. -/
  flatten_eq : layers.flatten = c
  /-- Empty padding layers are excluded from the depth count. -/
  nonempty : ∀ layer ∈ layers, layer ≠ []
  /-- Distinct occurrences in one layer have disjoint certified supports. -/
  pairwiseDisjoint : ∀ layer ∈ layers,
    layer.Pairwise fun g h => Disjoint g.support h.support

namespace SupportLayering

/-- The number of nonempty parallel layers. -/
def depth {c : OrderedCircuit R W} (schedule : SupportLayering c) : ℕ :=
  schedule.layers.length

/-- The sum of all layer sizes is the circuit gate count. -/
theorem sum_layerLengths {c : OrderedCircuit R W}
    (schedule : SupportLayering c) :
    (schedule.layers.map List.length).sum = c.gateCount := by
  rw [← List.length_flatten, schedule.flatten_eq]
  rfl

/-- Every nonempty support layering has depth at most its gate count. -/
theorem depth_le_gateCount {c : OrderedCircuit R W}
    (schedule : SupportLayering c) :
    schedule.depth ≤ c.gateCount := by
  rw [← schedule.sum_layerLengths]
  change schedule.layers.length ≤ _
  calc
    schedule.layers.length =
        (schedule.layers.map fun _ => 1).sum := by simp
    _ ≤ (schedule.layers.map List.length).sum := by
      apply List.sum_le_sum
      intro layer hlayer
      exact (List.length_pos_iff_ne_nil.mpr
        (schedule.nonempty layer hlayer))

/--
The canonical serialization: every gate occurrence occupies its own layer.
-/
def serial (c : OrderedCircuit R W) : SupportLayering c where
  layers := c.map fun g => [g]
  flatten_eq := by
    induction c with
    | nil => rfl
    | cons g c ih => simp [ih]
  nonempty := by
    intro layer hlayer
    rcases List.mem_map.mp hlayer with ⟨g, -, rfl⟩
    simp
  pairwiseDisjoint := by
    intro layer hlayer
    rcases List.mem_map.mp hlayer with ⟨g, -, rfl⟩
    simp

/-- The canonical serial layering has depth exactly equal to gate count. -/
@[simp]
theorem depth_serial (c : OrderedCircuit R W) :
    (serial c).depth = c.gateCount := by
  simp [depth, serial, OrderedCircuit.gateCount]

/--
Every gate occurrence in a layer is an occurrence in the flattened circuit.
-/
theorem gate_mem_of_mem_layer {c : OrderedCircuit R W}
    (schedule : SupportLayering c) {layer : List (PlacedGate R W)}
    (hlayer : layer ∈ schedule.layers) {g : PlacedGate R W}
    (hg : g ∈ layer) : g ∈ c := by
  rw [← schedule.flatten_eq]
  exact List.mem_flatten.mpr ⟨layer, hlayer, hg⟩

/--
If every circuit gate uses one common wire, each support-disjoint layer is a
singleton.
-/
theorem layer_length_eq_one_of_commonWire {c : OrderedCircuit R W}
    (schedule : SupportLayering c) (w : W)
    (hcommon : ∀ g ∈ c, w ∈ g.support)
    {layer : List (PlacedGate R W)} (hlayer : layer ∈ schedule.layers) :
    layer.length = 1 := by
  cases layer with
  | nil => exact (schedule.nonempty [] hlayer rfl).elim
  | cons g tail =>
      cases tail with
      | nil => rfl
      | cons h tail =>
          have hpair := schedule.pairwiseDisjoint (g :: h :: tail) hlayer
          have hdisjoint : Disjoint g.support h.support :=
            (List.pairwise_cons.mp hpair).1 h (by simp)
          have hgw : w ∈ g.support :=
            hcommon g (schedule.gate_mem_of_mem_layer hlayer (by simp))
          have hhw : w ∈ h.support :=
            hcommon h (schedule.gate_mem_of_mem_layer hlayer (by simp))
          exact ((Finset.disjoint_left.mp hdisjoint) hgw hhw).elim

/--
When every gate uses a common wire, every valid support layering is forced to
be serial: its depth is exactly the circuit gate count.
-/
theorem depth_eq_gateCount_of_commonWire {c : OrderedCircuit R W}
    (schedule : SupportLayering c) (w : W)
    (hcommon : ∀ g ∈ c, w ∈ g.support) :
    schedule.depth = c.gateCount := by
  calc
    schedule.depth = schedule.layers.length := rfl
    _ = (schedule.layers.map fun _ => 1).sum := by simp
    _ = (schedule.layers.map List.length).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro layer hlayer
      exact (schedule.layer_length_eq_one_of_commonWire w hcommon hlayer).symm
    _ = c.gateCount := schedule.sum_layerLengths

end SupportLayering

end QuaternionicComputing.Circuit
