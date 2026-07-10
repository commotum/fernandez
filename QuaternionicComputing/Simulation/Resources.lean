module

public import QuaternionicComputing.Circuit.Depth
public import QuaternionicComputing.Circuit.DescriptionCost
public import QuaternionicComputing.Simulation.QuaternionToReal

/-!
# Structural resources of the exact circuit translations

This file connects the generic support-depth and dense-description measures to
the literal circuit maps used by the exact simulations.

Every image gate in each primary translation certifiably uses the same added
top wire.  Consequently, in the conventional model where one parallel layer
may contain only pairwise support-disjoint gates, *every* nonempty layering of
the image circuit has depth equal to its gate count.  This is a theorem about
the present shared-top construction, not a lower bound against alternative
encodings or multi-ancilla constructions.

Dense local matrix descriptions grow by exactly four scalar-entry slots per
source slot for one added wire, and by sixteen under the visible two-step
quaternion-to-real composition.  Slot counts are not bit or runtime costs.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit

universe v

/-! ## The shared top wire belongs to every translated gate support -/

/-- The distinguished top wire is in every realified gate's certified support. -/
theorem top_mem_support_realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) :
    Sum.inl () ∈ (realifyPlacedGate g).support := by
  rw [PlacedGate.mem_support_iff]
  exact ⟨Sum.inl (), localSupport_realifyPlacedGate_top g ()⟩

/-- The distinguished top wire is in every complexified gate's certified support. -/
theorem top_mem_support_complexifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) :
    Sum.inl () ∈ (complexifyPlacedGate g).support := by
  rw [PlacedGate.mem_support_iff]
  exact ⟨Sum.inl (), localSupport_complexifyPlacedGate_top g ()⟩

/-- Every gate occurrence in a realified circuit uses the shared top wire. -/
theorem top_mem_support_of_mem_realifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℂ W} {k : PlacedGate ℝ (AddedWire W)}
    (hk : k ∈ realifyCircuit c) :
    Sum.inl () ∈ k.support := by
  rcases List.mem_map.mp hk with ⟨g, -, rfl⟩
  exact top_mem_support_realifyPlacedGate g

/-- Every gate occurrence in a complexified circuit uses the shared top wire. -/
theorem top_mem_support_of_mem_complexifyCircuit {W : Type v} [Fintype W]
    {c : OrderedCircuit ℍ[ℝ] W} {k : PlacedGate ℂ (AddedWire W)}
    (hk : k ∈ complexifyCircuit c) :
    Sum.inl () ∈ k.support := by
  rcases List.mem_map.mp hk with ⟨g, -, rfl⟩
  exact top_mem_support_complexifyPlacedGate g

/-! ## Exact serialization in the support-disjoint depth model -/

/-- Every support layering of the literal realified circuit has depth equal to source gate count. -/
theorem depth_realifyCircuit_eq_gateCount {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W)
    (schedule : SupportLayering (realifyCircuit c)) :
    schedule.depth = c.gateCount := by
  calc
    schedule.depth = (realifyCircuit c).gateCount :=
      schedule.depth_eq_gateCount_of_commonWire (Sum.inl ())
        (fun k hk => top_mem_support_of_mem_realifyCircuit hk)
    _ = c.gateCount := gateCount_realifyCircuit c

/-- Every support layering of the literal complexified circuit has depth equal to source gate count. -/
theorem depth_complexifyCircuit_eq_gateCount {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W)
    (schedule : SupportLayering (complexifyCircuit c)) :
    schedule.depth = c.gateCount := by
  calc
    schedule.depth = (complexifyCircuit c).gateCount :=
      schedule.depth_eq_gateCount_of_commonWire (Sum.inl ())
        (fun k hk => top_mem_support_of_mem_complexifyCircuit hk)
    _ = c.gateCount := gateCount_complexifyCircuit c

/-- The canonical serial support layering of the realified circuit. -/
def realifyCircuitSerialLayering {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) : SupportLayering (realifyCircuit c) :=
  SupportLayering.serial (realifyCircuit c)

/-- The canonical serial support layering of the complexified circuit. -/
def complexifyCircuitSerialLayering {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) : SupportLayering (complexifyCircuit c) :=
  SupportLayering.serial (complexifyCircuit c)

@[simp]
theorem depth_realifyCircuitSerialLayering {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) :
    (realifyCircuitSerialLayering c).depth = c.gateCount := by
  rw [realifyCircuitSerialLayering, SupportLayering.depth_serial,
    gateCount_realifyCircuit]

@[simp]
theorem depth_complexifyCircuitSerialLayering {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    (complexifyCircuitSerialLayering c).depth = c.gateCount := by
  rw [complexifyCircuitSerialLayering, SupportLayering.depth_serial,
    gateCount_complexifyCircuit]

/-- The visible quaternion-to-real composition is also forced serial by its newest shared top wire. -/
theorem depth_quaternionToRealCircuit_eq_gateCount
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W)
    (schedule : SupportLayering (quaternionToRealCircuit c)) :
    schedule.depth = c.gateCount := by
  unfold quaternionToRealCircuit at schedule ⊢
  calc
    schedule.depth = (complexifyCircuit c).gateCount :=
      depth_realifyCircuit_eq_gateCount (complexifyCircuit c) schedule
    _ = c.gateCount := gateCount_complexifyCircuit c

/-! ## Exact dense scalar-entry slot factors -/

/-- One added realification wire multiplies total dense local entry slots by four. -/
theorem totalDenseEntrySlots_realifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℂ W) :
    OrderedCircuit.totalDenseEntrySlots (realifyCircuit c) =
      4 * c.totalDenseEntrySlots :=
  OrderedCircuit.totalDenseEntrySlots_map_eq_four_mul
    realifyPlacedGate localArity_realifyPlacedGate c

/-- One added complexification wire multiplies total dense local entry slots by four. -/
theorem totalDenseEntrySlots_complexifyCircuit {W : Type v} [Fintype W]
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.totalDenseEntrySlots (complexifyCircuit c) =
      4 * c.totalDenseEntrySlots :=
  OrderedCircuit.totalDenseEntrySlots_map_eq_four_mul
    complexifyPlacedGate localArity_complexifyPlacedGate c

/-- The visible two-added-wire composition multiplies dense local entry slots by sixteen. -/
theorem totalDenseEntrySlots_quaternionToRealCircuit
    {W : Type v} [Fintype W] (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.totalDenseEntrySlots (quaternionToRealCircuit c) =
      16 * c.totalDenseEntrySlots := by
  rw [quaternionToRealCircuit, totalDenseEntrySlots_realifyCircuit,
    totalDenseEntrySlots_complexifyCircuit]
  omega

end QuaternionicComputing.Simulation
