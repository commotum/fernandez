module

public import QuaternionicComputing.Circuit.OrderingWitness
public import QuaternionicComputing.Simulation.Scheduled

/-!
# Complex simulation of the order-dependence witness

This file transports the disjoint-gate witness from
`Circuit.OrderingWitness` through the exact quaternion-to-complex simulation.
The added top wire is initialized in the canonical normalized state `|0⟩`.

Both legal schedules are translated exactly as supplied.  Their complexified
operators remain unequal, while the bottom-wire outcome corresponding to the
source basis value `00` has the same exact weight as in each quaternionic
source circuit: respectively `8281 / 15625` and `1369 / 15625`.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Simulation.OrderingWitness

open QuaternionicComputing.Circuit
open QuaternionicComputing.Circuit.OrderingWitness
open QuaternionicComputing.State

/-- The canonical normalized top qubit `|0⟩`. -/
def topZero : Qubit :=
  ⟨fun q => if q then 0 else 1, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

@[simp]
theorem topZero_false : topZero false = 1 :=
  rfl

@[simp]
theorem topZero_true : topZero true = 0 :=
  rfl

/-- Every gate occurrence in the witness family is locally unitary. -/
theorem gateFamily_locallyUnitary (q : Bool) :
    (gateFamily q).IsLocallyUnitary := by
  cases q
  · exact iGate_locallyUnitary
  · exact jGate_locallyUnitary

/-- Local unitarity of the first scheduled witness circuit. -/
theorem iThenJScheduled_locallyUnitary :
    (iThenJSchedule.scheduledCircuit gateFamily).IsLocallyUnitary :=
  QuaternionicComputing.Simulation.LegalSchedule.scheduledCircuit_isLocallyUnitary
    iThenJSchedule gateFamily gateFamily_locallyUnitary

/-- Local unitarity of the reverse scheduled witness circuit. -/
theorem jThenIScheduled_locallyUnitary :
    (jThenISchedule.scheduledCircuit gateFamily).IsLocallyUnitary :=
  QuaternionicComputing.Simulation.LegalSchedule.scheduledCircuit_isLocallyUnitary
    jThenISchedule gateFamily gateFamily_locallyUnitary

/--
The normalized complex output obtained by translating the supplied
`i`-then-`j` schedule and initializing the added wire in `|0⟩`.
-/
def iThenJComplexOutput : ComplexState (BitBasis (AddedWire Bool)) :=
  complexifyCircuitOutput
    (iThenJSchedule.scheduledCircuit gateFamily)
    iThenJScheduled_locallyUnitary topZero inputState

/--
The normalized complex output obtained by translating the supplied
`j`-then-`i` schedule and initializing the added wire in `|0⟩`.
-/
def jThenIComplexOutput : ComplexState (BitBasis (AddedWire Bool)) :=
  complexifyCircuitOutput
    (jThenISchedule.scheduledCircuit gateFamily)
    jThenIScheduled_locallyUnitary topZero inputState

/-- Complexification does not erase the witness's scheduled operator inequality. -/
theorem complexified_scheduled_operators_ne :
    OrderedCircuit.eval
        (complexifyCircuit
          (iThenJSchedule.scheduledCircuit gateFamily)) ≠
      OrderedCircuit.eval
        (complexifyCircuit
          (jThenISchedule.scheduledCircuit gateFamily)) :=
  eval_complexify_scheduledCircuit_ne_of_scheduledEval_ne
    iThenJSchedule jThenISchedule gateFamily scheduled_operators_ne

/-- The translated `i`-then-`j` output has exact bottom `00` weight `8281/15625`. -/
theorem iThenJComplexOutput_basis00_weight :
    wireComplexBottomWeight iThenJComplexOutput basis00 =
      8281 / 15625 := by
  unfold iThenJComplexOutput
  rw [complexifyCircuitOutput_bottomProbability]
  simpa [quaternionCircuitOutput, iThenJOutput] using
    iThenJOutput_basis00_weight

/-- The translated `j`-then-`i` output has exact bottom `00` weight `1369/15625`. -/
theorem jThenIComplexOutput_basis00_weight :
    wireComplexBottomWeight jThenIComplexOutput basis00 =
      1369 / 15625 := by
  unfold jThenIComplexOutput
  rw [complexifyCircuitOutput_bottomProbability]
  simpa [quaternionCircuitOutput, jThenIOutput] using
    jThenIOutput_basis00_weight

/-- The two translated schedules therefore have different bottom-wire outcomes. -/
theorem complexOutput_basis00_weight_ne :
    wireComplexBottomWeight iThenJComplexOutput basis00 ≠
      wireComplexBottomWeight jThenIComplexOutput basis00 := by
  rw [iThenJComplexOutput_basis00_weight,
    jThenIComplexOutput_basis00_weight]
  norm_num

end QuaternionicComputing.Simulation.OrderingWitness
