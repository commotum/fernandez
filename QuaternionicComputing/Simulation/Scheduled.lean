module

public import QuaternionicComputing.Circuit.Ordering
public import QuaternionicComputing.Simulation.QuaternionToComplex

/-!
# Simulation of legally scheduled quaternionic gate families

This thin bridge applies the fixed-order simulation theorem to the exact
chronological circuit selected by a `LegalSchedule`.  It does not choose a
schedule, identify different schedules, or change ordered-circuit semantics.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {W : Type w} [Fintype W]
variable {precedes : ι → ι → Prop}

/-- Pointwise local unitarity gives local unitarity of the scheduled circuit. -/
theorem LegalSchedule.scheduledCircuit_isLocallyUnitary
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (hunitary : ∀ i, (gates i).IsLocallyUnitary) :
    (schedule.scheduledCircuit gates).IsLocallyUnitary := by
  intro g hg
  rw [schedule.mem_scheduledCircuit_iff gates] at hg
  rcases hg with ⟨i, rfl⟩
  exact hunitary i

/-- A pointwise local-arity bound gives the same bound after scheduling. -/
theorem LegalSchedule.scheduledCircuit_arityBound
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) {d : ℕ}
    (hArity : ∀ i, (gates i).localArity ≤ d) :
    (schedule.scheduledCircuit gates).ArityBound d := by
  intro g hg
  rw [schedule.mem_scheduledCircuit_iff gates] at hg
  rcases hg with ⟨i, rfl⟩
  exact hArity i

/--
The complexified circuit for a fixed legal schedule embeds the operator of
that exact schedule.  No order-independence premise is used or implied.
-/
theorem eval_complexify_scheduledCircuit
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    OrderedCircuit.eval
        (complexifyCircuit (schedule.scheduledCircuit gates)) =
      wireComplexify (schedule.scheduledEval gates) := by
  exact eval_complexifyCircuit (schedule.scheduledCircuit gates)

/-- Complexification is injective, so translating two schedules cannot erase an operator gap. -/
theorem eval_complexify_scheduledCircuit_ne_of_scheduledEval_ne
    (s t : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (h : s.scheduledEval gates ≠ t.scheduledEval gates) :
    OrderedCircuit.eval (complexifyCircuit (s.scheduledCircuit gates)) ≠
      OrderedCircuit.eval (complexifyCircuit (t.scheduledCircuit gates)) := by
  rw [eval_complexify_scheduledCircuit, eval_complexify_scheduledCircuit]
  exact wireComplexify_injective.ne h

/-- The translated scheduled circuit still has exactly one gate per identifier. -/
theorem gateCount_complexify_scheduledCircuit
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    OrderedCircuit.gateCount
        (complexifyCircuit (schedule.scheduledCircuit gates)) =
      Fintype.card ι := by
  rw [gateCount_complexifyCircuit, schedule.gateCount_scheduledCircuit]

/--
Corrected scheduled form of paper Theorem 4.  Every supplied legal schedule is
simulated separately, with its fixed order retained in the source operator.
-/
theorem scheduledQuaternionToComplex_exactSimulation
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) {d : ℕ}
    (hunitary : ∀ i, (gates i).IsLocallyUnitary)
    (hArity : ∀ i, (gates i).localArity ≤ d)
    (top : Qubit) (psi : QuaternionState (BitBasis W)) :
    OrderedCircuit.eval
        (complexifyCircuit (schedule.scheduledCircuit gates)) =
        wireComplexify (schedule.scheduledEval gates) ∧
      OrderedCircuit.gateCount
          (complexifyCircuit (schedule.scheduledCircuit gates)) =
        Fintype.card ι ∧
      Fintype.card (AddedWire W) = Fintype.card W + 1 ∧
      (complexifyCircuit (schedule.scheduledCircuit gates)).ArityBound
        (d + 1) ∧
      ∀ x : BitBasis W,
        wireComplexBottomWeight
            (complexifyCircuitOutput (schedule.scheduledCircuit gates)
              (LegalSchedule.scheduledCircuit_isLocallyUnitary
                schedule gates hunitary)
              top psi) x =
          quaternionBasisWeight
            (quaternionCircuitOutput (schedule.scheduledCircuit gates)
              (LegalSchedule.scheduledCircuit_isLocallyUnitary
                schedule gates hunitary)
              psi) x := by
  let c := schedule.scheduledCircuit gates
  have hc : c.IsLocallyUnitary :=
    LegalSchedule.scheduledCircuit_isLocallyUnitary schedule gates hunitary
  have hd : c.ArityBound d :=
    LegalSchedule.scheduledCircuit_arityBound schedule gates hArity
  have hsim := quaternionToComplex_exactSimulation hc hd top psi
  simpa [c, LegalSchedule.scheduledEval,
    schedule.gateCount_scheduledCircuit gates] using hsim

end QuaternionicComputing.Simulation
