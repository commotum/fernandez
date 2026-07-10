module

public import QuaternionicComputing.Circuit.OrderingWitness

/-!
# Order-sensitive columns from a pure product input

This file reuses the disjoint locally unitary quaternionic `i`- and `j`-mixers
from `Circuit.OrderingWitness`, but starts from the normalized computational
basis state `|00⟩`.  That input factors pointwise into one-wire ground
amplitudes.

The two legal chronological orders produce opposite amplitudes at `|11⟩`:
`i` then `j` gives `-(16/25)k`, while `j` then `i` gives `(16/25)k`.
Consequently their output columns are unequal.  The two `|11⟩` basis weights
are nevertheless equal, so column inequality alone is not an observable
probability distinction.

This bounded diagnostic proves no signaling, entanglement, cryptographic
security, or mixed-state claim.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Circuit.ProductInputOrderingWitness

open QuaternionicComputing.Circuit.OrderingWitness
open QuaternionicComputing.State
open QuaternionicComputing.Quaternion

/-! ## The normalized ground product input -/

/-- One-wire ground-state amplitude, equal to one at `false` and zero at `true`. -/
def groundFactor (bit : Bool) : ℍ[ℝ] :=
  if bit then 0 else 1

/-- The two-wire computational-basis ground column `|00⟩`. -/
def groundColumn (x : BitBasis Bool) : ℍ[ℝ] :=
  if x = basis00 then 1 else 0

@[simp]
theorem groundColumn_basis00 : groundColumn basis00 = 1 := by
  simp [groundColumn]

@[simp]
theorem groundColumn_basis01 : groundColumn basis01 = 0 := by
  simp [groundColumn, basis00, basis01]

@[simp]
theorem groundColumn_basis10 : groundColumn basis10 = 0 := by
  simp [groundColumn, basis00, basis10]

@[simp]
theorem groundColumn_basis11 : groundColumn basis11 = 0 := by
  simp [groundColumn, basis00, basis11]

/-- The ground column factors into the ground amplitudes of its two wires. -/
theorem groundColumn_product (x : BitBasis Bool) :
    groundColumn x = groundFactor (x false) * groundFactor (x true) := by
  have hx : x = basis00 ↔ x false = false ∧ x true = false := by
    constructor
    · intro h
      subst x
      simp [basis00]
    · rintro ⟨hfalse, htrue⟩
      funext w
      cases w
      · simpa [basis00] using hfalse
      · simpa [basis00] using htrue
  cases hfalse : x false <;> cases htrue : x true <;>
    simp [groundColumn, groundFactor, hx, hfalse, htrue]

/-- The ground product column has exact total quaternionic weight one. -/
theorem groundColumn_normalization :
    quaternionTotalWeight groundColumn = 1 := by
  change (∑ x, _root_.Quaternion.normSq (groundColumn x)) = 1
  rw [sum_bitBasisBool]
  simp [_root_.Quaternion.normSq_def']

/-- The explicitly normalized pure ground product input. -/
def groundState : QuaternionState (BitBasis Bool) :=
  ⟨groundColumn, groundColumn_normalization⟩

/-! ## The two legal scheduled output columns -/

/-- Output column for the legal chronological order `i` then `j`. -/
def iThenJGroundOutputColumn : BitBasis Bool → ℍ[ℝ] :=
  iThenJSchedule.scheduledEval gateFamily *ᵥ groundColumn

/-- Output column for the legal chronological order `j` then `i`. -/
def jThenIGroundOutputColumn : BitBasis Bool → ℍ[ℝ] :=
  jThenISchedule.scheduledEval gateFamily *ᵥ groundColumn

private theorem iThenJ_ground_scalar_calculation :
    mixerOffDiagonal * j * (mixerOffDiagonal * i) =
      (⟨0, 0, 0, -16 / 25⟩ : ℍ[ℝ]) := by
  ext <;> norm_num [mixerOffDiagonal]

private theorem jThenI_ground_scalar_calculation :
    mixerOffDiagonal * i * (mixerOffDiagonal * j) =
      (⟨0, 0, 0, 16 / 25⟩ : ℍ[ℝ]) := by
  ext <;> norm_num [mixerOffDiagonal]

/-- Chronological `i` then `j` gives `-(16/25)k` at `|11⟩`. -/
@[simp]
theorem iThenJGroundOutputColumn_basis11 :
    iThenJGroundOutputColumn basis11 =
      (⟨0, 0, 0, -16 / 25⟩ : ℍ[ℝ]) := by
  change (OrderedCircuit.eval iThenJ *ᵥ groundColumn) basis11 = _
  rw [show OrderedCircuit.eval iThenJ = jGate.denote * iGate.denote by
    simp [iThenJ]]
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [sum_bitBasisBool]
  simpa [iGate_denote_apply, jGate_denote_apply, groundColumn, iMixer, jMixer,
    boolMixer, basis00, basis01, basis10, basis11] using
    iThenJ_ground_scalar_calculation

/-- Chronological `j` then `i` gives `(16/25)k` at `|11⟩`. -/
@[simp]
theorem jThenIGroundOutputColumn_basis11 :
    jThenIGroundOutputColumn basis11 =
      (⟨0, 0, 0, 16 / 25⟩ : ℍ[ℝ]) := by
  change (OrderedCircuit.eval jThenI *ᵥ groundColumn) basis11 = _
  rw [show OrderedCircuit.eval jThenI = iGate.denote * jGate.denote by
    simp [jThenI]]
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [sum_bitBasisBool]
  simpa [iGate_denote_apply, jGate_denote_apply, groundColumn, iMixer, jMixer,
    boolMixer, basis00, basis01, basis10, basis11] using
    jThenI_ground_scalar_calculation

/-- The two legal chronological orders produce unequal output columns. -/
theorem ground_output_columns_ne :
    iThenJGroundOutputColumn ≠ jThenIGroundOutputColumn := by
  intro h
  have h11 := congrFun h basis11
  rw [iThenJGroundOutputColumn_basis11,
    jThenIGroundOutputColumn_basis11] at h11
  have himK := congrArg (fun q : ℍ[ℝ] ↦ q.imK) h11
  norm_num at himK

/-! ## Equal weight at the separating coordinate -/

/-- The `i`-then-`j` output has `|11⟩` weight `256/625`. -/
theorem iThenJGroundOutputColumn_basis11_weight :
    quaternionBasisWeight iThenJGroundOutputColumn basis11 = 256 / 625 := by
  rw [quaternionBasisWeight, basisWeight,
    iThenJGroundOutputColumn_basis11]
  norm_num [quaternionWeight, _root_.Quaternion.normSq_def']

/-- The `j`-then-`i` output has the same `|11⟩` weight `256/625`. -/
theorem jThenIGroundOutputColumn_basis11_weight :
    quaternionBasisWeight jThenIGroundOutputColumn basis11 = 256 / 625 := by
  rw [quaternionBasisWeight, basisWeight,
    jThenIGroundOutputColumn_basis11]
  norm_num [quaternionWeight, _root_.Quaternion.normSq_def']

/-- The unequal `|11⟩` amplitudes have equal computational-basis weight. -/
theorem ground_output_basis11_weights_eq :
    quaternionBasisWeight iThenJGroundOutputColumn basis11 =
      quaternionBasisWeight jThenIGroundOutputColumn basis11 := by
  rw [iThenJGroundOutputColumn_basis11_weight,
    jThenIGroundOutputColumn_basis11_weight]

/-! ## Bundled normalized output states -/

/--
The normalized ground-state output for the legal chronological order
`i` then `j`.
-/
def iThenJGroundOutput : QuaternionState (BitBasis Bool) :=
  QuaternionState.evolveUnitary groundState
    (iThenJSchedule.scheduledEval gateFamily)
    (by
      simpa [LegalSchedule.scheduledEval] using
        OrderedCircuit.eval_mem_unitary iThenJ_locallyUnitary)

/--
The normalized ground-state output for the legal chronological order
`j` then `i`.
-/
def jThenIGroundOutput : QuaternionState (BitBasis Bool) :=
  QuaternionState.evolveUnitary groundState
    (jThenISchedule.scheduledEval gateFamily)
    (by
      simpa [LegalSchedule.scheduledEval] using
        OrderedCircuit.eval_mem_unitary jThenI_locallyUnitary)

/-- The bundled `i`-then-`j` output has amplitude `-(16/25)k` at `|11⟩`. -/
@[simp]
theorem iThenJGroundOutput_basis11 :
    iThenJGroundOutput basis11 =
      (⟨0, 0, 0, -16 / 25⟩ : ℍ[ℝ]) :=
  iThenJGroundOutputColumn_basis11

/-- The bundled `j`-then-`i` output has amplitude `(16/25)k` at `|11⟩`. -/
@[simp]
theorem jThenIGroundOutput_basis11 :
    jThenIGroundOutput basis11 =
      (⟨0, 0, 0, 16 / 25⟩ : ℍ[ℝ]) :=
  jThenIGroundOutputColumn_basis11

/-- The two normalized ground-state outputs are unequal. -/
theorem ground_outputs_ne :
    iThenJGroundOutput ≠ jThenIGroundOutput := by
  intro h
  apply ground_output_columns_ne
  exact congrArg Subtype.val h

/--
The unequal bundled output states nevertheless have equal computational-basis
weight at the separating coordinate `|11⟩`.
-/
theorem ground_outputs_basis11_weights_eq :
    quaternionBasisWeight iThenJGroundOutput basis11 =
      quaternionBasisWeight jThenIGroundOutput basis11 :=
  ground_output_basis11_weights_eq

end QuaternionicComputing.Circuit.ProductInputOrderingWitness
