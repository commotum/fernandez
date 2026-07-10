module

public import QuaternionicComputing.Scalar.Quaternion

/-!
# Quaternionic phase side

For column vectors acted on by matrices from the left, quaternionic scalars act
coherently on the right.  This module records the two candidate ray relations
and gives a concrete norm-preserving two-coordinate evolution for which the
paper's left-phase relation is not preserved.
-/

@[expose] public noncomputable section

open scoped Quaternion RightActions

namespace QuaternionicComputing.Quaternion

/-- Two quaternionic column vectors differ by a unit scalar on the left. -/
def LeftPhaseEquivalent {ι : Type*} (x y : ι → ℍ[ℝ]) : Prop :=
  ∃ η : ℍ[ℝ], _root_.Quaternion.normSq η = 1 ∧ x = η • y

/-- Two quaternionic column vectors differ by a unit scalar on the right. -/
def RightPhaseEquivalent {ι : Type*} (x y : ι → ℍ[ℝ]) : Prop :=
  ∃ η : ℍ[ℝ], _root_.Quaternion.normSq η = 1 ∧ x = y <• η

/-- Multiplication by a unit quaternion on the right preserves scalar norm square. -/
theorem normSq_mul_of_normSq_eq_one (x η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) :
    _root_.Quaternion.normSq (x * η) = _root_.Quaternion.normSq x := by
  rw [map_mul, hη, mul_one]

@[simp]
theorem normSq_i : _root_.Quaternion.normSq i = 1 := by
  rw [_root_.Quaternion.normSq_def']
  norm_num

@[simp]
theorem normSq_j : _root_.Quaternion.normSq j = 1 := by
  rw [_root_.Quaternion.normSq_def']
  norm_num

@[simp]
theorem normSq_k : _root_.Quaternion.normSq k = 1 := by
  rw [_root_.Quaternion.normSq_def']
  norm_num

/-- The same left phase does not commute through arbitrary left multiplication. -/
theorem fixed_left_phase_not_natural :
    j * (i * (1 : ℍ[ℝ])) ≠ i * (j * (1 : ℍ[ℝ])) := by
  intro h
  have hki : -k = k := by
    simpa only [mul_one, j_mul_i, i_mul_j] using h
  have himK := congrArg (fun q : ℍ[ℝ] ↦ q.imK) hki
  norm_num at himK

/-- The two-coordinate input used to witness failure of left-phase rays. -/
def phaseWitnessInput : Bool → ℍ[ℝ] :=
  fun _ ↦ 1

/-- A diagonal two-coordinate evolution with diagonal entries `1` and `j`. -/
def phaseWitnessGate (x : Bool → ℍ[ℝ]) : Bool → ℍ[ℝ]
  | false => x false
  | true => j * x true

/-- The witness gate preserves the sum of coordinate norm squares. -/
theorem phaseWitnessGate_normSq (x : Bool → ℍ[ℝ]) :
    (∑ b, _root_.Quaternion.normSq (phaseWitnessGate x b)) =
      ∑ b, _root_.Quaternion.normSq (x b) := by
  simp [phaseWitnessGate, map_mul]

/-- The input and its left multiple by `i` lie on the same left-phase ray. -/
theorem leftPhaseEquivalent_i_input :
    LeftPhaseEquivalent (i • phaseWitnessInput) phaseWitnessInput := by
  exact ⟨i, normSq_i, rfl⟩

/--
The paper's left-phase ray relation is not preserved by the norm-preserving
diagonal evolution `diag(1,j)`.
-/
theorem not_leftPhaseEquivalent_gate_i_input :
    ¬LeftPhaseEquivalent
      (phaseWitnessGate (i • phaseWitnessInput))
      (phaseWitnessGate phaseWitnessInput) := by
  rintro ⟨η, _, hη⟩
  have hfalse := congrFun hη false
  have htrue := congrFun hη true
  simp only [phaseWitnessGate, phaseWitnessInput, Pi.smul_apply, smul_eq_mul,
    mul_one] at hfalse htrue
  subst η
  have hki : -k = k := by
    simpa only [j_mul_i, i_mul_j] using htrue
  have himK := congrArg (fun q : ℍ[ℝ] ↦ q.imK) hki
  norm_num at himK

/-- The witness gate commutes with every right scalar action. -/
theorem phaseWitnessGate_right_smul (x : Bool → ℍ[ℝ]) (η : ℍ[ℝ]) :
    phaseWitnessGate (x <• η) = phaseWitnessGate x <• η := by
  funext b
  cases b <;> simp [phaseWitnessGate, mul_assoc]

/-- In particular, the right-phase relation is preserved by the witness gate. -/
theorem rightPhaseEquivalent_gate {x y : Bool → ℍ[ℝ]}
    (hxy : RightPhaseEquivalent x y) :
    RightPhaseEquivalent (phaseWitnessGate x) (phaseWitnessGate y) := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact ⟨η, hη, phaseWitnessGate_right_smul y η⟩

end QuaternionicComputing.Quaternion
