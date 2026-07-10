module

public import QuaternionicComputing.Simulation.ComplexToReal
public import QuaternionicComputing.Simulation.QuaternionToComplex

/-!
# End-to-end simulation sanity checks

This diagnostic leaf exercises the public placed-gate, ordered-circuit,
state-column, and bottom-weight APIs on two exact zero-wire scalar examples.
The complex example uses `I`, so it is genuinely non-real.  The quaternionic
example uses `j`, so it cannot be reduced to the complex subalgebra.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Simulation.Examples

open QuaternionicComputing.Circuit
open QuaternionicComputing.State
open QuaternionicComputing.Quaternion

/-- The unique split of a zero-wire local system and zero-wire complement. -/
def emptySplit : Empty ⊕ Empty ≃ Empty :=
  Equiv.sumEmpty Empty Empty

/-- The unique computational-basis assignment on zero wires. -/
def emptyBasis : BitBasis Empty :=
  fun e ↦ nomatch e

/-- Every zero-wire basis assignment is the unique `emptyBasis`. -/
theorem bitBasisEmpty_eq_emptyBasis (x : BitBasis Empty) : x = emptyBasis :=
  Subsingleton.elim _ _

/-- The actual target assignment with added top bit `false`. -/
def falseTopBasis : BitBasis (AddedWire Empty) :=
  addedBasisEquiv Empty (Sum.inl emptyBasis)

/-- The actual target assignment with added top bit `true`. -/
def trueTopBasis : BitBasis (AddedWire Empty) :=
  addedBasisEquiv Empty (Sum.inr emptyBasis)

/-! ## A genuinely non-real complex gate -/

/-- The zero-wire scalar matrix with unique entry `I`. -/
def complexILocal : Matrix (BitBasis Empty) (BitBasis Empty) ℂ :=
  fun _ _ ↦ Complex.I

/-- The locality-certified scalar-`I` gate. -/
def complexIGate : PlacedGate ℂ Empty :=
  PlacedGate.ofSplit emptySplit complexILocal

/-- The one-gate chronological scalar-`I` circuit. -/
def complexICircuit : OrderedCircuit ℂ Empty :=
  [complexIGate]

/-- The unit input column on the unique zero-wire basis state. -/
def complexOneColumn : BitBasis Empty → ℂ :=
  fun _ ↦ 1

@[simp]
theorem eval_complexICircuit_entry :
    OrderedCircuit.eval complexICircuit emptyBasis emptyBasis = Complex.I := by
  simp [complexICircuit, complexIGate, complexILocal, emptySplit]

/-- The realified target operator has a nonzero off-diagonal block entry. -/
theorem eval_realifyComplexICircuit_false_true :
    OrderedCircuit.eval (realifyCircuit complexICircuit)
        falseTopBasis trueTopBasis = 1 := by
  rw [eval_realifyCircuit]
  simp [wireRealify, Matrix.reindex_apply, falseTopBasis, trueTopBasis]

/-- The public translated evaluator intertwines the first real state column. -/
theorem realifyComplexICircuit_column0_evolution :
    OrderedCircuit.eval (realifyCircuit complexICircuit) *ᵥ
        wireRealColumn0 complexOneColumn =
      wireRealColumn0
        (OrderedCircuit.eval complexICircuit *ᵥ complexOneColumn) :=
  eval_realifyCircuit_mulVec_wireRealColumn0 complexICircuit complexOneColumn

/-- The evolved target column has exact top-`true` amplitude `-1`. -/
theorem realifyComplexICircuit_true_amplitude :
    (OrderedCircuit.eval (realifyCircuit complexICircuit) *ᵥ
      wireRealColumn0 complexOneColumn) trueTopBasis = -1 := by
  rw [realifyComplexICircuit_column0_evolution]
  simp [wireRealColumn0, transportAddedColumn, trueTopBasis,
    complexOneColumn, Matrix.mulVec, dotProduct,
    bitBasisEmpty_eq_emptyBasis]

/-- The public bottom-weight simulation gives the exact probability weight `1`. -/
theorem realifyComplexICircuit_bottomWeight :
    wireRealBottomWeight
        (OrderedCircuit.eval (realifyCircuit complexICircuit) *ᵥ
          wireRealColumn0 complexOneColumn) emptyBasis = 1 := by
  rw [realifyCircuit_bottomWeight_column0]
  simp [complexBasisWeight, basisWeight, complexWeight, complexOneColumn,
    Matrix.mulVec, dotProduct, bitBasisEmpty_eq_emptyBasis]

/-! ## A genuinely quaternionic gate -/

/-- The zero-wire scalar matrix with unique entry the quaternionic unit `j`. -/
def quaternionJLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℍ[ℝ] :=
  fun _ _ ↦ j

/-- The locality-certified scalar-`j` gate. -/
def quaternionJGate : PlacedGate ℍ[ℝ] Empty :=
  PlacedGate.ofSplit emptySplit quaternionJLocal

/-- The one-gate chronological scalar-`j` circuit. -/
def quaternionJCircuit : OrderedCircuit ℍ[ℝ] Empty :=
  [quaternionJGate]

/-- The quaternionic unit input column on the unique zero-wire basis state. -/
def quaternionOneColumn : BitBasis Empty → ℍ[ℝ] :=
  fun _ ↦ 1

@[simp]
theorem eval_quaternionJCircuit_entry :
    OrderedCircuit.eval quaternionJCircuit emptyBasis emptyBasis = j := by
  simp [quaternionJCircuit, quaternionJGate, quaternionJLocal, emptySplit]

/-- The complexified target operator has a nonzero off-diagonal block entry. -/
theorem eval_complexifyQuaternionJCircuit_false_true :
    OrderedCircuit.eval (complexifyCircuit quaternionJCircuit)
        falseTopBasis trueTopBasis = 1 := by
  rw [eval_complexifyCircuit]
  simp [wireComplexify, Matrix.reindex_apply, falseTopBasis, trueTopBasis]

/-- The public translated evaluator intertwines the first complex state column. -/
theorem complexifyQuaternionJCircuit_column0_evolution :
    OrderedCircuit.eval (complexifyCircuit quaternionJCircuit) *ᵥ
        wireComplexColumn0 quaternionOneColumn =
      wireComplexColumn0
        (OrderedCircuit.eval quaternionJCircuit *ᵥ quaternionOneColumn) :=
  eval_complexifyCircuit_mulVec_wireComplexColumn0
    quaternionJCircuit quaternionOneColumn

/-- The evolved target column has exact top-`true` amplitude `-1`. -/
theorem complexifyQuaternionJCircuit_true_amplitude :
    (OrderedCircuit.eval (complexifyCircuit quaternionJCircuit) *ᵥ
      wireComplexColumn0 quaternionOneColumn) trueTopBasis = -1 := by
  rw [complexifyQuaternionJCircuit_column0_evolution]
  simp [wireComplexColumn0, transportAddedColumn, trueTopBasis,
    quaternionOneColumn, Matrix.mulVec, dotProduct,
    bitBasisEmpty_eq_emptyBasis]

/-- The public bottom-weight simulation gives the exact probability weight `1`. -/
theorem complexifyQuaternionJCircuit_bottomWeight :
    wireComplexBottomWeight
        (OrderedCircuit.eval (complexifyCircuit quaternionJCircuit) *ᵥ
          wireComplexColumn0 quaternionOneColumn) emptyBasis = 1 := by
  rw [complexifyCircuit_bottomWeight_column0]
  simp [quaternionBasisWeight, basisWeight, quaternionWeight,
    quaternionOneColumn, Matrix.mulVec, dotProduct,
    _root_.Quaternion.normSq_def', bitBasisEmpty_eq_emptyBasis]

end QuaternionicComputing.Simulation.Examples
