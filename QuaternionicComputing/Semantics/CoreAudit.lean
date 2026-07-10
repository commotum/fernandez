module

public import QuaternionicComputing.Semantics.Measurement
public import QuaternionicComputing.Circuit.BasisPreparation

/-!
# Exact and basis-measurement semantic audit

This diagnostic leaf exercises the Stage 2 relations on empty operator index
types, standard real/complex/quaternion basis kets, and an actual ordered
circuit built from the public basis-preparation gate. It is intentionally not a
public-root import.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.CoreAudit

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

/-- Empty rectangular operator spaces still have ordinary exact equality. -/
theorem emptyOperator_exact {R O : Type*}
    (U V : Matrix O Empty R) : ExactOperatorEq U V := by
  exact funext fun _ ↦ funext fun i ↦ isEmptyElim i

/-- Every real computational basis ket has total basis weight one. -/
theorem realBasisKet_normalized (x : Bool) :
    totalWeight realWeight (Pi.single x 1) = 1 := by
  classical
  cases x <;>
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool,
      Pi.single_apply]

/-- Every complex computational basis ket has total basis weight one. -/
theorem complexBasisKet_normalized (x : Bool) :
    totalWeight complexWeight (Pi.single x 1) = 1 := by
  classical
  cases x <;>
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool,
      Pi.single_apply]

/-- Every quaternionic computational basis ket has total basis weight one. -/
theorem quaternionBasisKet_normalized (x : Bool) :
    totalWeight quaternionWeight (Pi.single x 1) = 1 := by
  classical
  cases x <;>
    simp [totalWeight, basisWeight, quaternionWeight, Fintype.univ_bool,
      Pi.single_apply]

/-- The generic pure-input-to-basis theorem specializes without hidden premises. -/
theorem complexPureInput_to_basis {U V : Matrix Bool Bool ℂ}
    (h : PureInputBasisMeasurementEq complexWeight U V) :
    BasisMeasurementEq complexWeight U V :=
  h.basisMeasurementEq complexBasisKet_normalized

/-- Exact circuit equality is consumed through an actual public circuit constructor. -/
theorem basisPreparation_exact (b : BitBasis Bool) :
    ExactCircuitEq
      ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool)
      [basisPreparationGate (R := ℂ) b] :=
  ExactCircuitEq.refl _

/-- The exact circuit witness yields all-normalized-pure-input basis agreement. -/
theorem basisPreparation_pureInputAgreement (b : BitBasis Bool) :
    PureInputBasisMeasurementEq complexWeight
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool))
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool)) :=
  (basisPreparation_exact b).pureInputBasisMeasurementEq

/-- Pointwise equality of one normalized state gives the same packaged distribution. -/
theorem complexState_distribution_refl (ψ : ComplexState Bool) :
    NormalizedDistributionEq complexWeight complexWeight_nonneg ψ ψ :=
  NormalizedDistributionEq.refl ψ

end QuaternionicComputing.Semantics.CoreAudit

#print axioms QuaternionicComputing.Semantics.ExactOperatorEq.mul
#print axioms QuaternionicComputing.Semantics.ExactCircuitEq.append
#print axioms QuaternionicComputing.Semantics.basisMeasurementEq_iff_outputWeightEqAt_basis
#print axioms QuaternionicComputing.Semantics.basisWeightEq_iff_normalizedDistributionEq
#print axioms QuaternionicComputing.Semantics.CoreAudit.complexPureInput_to_basis
#print axioms QuaternionicComputing.Semantics.CoreAudit.basisPreparation_pureInputAgreement
