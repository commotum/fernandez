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

/-- The complete exact-operator law surface is exercised by one square consumer. -/
theorem exactOperator_api (U V T : Matrix Bool Bool ℂ)
    (hUV : ExactOperatorEq U V) (hVT : ExactOperatorEq V T) :
    ExactOperatorEq U U ∧
      ExactOperatorEq U U ∧
      ExactOperatorEq V U ∧
      ExactOperatorEq U T ∧
      (ExactOperatorEq U V ↔ U = V) ∧
      ExactOperatorEq U V ∧
      U = V ∧
      ExactOperatorEq (U * U) (V * V) := by
  exact ⟨ExactOperatorEq.refl U,
    ExactOperatorEq.equivalence.1 U,
    ExactOperatorEq.symm hUV,
    ExactOperatorEq.trans hUV hVT,
    ExactOperatorEq.iff_eq,
    ExactOperatorEq.of_eq (ExactOperatorEq.eq hUV),
    ExactOperatorEq.eq hUV,
    ExactOperatorEq.mul hUV hUV⟩

/-- The exact-circuit laws are consumed without identifying circuit lists. -/
theorem exactCircuit_api
    (C D E : OrderedCircuit ℂ Bool)
    (hCD : ExactCircuitEq C D) (hDE : ExactCircuitEq D E)
    (hgate : List.Forall₂ (fun g k ↦ g.denote = k.denote) C D) :
    ExactCircuitEq C C ∧
      ExactCircuitEq C C ∧
      ExactCircuitEq D C ∧
      ExactCircuitEq C E ∧
      (ExactCircuitEq C D ↔ OrderedCircuit.eval C = OrderedCircuit.eval D) ∧
      ExactCircuitEq C C ∧
      OrderedCircuit.eval C = OrderedCircuit.eval D ∧
      ExactCircuitEq C D ∧
      ExactCircuitEq (C ++ D) (D ++ E) := by
  exact ⟨ExactCircuitEq.refl C,
    ExactCircuitEq.equivalence.1 C,
    ExactCircuitEq.symm hCD,
    ExactCircuitEq.trans hCD hDE,
    ExactCircuitEq.iff_eval_eq,
    ExactCircuitEq.of_eq rfl,
    ExactCircuitEq.eval_eq hCD,
    ExactCircuitEq.of_gatewise hgate,
    ExactCircuitEq.append hCD hDE⟩

/-- The pointwise basis-weight equivalence laws have a concrete complex consumer. -/
theorem basisWeight_api (a b c : Bool → ℂ)
    (hab : BasisWeightEq complexWeight a b)
    (hbc : BasisWeightEq complexWeight b c) :
    BasisWeightEq complexWeight a a ∧
      BasisWeightEq complexWeight a a ∧
      BasisWeightEq complexWeight b a ∧
      BasisWeightEq complexWeight a c ∧
      BasisWeightEq complexWeight a a := by
  exact ⟨BasisWeightEq.refl a,
    BasisWeightEq.equivalence.1 a,
    BasisWeightEq.symm hab,
    BasisWeightEq.trans hab hbc,
    BasisWeightEq.of_eq rfl⟩

/-- The fixed-input relation remains a separate, directly exercised scope. -/
theorem outputWeightEqAt_api (U V T : Matrix Bool Bool ℂ)
    (input : Bool → ℂ)
    (hUV : OutputWeightEqAt complexWeight U V input)
    (hVT : OutputWeightEqAt complexWeight V T input)
    (hexact : ExactOperatorEq U V) :
    OutputWeightEqAt complexWeight U U input ∧
      OutputWeightEqAt complexWeight U U input ∧
      OutputWeightEqAt complexWeight V U input ∧
      OutputWeightEqAt complexWeight U T input ∧
      OutputWeightEqAt complexWeight U V input := by
  exact ⟨OutputWeightEqAt.refl U,
    OutputWeightEqAt.equivalence.1 U,
    OutputWeightEqAt.symm hUV,
    OutputWeightEqAt.trans hUV hVT,
    OutputWeightEqAt.of_exact hexact⟩

/-- The all-basis-input relation laws have a distinct consumer. -/
theorem basisMeasurement_api (U V T : Matrix Bool Bool ℂ)
    (hUV : BasisMeasurementEq complexWeight U V)
    (hVT : BasisMeasurementEq complexWeight V T)
    (hexact : ExactOperatorEq U V) :
    BasisMeasurementEq complexWeight U U ∧
      BasisMeasurementEq complexWeight U U ∧
      BasisMeasurementEq complexWeight V U ∧
      BasisMeasurementEq complexWeight U T ∧
      BasisMeasurementEq complexWeight U V := by
  exact ⟨BasisMeasurementEq.refl U,
    BasisMeasurementEq.equivalence.1 U,
    BasisMeasurementEq.symm hUV,
    BasisMeasurementEq.trans hUV hVT,
    BasisMeasurementEq.of_exact hexact⟩

/-- Basis-ket and matrix-column formulations are checked together. -/
theorem basisMeasurement_basisCharacterization (U V : Matrix Bool Bool ℂ)
    (x : Bool) :
    (BasisMeasurementEq complexWeight U V ↔
      ∀ z, OutputWeightEqAt complexWeight U V (Pi.single z 1)) ∧
      (OutputWeightEqAt complexWeight U V (Pi.single x 1) ↔
        ∀ y, complexWeight (U y x) = complexWeight (V y x)) := by
  exact ⟨basisMeasurementEq_iff_outputWeightEqAt_basis complexWeight U V,
    outputWeightEqAt_basis_iff_column_weight complexWeight U V x⟩

/-- The all-normalized-pure-input relation laws have a distinct consumer. -/
theorem pureInputBasisMeasurement_api (U V T : Matrix Bool Bool ℂ)
    (hUV : PureInputBasisMeasurementEq complexWeight U V)
    (hVT : PureInputBasisMeasurementEq complexWeight V T)
    (hexact : ExactOperatorEq U V) :
    PureInputBasisMeasurementEq complexWeight U U ∧
      PureInputBasisMeasurementEq complexWeight U U ∧
      PureInputBasisMeasurementEq complexWeight V U ∧
      PureInputBasisMeasurementEq complexWeight U T ∧
      PureInputBasisMeasurementEq complexWeight U V := by
  exact ⟨PureInputBasisMeasurementEq.refl U,
    PureInputBasisMeasurementEq.equivalence.1 U,
    PureInputBasisMeasurementEq.symm hUV,
    PureInputBasisMeasurementEq.trans hUV hVT,
    PureInputBasisMeasurementEq.of_exact hexact⟩

/-- Distribution equivalence, events, and deterministic pushforwards stay distinct. -/
theorem normalizedDistribution_api (a b c : ComplexState Bool)
    (hab : NormalizedDistributionEq complexWeight complexWeight_nonneg a b)
    (hbc : NormalizedDistributionEq complexWeight complexWeight_nonneg b c)
    (event : Finset Bool) (f : Bool → Bool) :
    NormalizedDistributionEq complexWeight complexWeight_nonneg a a ∧
      NormalizedDistributionEq complexWeight complexWeight_nonneg a a ∧
      NormalizedDistributionEq complexWeight complexWeight_nonneg b a ∧
      NormalizedDistributionEq complexWeight complexWeight_nonneg a c ∧
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).eventWeight
          event =
        (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg b).eventWeight
          event ∧
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).pushforward f =
        (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg b).pushforward f ∧
      (BasisWeightEq complexWeight a b ↔
        NormalizedDistributionEq complexWeight complexWeight_nonneg a b) ∧
      NormalizedDistributionEq complexWeight complexWeight_nonneg a b ∧
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).eventWeight
          event =
        (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg b).eventWeight
          event ∧
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).pushforward f =
        (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg b).pushforward f ∧
      ((FiniteDistribution.ofNormalizedState complexWeight
          complexWeight_nonneg a).pushforward f).weight true =
        ((FiniteDistribution.ofNormalizedState complexWeight
          complexWeight_nonneg b).pushforward f).weight true := by
  have hweight : BasisWeightEq complexWeight a b :=
    (basisWeightEq_iff_normalizedDistributionEq complexWeight
      complexWeight_nonneg a b).mpr hab
  exact ⟨NormalizedDistributionEq.refl a,
    NormalizedDistributionEq.equivalence.1 a,
    NormalizedDistributionEq.symm hab,
    NormalizedDistributionEq.trans hab hbc,
    NormalizedDistributionEq.eventWeight_eq hab event,
    NormalizedDistributionEq.pushforward_eq hab f,
    basisWeightEq_iff_normalizedDistributionEq complexWeight
      complexWeight_nonneg a b,
    BasisWeightEq.normalizedDistributionEq hweight,
    BasisWeightEq.eventWeight_eq hweight event,
    BasisWeightEq.pushforward_eq hweight f,
    BasisWeightEq.pushforward_weight_eq hweight f true⟩

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

/-- Exact circuit equality yields its genuinely fixed-input consequence. -/
theorem basisPreparation_fixedInputAgreement (b : BitBasis Bool)
    (input : BitBasis Bool → ℂ) :
    OutputWeightEqAt complexWeight
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool))
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool)) input :=
  (basisPreparation_exact b).outputWeightEqAt input

/-- Exact circuit equality yields its all-basis-input consequence separately. -/
theorem basisPreparation_basisAgreement (b : BitBasis Bool) :
    BasisMeasurementEq complexWeight
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool))
      (OrderedCircuit.eval
        ([basisPreparationGate (R := ℂ) b] : OrderedCircuit ℂ Bool)) :=
  (basisPreparation_exact b).basisMeasurementEq

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
#print axioms QuaternionicComputing.Semantics.CoreAudit.basisPreparation_fixedInputAgreement
#print axioms QuaternionicComputing.Semantics.CoreAudit.basisPreparation_basisAgreement
#print axioms QuaternionicComputing.Semantics.CoreAudit.basisPreparation_pureInputAgreement
