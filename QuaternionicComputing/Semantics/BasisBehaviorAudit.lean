module

public import QuaternionicComputing.Semantics.BasisBehaviorCircuit

/-!
# Certified basis-behavior audit

This non-root diagnostic leaf exercises the complete certified basis-behavior
API.  It also gives the strict vacuity witness required by Goal 2 Stage 5:
two explicit rational real orthogonal matrices have no phased basis transition
at all, and therefore have equal raw transition relations, while a named
computational-basis measurement probability differs.

The public root deliberately does not import this file.  In particular, the
raw relation counterexample is evidence that `BasisTransitionRelationEq` is a
diagnostic notion and cannot replace a certified permutation implementation.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.BasisBehaviorAudit

open QuaternionicComputing.Circuit

/-! ## Structural API consumers -/

/-- Complete consumer for the basis-ket and raw-transition diagnostic layer. -/
theorem rawTransition_api
    {R I : Type*} [Fintype I] [DecidableEq I] [NonAssocSemiring R]
    (unitPhase : R → Prop) (U V T : Matrix I I R) (x y : I)
    (hUV : BasisTransitionRelationEq unitPhase U V)
    (hVT : BasisTransitionRelationEq unitPhase V T)
    (hexact : ExactOperatorEq U V) :
    basisKet (R := R) x x = 1 ∧
      (BasisTransition unitPhase U x y ↔
        ∃ phase : R, unitPhase phase ∧
          ∀ z, U z x = if z = y then phase else 0) ∧
      BasisTransitionRelationEq unitPhase U U ∧
      BasisTransitionRelationEq unitPhase V U ∧
      BasisTransitionRelationEq unitPhase U T ∧
      BasisTransitionRelationEq unitPhase U U ∧
      BasisTransitionRelationEq unitPhase U V ∧
      (BasisTransition unitPhase U x y ↔
        ∃ phase : R, unitPhase phase ∧
          U *ᵥ basisKet (R := R) x =
            fun z ↦ if z = y then phase else 0) := by
  exact ⟨by simp [basisKet_apply],
    Iff.rfl,
    BasisTransitionRelationEq.refl U,
    BasisTransitionRelationEq.symm hUV,
    BasisTransitionRelationEq.trans hUV hVT,
    BasisTransitionRelationEq.equivalence.1 U,
    BasisTransitionRelationEq.of_exact hexact,
    basisTransition_iff_mulVec_basisKet unitPhase U x y⟩

/-- Complete consumer for generic certified permutation implementations. -/
theorem implementation_api
    {R I : Type*} [Semiring R] [DecidableEq I]
    {unitPhase : R → Prop} {U : Matrix I I R}
    {p q : Equiv.Perm I} (hone : unitPhase 1)
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hp : BasisPermutationImplementation unitPhase U p)
    (hq : BasisPermutationImplementation unitPhase U q) (x y : I)
    (htransition : BasisTransition unitPhase U x y) :
    BasisTransition unitPhase U x (p x) ∧
      BasisTransition unitPhase U x (p x) ∧
      (BasisTransition unitPhase U x y ↔ y = p x) ∧
      y = p x ∧
      p = q ∧
      BasisPermutationImplementation unitPhase
        (p.permMatrix R) p.symm := by
  exact ⟨hp.basisTransition x,
    hp.transition x,
    hp.basisTransition_iff hnonzero x y,
    hp.transition_target_unique hnonzero htransition,
    BasisPermutationImplementation.permutation_unique hnonzero hp hq,
    BasisPermutationImplementation.ofPermMatrix hone p⟩

/-- Complete consumer for certified-only same-basis behavior. -/
theorem sameBehavior_api
    {R I : Type*} [Zero R] [DecidableEq I]
    {unitPhase : R → Prop} {U V T : Matrix I I R}
    {p q r : Equiv.Perm I}
    {hU : BasisPermutationImplementation unitPhase U p}
    {hV : BasisPermutationImplementation unitPhase V q}
    {hT : BasisPermutationImplementation unitPhase T r}
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hUV : SameBasisBehavior hU hV)
    (hVT : SameBasisBehavior hV hT)
    (hexact : ExactOperatorEq U V) :
    SameBasisBehavior hU hU ∧
      SameBasisBehavior hV hU ∧
      SameBasisBehavior hU hT ∧
      BasisTransitionRelationEq unitPhase U V ∧
      SameBasisBehavior hU hV := by
  exact ⟨SameBasisBehavior.refl hU,
    SameBasisBehavior.symm hUV,
    SameBasisBehavior.trans hUV hVT,
    SameBasisBehavior.basisTransitionRelationEq hnonzero hUV,
    ExactOperatorEq.sameBasisBehavior hnonzero hU hV hexact⟩

/-- Consumer for recovery of a certified permutation from basis measurements. -/
theorem measurementDeterminesBehavior_api
    {R I : Type*} [Zero R] [DecidableEq I]
    {unitPhase : R → Prop} {weight : R → ℝ}
    {U V : Matrix I I R} {p q : Equiv.Perm I}
    (hzero : weight 0 = 0)
    (hunit : ∀ phase, unitPhase phase → weight phase = 1)
    (hU : BasisPermutationImplementation unitPhase U p)
    (hV : BasisPermutationImplementation unitPhase V q)
    (hmeasure : BasisMeasurementEq weight U V) :
    SameBasisBehavior hU hV :=
  BasisMeasurementEq.sameBasisBehavior hzero hunit hU hV hmeasure

/-- Equal certified permutations produce the correctly sided phase relations. -/
theorem scalarPhase_api
    {I : Type*} [DecidableEq I]
    {UR VR : Matrix I I ℝ} {UC VC : Matrix I I ℂ}
    {UQ VQ : Matrix I I ℍ[ℝ]}
    {pR qR pC qC pQ qQ : Equiv.Perm I}
    {hUR : RealBasisPermutationImplementation UR pR}
    {hVR : RealBasisPermutationImplementation VR qR}
    {hUC : ComplexBasisPermutationImplementation UC pC}
    {hVC : ComplexBasisPermutationImplementation VC qC}
    {hUQ : QuaternionBasisPermutationImplementation UQ pQ}
    {hVQ : QuaternionBasisPermutationImplementation VQ qQ}
    (hR : SameBasisBehavior hUR hVR)
    (hC : SameBasisBehavior hUC hVC)
    (hQ : SameBasisBehavior hUQ hVQ) :
    RealInputBasisSignEq UR VR ∧
      RealOutputBasisSignEq UR VR ∧
      ComplexInputBasisPhaseEq UC VC ∧
      ComplexOutputBasisPhaseEq UC VC ∧
      QuaternionInputRightPhaseEq UQ VQ ∧
      QuaternionOutputLeftPhaseEq UQ VQ :=
  ⟨hR.realInputBasisSignEq,
    hR.realOutputBasisSignEq,
    hC.complexInputBasisPhaseEq,
    hC.complexOutputBasisPhaseEq,
    hQ.quaternionInputRightPhaseEq,
    hQ.quaternionOutputLeftPhaseEq⟩

/--
Complete consumer for the certified-class converses and exact equivalences in
the real, complex, and quaternionic scalar specializations.
-/
theorem certifiedEquivalences_api
    {I : Type*} [DecidableEq I]
    {UR VR : Matrix I I ℝ} {UC VC : Matrix I I ℂ}
    {UQ VQ : Matrix I I ℍ[ℝ]}
    {pR qR pC qC pQ qQ : Equiv.Perm I}
    {hUR : RealBasisPermutationImplementation UR pR}
    {hVR : RealBasisPermutationImplementation VR qR}
    {hUC : ComplexBasisPermutationImplementation UC pC}
    {hVC : ComplexBasisPermutationImplementation VC qC}
    {hUQ : QuaternionBasisPermutationImplementation UQ pQ}
    {hVQ : QuaternionBasisPermutationImplementation VQ qQ}
    (hR : SameBasisBehavior hUR hVR)
    (hC : SameBasisBehavior hUC hVC)
    (hQ : SameBasisBehavior hUQ hVQ) :
    SameBasisBehavior hUR hVR ∧
      SameBasisBehavior hUC hVC ∧
      SameBasisBehavior hUQ hVQ ∧
      SameBasisBehavior hUR hVR ∧
      SameBasisBehavior hUC hVC ∧
      SameBasisBehavior hUQ hVQ ∧
      SameBasisBehavior hUR hVR ∧
      SameBasisBehavior hUC hVC ∧
      SameBasisBehavior hUQ hVQ ∧
      BasisMeasurementEq State.realWeight UR VR ∧
      BasisMeasurementEq State.complexWeight UC VC ∧
      BasisMeasurementEq State.quaternionWeight UQ VQ ∧
      (SameBasisBehavior hUR hVR ↔ RealInputBasisSignEq UR VR) ∧
      (SameBasisBehavior hUR hVR ↔ RealOutputBasisSignEq UR VR) ∧
      (SameBasisBehavior hUR hVR ↔
        BasisMeasurementEq State.realWeight UR VR) ∧
      (SameBasisBehavior hUC hVC ↔ ComplexInputBasisPhaseEq UC VC) ∧
      (SameBasisBehavior hUC hVC ↔ ComplexOutputBasisPhaseEq UC VC) ∧
      (SameBasisBehavior hUC hVC ↔
        BasisMeasurementEq State.complexWeight UC VC) ∧
      (SameBasisBehavior hUQ hVQ ↔ QuaternionInputRightPhaseEq UQ VQ) ∧
      (SameBasisBehavior hUQ hVQ ↔ QuaternionOutputLeftPhaseEq UQ VQ) ∧
      (SameBasisBehavior hUQ hVQ ↔
        BasisMeasurementEq State.quaternionWeight UQ VQ) ∧
      SameBasisBehavior hUR hUR ∧
      SameBasisBehavior hUC hUC ∧
      SameBasisBehavior hUQ hUQ ∧
      SameBasisBehavior hUR hUR ∧
      SameBasisBehavior hUC hUC ∧
      SameBasisBehavior hUQ hUQ := by
  have hRin := hR.realInputBasisSignEq
  have hRout := hR.realOutputBasisSignEq
  have hCin := hC.complexInputBasisPhaseEq
  have hCout := hC.complexOutputBasisPhaseEq
  have hQin := hQ.quaternionInputRightPhaseEq
  have hQout := hQ.quaternionOutputLeftPhaseEq
  have hRm := hR.realBasisMeasurementEq
  have hCm := hC.complexBasisMeasurementEq
  have hQm := hQ.quaternionBasisMeasurementEq
  exact ⟨hRm.realSameBasisBehavior hUR hVR,
    hCm.complexSameBasisBehavior hUC hVC,
    hQm.quaternionSameBasisBehavior hUQ hVQ,
    hRin.sameBasisBehavior hUR hVR,
    hCin.sameBasisBehavior hUC hVC,
    hQin.sameBasisBehavior hUQ hVQ,
    hRout.sameBasisBehavior hUR hVR,
    hCout.sameBasisBehavior hUC hVC,
    hQout.sameBasisBehavior hUQ hVQ,
    hRm, hCm, hQm,
    sameBasisBehavior_iff_realInputBasisSignEq hUR hVR,
    sameBasisBehavior_iff_realOutputBasisSignEq hUR hVR,
    sameBasisBehavior_iff_realBasisMeasurementEq hUR hVR,
    sameBasisBehavior_iff_complexInputBasisPhaseEq hUC hVC,
    sameBasisBehavior_iff_complexOutputBasisPhaseEq hUC hVC,
    sameBasisBehavior_iff_complexBasisMeasurementEq hUC hVC,
    sameBasisBehavior_iff_quaternionInputRightPhaseEq hUQ hVQ,
    sameBasisBehavior_iff_quaternionOutputLeftPhaseEq hUQ hVQ,
    sameBasisBehavior_iff_quaternionBasisMeasurementEq hUQ hVQ,
    ExactOperatorEq.realSameBasisBehavior (ExactOperatorEq.refl UR) hUR hUR,
    ExactOperatorEq.complexSameBasisBehavior (ExactOperatorEq.refl UC) hUC hUC,
    ExactOperatorEq.quaternionSameBasisBehavior (ExactOperatorEq.refl UQ) hUQ hUQ,
    RealGlobalSignEq.sameBasisBehavior (RealGlobalSignEq.refl UR) hUR hUR,
    ComplexGlobalPhaseEq.sameBasisBehavior (ComplexGlobalPhaseEq.refl UC) hUC hUC,
    QuaternionCentralSignEq.sameBasisBehavior
      (QuaternionCentralSignEq.refl UQ) hUQ hUQ⟩

/-- Concrete consumers for all three scalar predicates and implementation aliases. -/
theorem scalarImplementation_api (p : Equiv.Perm Bool) :
    RealUnitSign 1 ∧
      ComplexUnitPhase 1 ∧
      QuaternionUnitPhase 1 ∧
      (1 : ℝ) ≠ 0 ∧
      (1 : ℂ) ≠ 0 ∧
      (1 : ℍ[ℝ]) ≠ 0 ∧
      RealBasisPermutationImplementation
        (p.permMatrix ℝ) p.symm ∧
      ComplexBasisPermutationImplementation
        (p.permMatrix ℂ) p.symm ∧
      QuaternionBasisPermutationImplementation
        (p.permMatrix ℍ[ℝ]) p.symm := by
  exact ⟨realUnitSign_one,
    complexUnitPhase_one,
    quaternionUnitPhase_one,
    realUnitSign_ne_zero realUnitSign_one,
    complexUnitPhase_ne_zero complexUnitPhase_one,
    quaternionUnitPhase_ne_zero quaternionUnitPhase_one,
    BasisPermutationImplementation.ofPermMatrix realUnitSign_one p,
    BasisPermutationImplementation.ofPermMatrix complexUnitPhase_one p,
    BasisPermutationImplementation.ofPermMatrix quaternionUnitPhase_one p⟩

/-- Concrete consumers for the generic and three scalar unitary bundles. -/
theorem certifiedOperator_api (p : Equiv.Perm Bool) :
    (∃ op : BasisClassicalUnitaryOperator ℝ Bool RealUnitSign,
        op.matrix = p.permMatrix ℝ ∧ op.permutation = p.symm) ∧
      (∃ op : RealBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : ComplexBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : QuaternionBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) := by
  exact ⟨⟨BasisClassicalUnitaryOperator.ofPermMatrix realUnitSign_one p,
      rfl, rfl⟩,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix realUnitSign_one p, rfl⟩,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix complexUnitPhase_one p, rfl⟩,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix quaternionUnitPhase_one p, rfl⟩⟩

/-- Complete consumer for certified unitary-bundle behavior and its laws. -/
theorem bundledBehavior_api
    {R I : Type*} [Semiring R] [StarRing R] [Fintype I] [DecidableEq I]
    {unitPhase : R → Prop}
    (A B C : BasisClassicalUnitaryOperator R I unitPhase)
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hAB : BasisClassicalUnitaryOperator.SameBasisBehavior A B)
    (hBC : BasisClassicalUnitaryOperator.SameBasisBehavior B C)
    (hmatrix : A.matrix = B.matrix) :
    (BasisClassicalUnitaryOperator.SameBasisBehavior A B ↔
        A.permutation = B.permutation) ∧
      BasisClassicalUnitaryOperator.SameBasisBehavior A A ∧
      BasisClassicalUnitaryOperator.SameBasisBehavior B A ∧
      BasisClassicalUnitaryOperator.SameBasisBehavior A C ∧
      BasisClassicalUnitaryOperator.SameBasisBehavior A A ∧
      BasisClassicalUnitaryOperator.SameBasisBehavior A B ∧
      BasisTransitionRelationEq unitPhase A.matrix B.matrix := by
  exact ⟨BasisClassicalUnitaryOperator.sameBasisBehavior_iff_permutation_eq A B,
    BasisClassicalUnitaryOperator.SameBasisBehavior.refl A,
    BasisClassicalUnitaryOperator.SameBasisBehavior.symm hAB,
    BasisClassicalUnitaryOperator.SameBasisBehavior.trans hAB hBC,
    BasisClassicalUnitaryOperator.SameBasisBehavior.equivalence.1 A,
    BasisClassicalUnitaryOperator.sameBasisBehavior_of_matrix_eq
      hnonzero A B hmatrix,
    BasisClassicalUnitaryOperator.basisTransitionRelationEq hnonzero hAB⟩

/-- Complete consumer for scalar-specialized permutation and bundle constructors. -/
theorem specializedConstructors_api (p : Equiv.Perm Bool) :
    RealBasisPermutationImplementation (p.permMatrix ℝ) p.symm ∧
      ComplexBasisPermutationImplementation (p.permMatrix ℂ) p.symm ∧
      QuaternionBasisPermutationImplementation (p.permMatrix ℍ[ℝ]) p.symm ∧
      p.symm = p.symm ∧
      p.symm = p.symm ∧
      p.symm = p.symm ∧
      (RealBasisClassicalUnitaryOperator.ofPermMatrix p).permutation = p.symm ∧
      (ComplexBasisClassicalUnitaryOperator.ofPermMatrix p).permutation = p.symm ∧
      (QuaternionBasisClassicalUnitaryOperator.ofPermMatrix p).permutation =
        p.symm := by
  let hR := RealBasisPermutationImplementation.ofPermMatrix p
  let hC := ComplexBasisPermutationImplementation.ofPermMatrix p
  let hQ := QuaternionBasisPermutationImplementation.ofPermMatrix p
  exact ⟨hR, hC, hQ,
    RealBasisPermutationImplementation.permutation_unique hR hR,
    ComplexBasisPermutationImplementation.permutation_unique hC hC,
    QuaternionBasisPermutationImplementation.permutation_unique hQ hQ,
    rfl, rfl, rfl⟩

/-! ## Empty-index and nontrivial-permutation checks -/

/-- Empty index types support a unique certified permutation without a hidden inhabitant. -/
theorem emptyIndex_certified :
    (∀ p : Equiv.Perm Empty, p = Equiv.refl Empty) ∧
      Nonempty (RealBasisClassicalUnitaryOperator Empty) ∧
      Nonempty (ComplexBasisClassicalUnitaryOperator Empty) ∧
      Nonempty (QuaternionBasisClassicalUnitaryOperator Empty) := by
  refine ⟨?_,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix
      realUnitSign_one (Equiv.refl Empty)⟩,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix
      complexUnitPhase_one (Equiv.refl Empty)⟩,
    ⟨BasisClassicalUnitaryOperator.ofPermMatrix
      quaternionUnitPhase_one (Equiv.refl Empty)⟩⟩
  intro p
  apply Equiv.ext
  intro x
  exact x.elim

/-- A nonidentity Bool permutation has certified real, complex, and quaternionic operators. -/
theorem boolSwap_certified :
    let p : Equiv.Perm Bool := Equiv.swap false true
    p ≠ Equiv.refl Bool ∧
      (∃ op : RealBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : ComplexBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : QuaternionBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) := by
  dsimp only
  refine ⟨?_, (certifiedOperator_api (Equiv.swap false true)).2⟩
  intro h
  have hfalse := congrArg (fun e : Equiv.Perm Bool ↦ e false) h
  simp at hfalse

/-! ## Circuit API consumers -/

/-- Complete consumer for generic certified circuits and their behavior relation. -/
theorem circuitBehavior_api
    {R W : Type*} [Semiring R] [StarRing R] [Fintype W]
    {unitPhase : R → Prop}
    (C D E : BasisClassicalCircuit R W unitPhase)
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hCD : SameCircuitBasisBehavior C D)
    (hDE : SameCircuitBasisBehavior D E)
    (hexact : ExactCircuitEq C.circuit D.circuit) :
    OrderedCircuit.eval C.circuit ∈
        unitary (Matrix (BitBasis W) (BitBasis W) R) ∧
      C.toOperator.matrix = OrderedCircuit.eval C.circuit ∧
      C.toOperator.permutation = C.permutation ∧
      (SameCircuitBasisBehavior C D ↔ C.permutation = D.permutation) ∧
      SameCircuitBasisBehavior C C ∧
      SameCircuitBasisBehavior D C ∧
      SameCircuitBasisBehavior C E ∧
      SameCircuitBasisBehavior C C ∧
      SameCircuitBasisBehavior C D := by
  exact ⟨C.eval_mem_unitary,
    C.toOperator_matrix,
    C.toOperator_permutation,
    SameCircuitBasisBehavior.iff_permutation_eq,
    SameCircuitBasisBehavior.refl C,
    SameCircuitBasisBehavior.symm hCD,
    SameCircuitBasisBehavior.trans hCD hDE,
    SameCircuitBasisBehavior.equivalence.1 C,
    ExactCircuitEq.sameCircuitBasisBehavior hexact hnonzero⟩

/-- The three scalar circuit aliases consume their specialized exact-evaluation bridges. -/
theorem scalarCircuit_api
    {W : Type*} [Fintype W]
    (CR DR : RealBasisClassicalCircuit W)
    (CC DC : ComplexBasisClassicalCircuit W)
    (CQ DQ : QuaternionBasisClassicalCircuit W)
    (hR : ExactCircuitEq CR.circuit DR.circuit)
    (hC : ExactCircuitEq CC.circuit DC.circuit)
    (hQ : ExactCircuitEq CQ.circuit DQ.circuit) :
    SameCircuitBasisBehavior CR DR ∧
      SameCircuitBasisBehavior CC DC ∧
      SameCircuitBasisBehavior CQ DQ ∧
      (SameCircuitBasisBehavior CR DR ↔
        RealCircuitInputBasisSignEq CR.circuit DR.circuit) ∧
      (SameCircuitBasisBehavior CR DR ↔
        RealCircuitOutputBasisSignEq CR.circuit DR.circuit) ∧
      (SameCircuitBasisBehavior CR DR ↔
        BasisMeasurementEq State.realWeight CR.circuit.eval DR.circuit.eval) ∧
      (SameCircuitBasisBehavior CC DC ↔
        ComplexCircuitInputBasisPhaseEq CC.circuit DC.circuit) ∧
      (SameCircuitBasisBehavior CC DC ↔
        ComplexCircuitOutputBasisPhaseEq CC.circuit DC.circuit) ∧
      (SameCircuitBasisBehavior CC DC ↔
        BasisMeasurementEq State.complexWeight CC.circuit.eval DC.circuit.eval) ∧
      (SameCircuitBasisBehavior CQ DQ ↔
        QuaternionCircuitInputRightPhaseEq CQ.circuit DQ.circuit) ∧
      (SameCircuitBasisBehavior CQ DQ ↔
        QuaternionCircuitOutputLeftPhaseEq CQ.circuit DQ.circuit) ∧
      (SameCircuitBasisBehavior CQ DQ ↔
        BasisMeasurementEq State.quaternionWeight CQ.circuit.eval
          DQ.circuit.eval) ∧
      SameCircuitBasisBehavior CR CR ∧
      SameCircuitBasisBehavior CC CC ∧
      SameCircuitBasisBehavior CQ CQ :=
  ⟨hR.realSameCircuitBasisBehavior,
    hC.complexSameCircuitBasisBehavior,
    hQ.quaternionSameCircuitBasisBehavior,
    SameCircuitBasisBehavior.iff_realCircuitInputBasisSignEq,
    SameCircuitBasisBehavior.iff_realCircuitOutputBasisSignEq,
    SameCircuitBasisBehavior.iff_realBasisMeasurementEq,
    SameCircuitBasisBehavior.iff_complexCircuitInputBasisPhaseEq,
    SameCircuitBasisBehavior.iff_complexCircuitOutputBasisPhaseEq,
    SameCircuitBasisBehavior.iff_complexBasisMeasurementEq,
    SameCircuitBasisBehavior.iff_quaternionCircuitInputRightPhaseEq,
    SameCircuitBasisBehavior.iff_quaternionCircuitOutputLeftPhaseEq,
    SameCircuitBasisBehavior.iff_quaternionBasisMeasurementEq,
    RealCircuitGlobalSignEq.sameCircuitBasisBehavior
      (RealCircuitGlobalSignEq.refl CR.circuit),
    ComplexCircuitGlobalPhaseEq.sameCircuitBasisBehavior
      (ComplexCircuitGlobalPhaseEq.refl CC.circuit),
    QuaternionCircuitCentralSignEq.sameCircuitBasisBehavior
      (QuaternionCircuitCentralSignEq.refl CQ.circuit)⟩

/-- Complete consumer for the generic certified identity circuit. -/
theorem emptyCircuit_api
    {R W : Type*} [Semiring R] [StarRing R] [Fintype W]
    (unitPhase : R → Prop) (hone : unitPhase 1) :
    let C := emptyBasisClassicalCircuit (W := W) unitPhase hone
    C.circuit = [] ∧
      C.permutation = Equiv.refl (BitBasis W) ∧
      OrderedCircuit.eval C.circuit ∈
        unitary (Matrix (BitBasis W) (BitBasis W) R) := by
  exact ⟨emptyBasisClassicalCircuit_circuit unitPhase hone,
    emptyBasisClassicalCircuit_permutation unitPhase hone,
    BasisClassicalCircuit.eval_mem_unitary _⟩

/-- Complete consumer for the matrix, gate, and singleton-circuit XOR certificates. -/
theorem basisPreparation_api
    {R W : Type*} [Semiring R] [StarRing R] [Fintype W]
    (unitPhase : R → Prop) (hone : unitPhase 1)
    (b x y : BitBasis W) :
    BasisPermutationImplementation unitPhase
        (basisPreparationMatrix (R := R) b) (xorBasisEquiv b) ∧
      (basisPreparationOperator unitPhase hone b).matrix =
        basisPreparationMatrix (R := R) b ∧
      (basisPreparationOperator unitPhase hone b).permutation =
        xorBasisEquiv b ∧
      BasisPermutationImplementation unitPhase
        (basisPreparationGate (R := R) b).denote (xorBasisEquiv b) ∧
      (basisPreparationCircuit unitPhase hone b).circuit =
        [basisPreparationGate (R := R) b] ∧
      (basisPreparationCircuit unitPhase hone b).permutation =
        xorBasisEquiv b ∧
      BasisTransition unitPhase
        (OrderedCircuit.eval
          (basisPreparationCircuit unitPhase hone b).circuit)
        x (xorBasisEquiv b x) ∧
      OrderedCircuit.eval
          (basisPreparationCircuit unitPhase hone b).circuit y x =
        (if y = xorBasisEquiv b x then 1 else 0) ∧
      OrderedCircuit.eval
          (basisPreparationCircuit unitPhase hone b).circuit *ᵥ
          basisColumn (R := R) (groundBasis W) =
        basisColumn (R := R) b := by
  exact ⟨basisPreparationMatrixImplementation unitPhase hone b,
    basisPreparationOperator_matrix unitPhase hone b,
    basisPreparationOperator_permutation unitPhase hone b,
    basisPreparationGateImplementation unitPhase hone b,
    basisPreparationCircuit_circuit unitPhase hone b,
    basisPreparationCircuit_permutation unitPhase hone b,
    basisPreparationCircuit_basisTransition unitPhase hone b x,
    basisPreparationCircuit_eval_entry unitPhase hone b x y,
    basisPreparationCircuit_mulVec_ground unitPhase hone b⟩

/-- The zero-wire circuit has one basis assignment and genuine all-input behavior. -/
theorem zeroWire_circuit_api :
    let emptyBits : BitBasis Empty := fun e ↦ nomatch e
    let realIdentity : RealBasisClassicalCircuit Empty :=
      emptyBasisClassicalCircuit RealUnitSign realUnitSign_one
    let complexPrep : ComplexBasisClassicalCircuit Empty :=
      basisPreparationCircuit ComplexUnitPhase complexUnitPhase_one emptyBits
    let quaternionPrep : QuaternionBasisClassicalCircuit Empty :=
      basisPreparationCircuit QuaternionUnitPhase quaternionUnitPhase_one emptyBits
    realIdentity.permutation = Equiv.refl (BitBasis Empty) ∧
      complexPrep.permutation = xorBasisEquiv emptyBits ∧
      quaternionPrep.permutation = xorBasisEquiv emptyBits ∧
      SameCircuitBasisBehavior complexPrep complexPrep ∧
      OrderedCircuit.eval complexPrep.circuit emptyBits emptyBits = 1 ∧
      OrderedCircuit.eval complexPrep.circuit *ᵥ
          basisColumn (R := ℂ) (groundBasis Empty) =
        basisColumn (R := ℂ) emptyBits := by
  dsimp only
  refine ⟨emptyBasisClassicalCircuit_permutation _ _,
    basisPreparationCircuit_permutation _ _ _,
    basisPreparationCircuit_permutation _ _ _,
    SameCircuitBasisBehavior.refl _, ?_, ?_⟩
  · rw [show OrderedCircuit.eval
        (basisPreparationCircuit ComplexUnitPhase complexUnitPhase_one
          (fun e : Empty ↦ nomatch e)).circuit
        (fun e : Empty ↦ nomatch e) (fun e : Empty ↦ nomatch e) =
        if (fun e : Empty ↦ nomatch e) =
            xorBasisEquiv (fun e : Empty ↦ nomatch e)
              (fun e : Empty ↦ nomatch e)
          then 1 else 0 by
      exact basisPreparationCircuit_eval_entry _ _ _ _ _]
    exact if_pos (Subsingleton.elim _ _)
  · exact basisPreparationCircuit_mulVec_ground _ _ _

/-! ## Rational unitary vacuity witness -/

/-- The real rational rotation `[[3/5,4/5],[-4/5,3/5]]`. -/
def realRotation35 : Matrix Bool Bool ℝ
  | false, false => 3 / 5
  | false, true => 4 / 5
  | true, false => -4 / 5
  | true, true => 3 / 5

/-- The real rational rotation `[[5/13,12/13],[-12/13,5/13]]`. -/
def realRotation513 : Matrix Bool Bool ℝ
  | false, false => 5 / 13
  | false, true => 12 / 13
  | true, false => -12 / 13
  | true, true => 5 / 13

/-- The `3/5`--`4/5` rational rotation is exactly unitary. -/
theorem realRotation35_mem_unitary :
    realRotation35 ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, realRotation35, Fintype.univ_bool]

/-- The `5/13`--`12/13` rational rotation is exactly unitary. -/
theorem realRotation513_mem_unitary :
    realRotation513 ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [Matrix.mul_apply, realRotation513, Fintype.univ_bool]

/-- Every entry of the `3/5`--`4/5` rotation is nonzero. -/
theorem realRotation35_entry_ne_zero (y x : Bool) :
    realRotation35 y x ≠ 0 := by
  cases y <;> cases x <;> norm_num [realRotation35]

/-- Every entry of the `5/13`--`12/13` rotation is nonzero. -/
theorem realRotation513_entry_ne_zero (y x : Bool) :
    realRotation513 y x ≠ 0 := by
  cases y <;> cases x <;> norm_num [realRotation513]

/-- The first rotation never maps a basis input to any phased basis ket. -/
theorem realRotation35_no_transition (x y : Bool) :
    ¬ BasisTransition RealUnitSign realRotation35 x y := by
  rintro ⟨phase, hphase, hentry⟩
  cases x <;> cases y
  · have h := hentry true
    norm_num [realRotation35] at h
  · have h := hentry false
    norm_num [realRotation35] at h
  · have h := hentry true
    norm_num [realRotation35] at h
  · have h := hentry false
    norm_num [realRotation35] at h

/-- The second rotation never maps a basis input to any phased basis ket. -/
theorem realRotation513_no_transition (x y : Bool) :
    ¬ BasisTransition RealUnitSign realRotation513 x y := by
  rintro ⟨phase, hphase, hentry⟩
  cases x <;> cases y
  · have h := hentry true
    norm_num [realRotation513] at h
  · have h := hentry false
    norm_num [realRotation513] at h
  · have h := hentry true
    norm_num [realRotation513] at h
  · have h := hentry false
    norm_num [realRotation513] at h

/-- Despite unitarity, the first rotation has no certified basis permutation. -/
theorem realRotation35_no_implementation :
    ¬ ∃ p, RealBasisPermutationImplementation realRotation35 p := by
  rintro ⟨p, hp⟩
  exact realRotation35_no_transition false (p false)
    (hp.basisTransition false)

/-- Despite unitarity, the second rotation has no certified basis permutation. -/
theorem realRotation513_no_implementation :
    ¬ ∃ p, RealBasisPermutationImplementation realRotation513 p := by
  rintro ⟨p, hp⟩
  exact realRotation513_no_transition false (p false)
    (hp.basisTransition false)

/-- Both empty raw transition relations are extensionally equal. -/
theorem rotations_transition_relation_eq :
    BasisTransitionRelationEq RealUnitSign realRotation35 realRotation513 := by
  intro x y
  constructor
  · exact (realRotation35_no_transition x y).elim
  · exact (realRotation513_no_transition x y).elim

/-- The two rotations disagree on the explicit `false → false` basis weight. -/
theorem rotations_not_basisMeasurementEq :
    ¬ BasisMeasurementEq State.realWeight realRotation35 realRotation513 := by
  intro h
  have h00 := h false false
  norm_num [State.realWeight, realRotation35, realRotation513] at h00

/--
The complete physically relevant vacuity witness: unitary, everywhere nonzero
matrices can have equal empty raw transition relations but unequal basis
measurement probabilities and no certified classical behavior.
-/
theorem unitary_vacuity_witness :
    realRotation35 ∈ unitary (Matrix Bool Bool ℝ) ∧
      realRotation513 ∈ unitary (Matrix Bool Bool ℝ) ∧
      (∀ y x, realRotation35 y x ≠ 0) ∧
      (∀ y x, realRotation513 y x ≠ 0) ∧
      (¬ ∃ p, RealBasisPermutationImplementation realRotation35 p) ∧
      (¬ ∃ p, RealBasisPermutationImplementation realRotation513 p) ∧
      BasisTransitionRelationEq RealUnitSign realRotation35 realRotation513 ∧
      ¬ BasisMeasurementEq State.realWeight realRotation35 realRotation513 :=
  ⟨realRotation35_mem_unitary, realRotation513_mem_unitary,
    realRotation35_entry_ne_zero, realRotation513_entry_ne_zero,
    realRotation35_no_implementation, realRotation513_no_implementation,
    rotations_transition_relation_eq, rotations_not_basisMeasurementEq⟩

/-! ## Local axiom endpoints -/

#print axioms rawTransition_api
#print axioms implementation_api
#print axioms sameBehavior_api
#print axioms measurementDeterminesBehavior_api
#print axioms scalarPhase_api
#print axioms certifiedEquivalences_api
#print axioms scalarImplementation_api
#print axioms certifiedOperator_api
#print axioms bundledBehavior_api
#print axioms specializedConstructors_api
#print axioms emptyIndex_certified
#print axioms boolSwap_certified
#print axioms circuitBehavior_api
#print axioms scalarCircuit_api
#print axioms emptyCircuit_api
#print axioms basisPreparation_api
#print axioms zeroWire_circuit_api
#print axioms unitary_vacuity_witness

end QuaternionicComputing.Semantics.BasisBehaviorAudit
