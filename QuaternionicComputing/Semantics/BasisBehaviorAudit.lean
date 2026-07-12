module

public import QuaternionicComputing.Semantics.BasisBehavior

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

/-! ## Empty-index and nontrivial-permutation checks -/

/-- Empty index types admit a unique certified permutation without a hidden inhabitant. -/
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
    (∃ op : RealBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : ComplexBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) ∧
      (∃ op : QuaternionBasisClassicalUnitaryOperator Bool,
        op.permutation = p.symm) := by
  exact (certifiedOperator_api (Equiv.swap false true)).2

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
#print axioms scalarImplementation_api
#print axioms certifiedOperator_api
#print axioms emptyIndex_certified
#print axioms boolSwap_certified
#print axioms unitary_vacuity_witness

end QuaternionicComputing.Semantics.BasisBehaviorAudit
