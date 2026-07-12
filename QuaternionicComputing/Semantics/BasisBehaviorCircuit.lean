module

public import QuaternionicComputing.Semantics.BasisBehavior
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit
public import QuaternionicComputing.Circuit.BasisPreparation

/-!
# Certified computational-basis behavior of ordered circuits

This leaf lifts certified classical basis behavior from matrices to
`Circuit.OrderedCircuit` through the chronological evaluator.  A certificate
stores local unitarity of the gate list and an all-input basis-permutation
certificate for its evaluated matrix.  It does not identify gate lists,
schedules, or resource counts.

The known-basis preparation construction is a genuine all-input consumer: its
matrix, full-support gate, and singleton circuit implement XOR by the chosen
basis assignment.  The final ground-column theorem is kept separately because
it concerns only the one known external input `groundBasis W`.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

open QuaternionicComputing.Circuit

universe u v

/--
An ordered circuit whose evaluated matrix is unitary and implements one
certified computational-basis permutation.  Local unitarity is stored at the
gate-list level; evaluated unitarity is derived from it.
-/
structure BasisClassicalCircuit (R : Type u) (W : Type v)
    [Semiring R] [StarRing R] [Fintype W] (unitPhase : R → Prop) where
  /-- The chronological gate list. -/
  circuit : OrderedCircuit R W
  /-- Every local gate matrix is unitary. -/
  locallyUnitary : circuit.IsLocallyUnitary
  /-- The certified permutation of computational-basis assignments. -/
  permutation : Equiv.Perm (BitBasis W)
  /-- All-input basis behavior of the evaluated matrix. -/
  implementation :
    BasisPermutationImplementation unitPhase (OrderedCircuit.eval circuit) permutation

namespace BasisClassicalCircuit

variable {R : Type u} {W : Type v} [Semiring R] [StarRing R] [Fintype W]
variable {unitPhase : R → Prop}

/-- The evaluation of a certified basis-classical circuit is unitary. -/
theorem eval_mem_unitary (C : BasisClassicalCircuit R W unitPhase) :
    OrderedCircuit.eval C.circuit ∈
      unitary (Matrix (BitBasis W) (BitBasis W) R) :=
  OrderedCircuit.eval_mem_unitary C.locallyUnitary

/-- Forget circuit syntax while retaining its evaluated certified operator. -/
def toOperator (C : BasisClassicalCircuit R W unitPhase) :
    BasisClassicalUnitaryOperator R (BitBasis W) unitPhase where
  matrix := OrderedCircuit.eval C.circuit
  mem_unitary := C.eval_mem_unitary
  permutation := C.permutation
  implementation := C.implementation

@[simp]
theorem toOperator_matrix (C : BasisClassicalCircuit R W unitPhase) :
    C.toOperator.matrix = OrderedCircuit.eval C.circuit :=
  rfl

@[simp]
theorem toOperator_permutation (C : BasisClassicalCircuit R W unitPhase) :
    C.toOperator.permutation = C.permutation :=
  rfl

end BasisClassicalCircuit

/-- Real certified basis-classical circuits, with signs as column phases. -/
abbrev RealBasisClassicalCircuit (W : Type v) [Fintype W] :=
  BasisClassicalCircuit ℝ W RealUnitSign

/-- Complex certified basis-classical circuits, with unit complex column phases. -/
abbrev ComplexBasisClassicalCircuit (W : Type v) [Fintype W] :=
  BasisClassicalCircuit ℂ W ComplexUnitPhase

/-- Quaternionic certified basis-classical circuits, with unit right column phases. -/
abbrev QuaternionBasisClassicalCircuit (W : Type v) [Fintype W] :=
  BasisClassicalCircuit ℍ[ℝ] W QuaternionUnitPhase

/-- Two certified circuits have the same classical behavior exactly when their certificates
carry the same computational-basis permutation. -/
def SameCircuitBasisBehavior {R : Type u} {W : Type v}
    [Semiring R] [StarRing R] [Fintype W] {unitPhase : R → Prop}
    (C D : BasisClassicalCircuit R W unitPhase) : Prop :=
  SameBasisBehavior C.implementation D.implementation

namespace SameCircuitBasisBehavior

variable {R : Type u} {W : Type v} [Semiring R] [StarRing R] [Fintype W]
variable {unitPhase : R → Prop}
variable {C D E : BasisClassicalCircuit R W unitPhase}

@[simp]
theorem iff_permutation_eq :
    SameCircuitBasisBehavior C D ↔ C.permutation = D.permutation :=
  Iff.rfl

@[refl]
theorem refl (C : BasisClassicalCircuit R W unitPhase) :
    SameCircuitBasisBehavior C C :=
  rfl

@[symm]
theorem symm (h : SameCircuitBasisBehavior C D) :
    SameCircuitBasisBehavior D C :=
  Eq.symm h

@[trans]
theorem trans (hCD : SameCircuitBasisBehavior C D)
    (hDE : SameCircuitBasisBehavior D E) :
    SameCircuitBasisBehavior C E :=
  Eq.trans hCD hDE

/-- Same certified circuit behavior is an equivalence relation. -/
theorem equivalence :
    Equivalence (@SameCircuitBasisBehavior R W _ _ _ unitPhase) :=
  ⟨refl, symm, trans⟩

/-! ### Exact scalar characterizations on certified circuits -/

/-- On certified real circuits, same permutation is exactly input-column sign equality. -/
theorem iff_realCircuitInputBasisSignEq {W : Type v} [Fintype W]
    {C D : RealBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      RealCircuitInputBasisSignEq C.circuit D.circuit :=
  sameBasisBehavior_iff_realInputBasisSignEq C.implementation D.implementation

/-- On certified real circuits, same permutation is exactly output-row sign equality. -/
theorem iff_realCircuitOutputBasisSignEq {W : Type v} [Fintype W]
    {C D : RealBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      RealCircuitOutputBasisSignEq C.circuit D.circuit :=
  sameBasisBehavior_iff_realOutputBasisSignEq C.implementation D.implementation

/-- On certified real circuits, same permutation is exactly basis-measurement equality. -/
theorem iff_realBasisMeasurementEq {W : Type v} [Fintype W]
    {C D : RealBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      BasisMeasurementEq State.realWeight C.circuit.eval D.circuit.eval :=
  sameBasisBehavior_iff_realBasisMeasurementEq C.implementation D.implementation

/-- On certified complex circuits, same permutation is exactly input-column phase equality. -/
theorem iff_complexCircuitInputBasisPhaseEq {W : Type v} [Fintype W]
    {C D : ComplexBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      ComplexCircuitInputBasisPhaseEq C.circuit D.circuit :=
  sameBasisBehavior_iff_complexInputBasisPhaseEq C.implementation D.implementation

/-- On certified complex circuits, same permutation is exactly output-row phase equality. -/
theorem iff_complexCircuitOutputBasisPhaseEq {W : Type v} [Fintype W]
    {C D : ComplexBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      ComplexCircuitOutputBasisPhaseEq C.circuit D.circuit :=
  sameBasisBehavior_iff_complexOutputBasisPhaseEq C.implementation D.implementation

/-- On certified complex circuits, same permutation is exactly basis-measurement equality. -/
theorem iff_complexBasisMeasurementEq {W : Type v} [Fintype W]
    {C D : ComplexBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      BasisMeasurementEq State.complexWeight C.circuit.eval D.circuit.eval :=
  sameBasisBehavior_iff_complexBasisMeasurementEq C.implementation D.implementation

/--
On certified quaternionic circuits, same permutation is exactly input-column
right-phase equality.
-/
theorem iff_quaternionCircuitInputRightPhaseEq {W : Type v} [Fintype W]
    {C D : QuaternionBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      QuaternionCircuitInputRightPhaseEq C.circuit D.circuit :=
  sameBasisBehavior_iff_quaternionInputRightPhaseEq
    C.implementation D.implementation

/--
On certified quaternionic circuits, same permutation is exactly output-row
left-phase equality.
-/
theorem iff_quaternionCircuitOutputLeftPhaseEq {W : Type v} [Fintype W]
    {C D : QuaternionBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      QuaternionCircuitOutputLeftPhaseEq C.circuit D.circuit :=
  sameBasisBehavior_iff_quaternionOutputLeftPhaseEq
    C.implementation D.implementation

/-- On certified quaternionic circuits, same permutation is exactly basis-measurement equality. -/
theorem iff_quaternionBasisMeasurementEq {W : Type v} [Fintype W]
    {C D : QuaternionBasisClassicalCircuit W} :
    SameCircuitBasisBehavior C D ↔
      BasisMeasurementEq State.quaternionWeight C.circuit.eval D.circuit.eval :=
  sameBasisBehavior_iff_quaternionBasisMeasurementEq
    C.implementation D.implementation

end SameCircuitBasisBehavior

namespace ExactCircuitEq

/-- Exact equality of evaluations forces the same certified basis permutation. -/
theorem sameCircuitBasisBehavior {R : Type u} {W : Type v}
    [Semiring R] [StarRing R] [Fintype W] {unitPhase : R → Prop}
    {C D : BasisClassicalCircuit R W unitPhase}
    (h : ExactCircuitEq C.circuit D.circuit)
    (unitPhase_ne_zero : ∀ phase, unitPhase phase → phase ≠ 0) :
    SameCircuitBasisBehavior C D := by
  have hD : BasisPermutationImplementation unitPhase
      (OrderedCircuit.eval C.circuit) D.permutation := by
    rw [h.eval_eq]
    exact D.implementation
  exact BasisPermutationImplementation.permutation_unique
    unitPhase_ne_zero C.implementation hD

/-- Exact equality of real circuit evaluations preserves certified classical behavior. -/
theorem realSameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : RealBasisClassicalCircuit W}
    (h : ExactCircuitEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.sameCircuitBasisBehavior (fun _ hphase ↦ realUnitSign_ne_zero hphase)

/-- Exact equality of complex circuit evaluations preserves certified classical behavior. -/
theorem complexSameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : ComplexBasisClassicalCircuit W}
    (h : ExactCircuitEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.sameCircuitBasisBehavior (fun _ hphase ↦ complexUnitPhase_ne_zero hphase)

/-- Exact equality of quaternionic circuit evaluations preserves certified classical behavior. -/
theorem quaternionSameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : QuaternionBasisClassicalCircuit W}
    (h : ExactCircuitEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.sameCircuitBasisBehavior (fun _ hphase ↦ quaternionUnitPhase_ne_zero hphase)

end ExactCircuitEq

/-! ## Global and central circuit phase preservation -/

namespace RealCircuitGlobalSignEq

/-- A real global circuit sign preserves the certified basis permutation. -/
theorem sameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : RealBasisClassicalCircuit W}
    (h : RealCircuitGlobalSignEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.eval.sameBasisBehavior C.implementation D.implementation

end RealCircuitGlobalSignEq

namespace ComplexCircuitGlobalPhaseEq

/-- A complex global circuit phase preserves the certified basis permutation. -/
theorem sameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : ComplexBasisClassicalCircuit W}
    (h : ComplexCircuitGlobalPhaseEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.eval.sameBasisBehavior C.implementation D.implementation

end ComplexCircuitGlobalPhaseEq

namespace QuaternionCircuitCentralSignEq

/-- A quaternionic central circuit sign preserves the certified basis permutation. -/
theorem sameCircuitBasisBehavior {W : Type v} [Fintype W]
    {C D : QuaternionBasisClassicalCircuit W}
    (h : QuaternionCircuitCentralSignEq C.circuit D.circuit) :
    SameCircuitBasisBehavior C D :=
  h.eval.sameBasisBehavior C.implementation D.implementation

end QuaternionCircuitCentralSignEq

/-! ## Identity circuit -/

section EmptyCircuit

variable {R : Type u} [Semiring R] [StarRing R]
variable {W : Type v} [Fintype W]

/--
The empty chronological circuit is a certified basis-classical circuit for
the identity permutation.  This construction is valid unchanged when the
wire type is empty.
-/
def emptyBasisClassicalCircuit (unitPhase : R → Prop)
    (unit_one : unitPhase 1) : BasisClassicalCircuit R W unitPhase where
  circuit := []
  locallyUnitary := OrderedCircuit.isLocallyUnitary_nil
  permutation := Equiv.refl (BitBasis W)
  implementation := by
    classical
    simpa only [OrderedCircuit.eval_nil, Matrix.permMatrix_refl,
      Equiv.refl_symm] using
      (BasisPermutationImplementation.ofPermMatrix
        (R := R) (unitPhase := unitPhase) unit_one
        (Equiv.refl (BitBasis W)))

@[simp]
theorem emptyBasisClassicalCircuit_circuit (unitPhase : R → Prop)
    (unit_one : unitPhase 1) :
    (emptyBasisClassicalCircuit (W := W) unitPhase unit_one).circuit = [] :=
  rfl

@[simp]
theorem emptyBasisClassicalCircuit_permutation (unitPhase : R → Prop)
    (unit_one : unitPhase 1) :
    (emptyBasisClassicalCircuit (W := W) unitPhase unit_one).permutation =
      Equiv.refl (BitBasis W) :=
  rfl

end EmptyCircuit

/-! ## The existing XOR basis-preparation construction -/

section BasisPreparation

variable {R : Type u} [Semiring R]
variable {W : Type v} [Fintype W]

/-- The permutation-matrix formula certifies all-input XOR basis behavior. -/
def basisPreparationMatrixImplementation (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    BasisPermutationImplementation unitPhase
      (basisPreparationMatrix (R := R) b) (xorBasisEquiv b) := by
  classical
  simpa only [basisPreparationMatrix, xorBasisEquiv_symm] using
    (BasisPermutationImplementation.ofPermMatrix
      (R := R) (unitPhase := unitPhase) unit_one (xorBasisEquiv b))

/-- The denotation of the existing full-support gate carries the XOR certificate. -/
def basisPreparationGateImplementation (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    BasisPermutationImplementation unitPhase
      (basisPreparationGate (R := R) b).denote (xorBasisEquiv b) := by
  simpa only [basisPreparationGate_denote] using
    basisPreparationMatrixImplementation unitPhase unit_one b

section Star

variable [StarRing R]

/-- The XOR preparation matrix bundled with its actual unitarity and permutation proofs. -/
def basisPreparationOperator (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    BasisClassicalUnitaryOperator R (BitBasis W) unitPhase where
  matrix := basisPreparationMatrix (R := R) b
  mem_unitary := basisPreparationMatrix_mem_unitary b
  permutation := xorBasisEquiv b
  implementation := basisPreparationMatrixImplementation unitPhase unit_one b

@[simp]
theorem basisPreparationOperator_matrix (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    (basisPreparationOperator unitPhase unit_one b).matrix =
      basisPreparationMatrix (R := R) b :=
  rfl

@[simp]
theorem basisPreparationOperator_permutation (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    (basisPreparationOperator unitPhase unit_one b).permutation = xorBasisEquiv b :=
  rfl

/-- The singleton full-support preparation gate as a certified basis-classical circuit. -/
def basisPreparationCircuit (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    BasisClassicalCircuit R W unitPhase where
  circuit := [basisPreparationGate (R := R) b]
  locallyUnitary := by
    simpa only [OrderedCircuit.isLocallyUnitary_cons,
      OrderedCircuit.isLocallyUnitary_nil, and_true] using
      basisPreparationGate_isLocallyUnitary (R := R) b
  permutation := xorBasisEquiv b
  implementation := by
    simpa only [OrderedCircuit.eval_singleton] using
      basisPreparationGateImplementation unitPhase unit_one b

@[simp]
theorem basisPreparationCircuit_circuit (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    (basisPreparationCircuit unitPhase unit_one b).circuit =
      [basisPreparationGate (R := R) b] :=
  rfl

@[simp]
theorem basisPreparationCircuit_permutation (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    (basisPreparationCircuit unitPhase unit_one b).permutation = xorBasisEquiv b :=
  rfl

/-- Every input column of the singleton circuit has its certified XOR output. -/
theorem basisPreparationCircuit_basisTransition (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b x : BitBasis W) :
    BasisTransition unitPhase
      (OrderedCircuit.eval (basisPreparationCircuit unitPhase unit_one b).circuit)
      x (xorBasisEquiv b x) :=
  (basisPreparationCircuit unitPhase unit_one b).implementation.basisTransition x

/-- The all-input evaluator formula: the unique XOR output has entry `1`. -/
theorem basisPreparationCircuit_eval_entry (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b x y : BitBasis W) :
    OrderedCircuit.eval (basisPreparationCircuit unitPhase unit_one b).circuit y x =
      if y = xorBasisEquiv b x then 1 else 0 := by
  classical
  rw [basisPreparationCircuit_circuit, OrderedCircuit.eval_singleton,
    basisPreparationGate_denote]
  simp only [basisPreparationMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  have hinv (z : BitBasis W) : xorBasisEquiv b (xorBasisEquiv b z) = z := by
    funext w
    simp
  have hiff : (xorBasisEquiv b y = x) ↔ (y = xorBasisEquiv b x) := by
    constructor
    · intro h
      rw [← h, hinv]
    · intro h
      rw [h, hinv]
  simp only [hiff]

/--
The known ground-column preparation theorem for the certified singleton
circuit.  Unlike the preceding entry theorem and implementation certificate,
this statement concerns only one fixed external input.
-/
theorem basisPreparationCircuit_mulVec_ground (unitPhase : R → Prop)
    (unit_one : unitPhase 1) (b : BitBasis W) :
    OrderedCircuit.eval (basisPreparationCircuit unitPhase unit_one b).circuit *ᵥ
        basisColumn (R := R) (groundBasis W) =
      basisColumn (R := R) b := by
  simpa only [basisPreparationCircuit_circuit, OrderedCircuit.eval_singleton] using
    basisPreparationGate_mulVec_ground (R := R) b

end Star

end BasisPreparation

end QuaternionicComputing.Semantics
