module

public import QuaternionicComputing.Semantics.ChannelPhase
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealCircuit
public import QuaternionicComputing.Circuit.LocalUnitary

/-!
# Unitary channels of chronological circuits

This leaf lifts the finite real/complex unitary-channel semantics through the
actual evaluator of a locally unitary chronological circuit.  A
`UnitaryCircuit` stores only the gate list and its local-unitarity certificate;
its `UnitaryOperator` is derived from `OrderedCircuit.eval`.

`CircuitChannelEq` compares the complete evolved density matrix for every
density input, while `CircuitAllMeasurementEq` compares every genuine
physical-effect Born value after evolution.  Both are relations on certified
circuits and therefore have honest equivalence laws.  Appending a later
circuit uses the established chronological order: the later evaluated matrix
multiplies on the left.

The matrix-level phase converses require an inhabited basis.  Circuit basis
types `BitBasis W = W → Bool` are canonically inhabited even when `W` is
empty, so the circuit wrappers discharge that hypothesis internally rather
than burdening callers with redundant evidence.

This module compares evaluated physical maps only.  It does not compare gate
syntax, schedules, resources, cross-model encodings, partial traces, or
quaternionic channels.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

open QuaternionicComputing.Circuit

universe u v

/-! ## From locally unitary circuits to bundled operators -/

namespace UnitaryOperator

variable {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]

/-- Bundle the evaluation of a locally unitary circuit as a unitary operator. -/
def ofCircuit (C : OrderedCircuit 𝕜 W) (hC : C.IsLocallyUnitary) :
    UnitaryOperator 𝕜 (BitBasis W) :=
  ofMatrix C.eval (C.eval_mem_unitary hC)

/-- The matrix of a bundled circuit operator is its chronological evaluation. -/
@[simp]
theorem ofCircuit_coe (C : OrderedCircuit 𝕜 W) (hC : C.IsLocallyUnitary) :
    ((ofCircuit C hC : UnitaryOperator 𝕜 (BitBasis W)) :
      Matrix (BitBasis W) (BitBasis W) 𝕜) = C.eval :=
  rfl

end UnitaryOperator

/--
A chronological circuit bundled with a proof that every local gate is
unitary.  Its evaluated unitary operator is derived rather than stored.
-/
structure UnitaryCircuit (𝕜 : Type u) (W : Type v)
    [RCLike 𝕜] [Fintype W] where
  /-- The underlying chronological gate list. -/
  circuit : OrderedCircuit 𝕜 W
  /-- Every stored local gate matrix is unitary. -/
  locallyUnitary : circuit.IsLocallyUnitary

/-- A locally unitary real chronological circuit. -/
abbrev RealUnitaryCircuit (W : Type v) [Fintype W] :=
  UnitaryCircuit ℝ W

/-- A locally unitary complex chronological circuit. -/
abbrev ComplexUnitaryCircuit (W : Type v) [Fintype W] :=
  UnitaryCircuit ℂ W

namespace UnitaryCircuit

variable {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]

/-- Forget the certificate and use a unitary circuit as its chronological gate list. -/
instance : Coe (UnitaryCircuit 𝕜 W) (OrderedCircuit 𝕜 W) where
  coe C := C.circuit

/-- Coercion exposes the stored chronological circuit definitionally. -/
@[simp]
theorem coe_circuit (C : UnitaryCircuit 𝕜 W) :
    ((C : OrderedCircuit 𝕜 W)) = C.circuit :=
  rfl

/-- Certified unitary circuits are equal when their gate lists are equal. -/
theorem ext_circuit {C D : UnitaryCircuit 𝕜 W}
    (h : C.circuit = D.circuit) : C = D := by
  cases C
  cases D
  simpa using h

/-- Certified unitary circuits are extensional in the underlying circuit. -/
@[ext]
theorem ext {C D : UnitaryCircuit 𝕜 W}
    (h : (C : OrderedCircuit 𝕜 W) = (D : OrderedCircuit 𝕜 W)) : C = D :=
  ext_circuit h

/-- Equality of unitary circuits is exactly equality of their gate lists. -/
theorem eq_iff_circuit_eq {C D : UnitaryCircuit 𝕜 W} :
    C = D ↔ C.circuit = D.circuit := by
  constructor
  · rintro rfl
    rfl
  · exact ext_circuit

/-- The evaluation of a unitary circuit is unitary. -/
theorem eval_mem_unitary (C : UnitaryCircuit 𝕜 W) :
    C.circuit.eval ∈
      unitary (Matrix (BitBasis W) (BitBasis W) 𝕜) :=
  C.circuit.eval_mem_unitary C.locallyUnitary

/-- Forget circuit syntax while retaining the evaluated unitary operator. -/
def toOperator (C : UnitaryCircuit 𝕜 W) :
    UnitaryOperator 𝕜 (BitBasis W) :=
  UnitaryOperator.ofCircuit C.circuit C.locallyUnitary

/-- A circuit's bundled operator has its chronological evaluator as matrix. -/
@[simp]
theorem toOperator_coe (C : UnitaryCircuit 𝕜 W) :
    ((C.toOperator : UnitaryOperator 𝕜 (BitBasis W)) :
      Matrix (BitBasis W) (BitBasis W) 𝕜) = C.circuit.eval :=
  rfl

/-- The empty chronological circuit with its vacuous local-unitarity proof. -/
def identity : UnitaryCircuit 𝕜 W where
  circuit := []
  locallyUnitary := OrderedCircuit.isLocallyUnitary_nil

/-- The stored circuit of the identity bundle is the empty gate list. -/
@[simp]
theorem identity_circuit :
    (identity : UnitaryCircuit 𝕜 W).circuit = [] :=
  rfl

/-- The empty circuit evaluates to the bundled identity operator. -/
@[simp]
theorem toOperator_identity :
    (identity : UnitaryCircuit 𝕜 W).toOperator = UnitaryOperator.identity := by
  apply UnitaryOperator.ext_matrix
  simp

/-- Append a later locally unitary circuit to an earlier one. -/
def append (C D : UnitaryCircuit 𝕜 W) : UnitaryCircuit 𝕜 W where
  circuit := C.circuit ++ D.circuit
  locallyUnitary := C.locallyUnitary.append D.locallyUnitary

/-- Bundled append retains literal chronological list append. -/
@[simp]
theorem append_circuit (C D : UnitaryCircuit 𝕜 W) :
    (C.append D).circuit = C.circuit ++ D.circuit :=
  rfl

/-- Bundled chronological append is associative. -/
@[simp]
theorem append_assoc (C D E : UnitaryCircuit 𝕜 W) :
    (C.append D).append E = C.append (D.append E) := by
  apply ext_circuit
  simp only [append_circuit, List.append_assoc]

/-- The empty circuit is a left identity for chronological append. -/
@[simp]
theorem identity_append (C : UnitaryCircuit 𝕜 W) :
    identity.append C = C := by
  apply ext_circuit
  simp

/-- The empty circuit is a right identity for chronological append. -/
@[simp]
theorem append_identity (C : UnitaryCircuit 𝕜 W) :
    C.append identity = C := by
  apply ext_circuit
  simp

/--
The operator of `C.append D` applies `C` first and `D` later, hence is
`C.toOperator.followedBy D.toOperator` with matrix `eval D * eval C`.
-/
@[simp]
theorem toOperator_append (C D : UnitaryCircuit 𝕜 W) :
    (C.append D).toOperator = C.toOperator.followedBy D.toOperator := by
  apply UnitaryOperator.ext_matrix
  simp

end UnitaryCircuit

/-! ## Evaluator-backed channel relations -/

/-- Equality of the complete unitary channels induced by two certified circuits. -/
def CircuitChannelEq {𝕜 : Type u} {W : Type v}
    [RCLike 𝕜] [Fintype W]
    (C D : UnitaryCircuit 𝕜 W) : Prop :=
  ChannelEq C.toOperator D.toOperator

/-- Agreement of two certified circuits on all density inputs and physical effects. -/
def CircuitAllMeasurementEq {𝕜 : Type u} {W : Type v}
    [RCLike 𝕜] [Fintype W]
    (C D : UnitaryCircuit 𝕜 W) : Prop :=
  AllMeasurementEq C.toOperator D.toOperator

namespace CircuitChannelEq

variable {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
variable {C D E : UnitaryCircuit 𝕜 W}

/-- Circuit channel equality is exactly channel equality of evaluated operators. -/
@[simp]
theorem iff_toOperator :
    CircuitChannelEq C D ↔ ChannelEq C.toOperator D.toOperator :=
  Iff.rfl

/-- Expose equality of evolved density matrices for one input. -/
theorem evolve_eq (h : CircuitChannelEq C D)
    (rho : DensityMatrix 𝕜 (BitBasis W)) :
    C.toOperator.evolve rho = D.toOperator.evolve rho :=
  ChannelEq.evolve_eq h rho

@[refl]
theorem refl (C : UnitaryCircuit 𝕜 W) : CircuitChannelEq C C :=
  ChannelEq.refl _

@[symm]
theorem symm (h : CircuitChannelEq C D) : CircuitChannelEq D C :=
  ChannelEq.symm h

@[trans]
theorem trans (hCD : CircuitChannelEq C D) (hDE : CircuitChannelEq D E) :
    CircuitChannelEq C E :=
  ChannelEq.trans hCD hDE

/-- Evaluated circuit-channel equality is an equivalence relation. -/
theorem equivalence : Equivalence (@CircuitChannelEq 𝕜 W _ _) :=
  ⟨refl, symm, trans⟩

/-- Equal circuit channels agree on every genuine physical measurement. -/
theorem allMeasurementEq (h : CircuitChannelEq C D) :
    CircuitAllMeasurementEq C D :=
  ChannelEq.allMeasurementEq h

/-- Appending related early and later circuit pairs preserves channel equality. -/
theorem append {C1 C2 D1 D2 : UnitaryCircuit 𝕜 W}
    (h1 : CircuitChannelEq C1 D1) (h2 : CircuitChannelEq C2 D2) :
    CircuitChannelEq (C1.append C2) (D1.append D2) := by
  rw [iff_toOperator, UnitaryCircuit.toOperator_append,
    UnitaryCircuit.toOperator_append]
  exact ChannelEq.followedBy h1 h2

/-- A common later certified circuit preserves channel equality. -/
theorem append_same_later (L : UnitaryCircuit 𝕜 W)
    (h : CircuitChannelEq C D) :
    CircuitChannelEq (C.append L) (D.append L) :=
  append h (refl L)

/-- A common earlier certified circuit preserves channel equality. -/
theorem prepend_same_earlier (E : UnitaryCircuit 𝕜 W)
    (h : CircuitChannelEq C D) :
    CircuitChannelEq (E.append C) (E.append D) :=
  append (refl E) h

end CircuitChannelEq

namespace CircuitAllMeasurementEq

variable {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
variable {C D E : UnitaryCircuit 𝕜 W}

/-- Circuit all-measurement equality is the evaluated-operator relation. -/
@[simp]
theorem iff_toOperator :
    CircuitAllMeasurementEq C D ↔
      AllMeasurementEq C.toOperator D.toOperator :=
  Iff.rfl

/-- Expose equality of one physical-effect Born value after one density input. -/
theorem bornValue_eq (h : CircuitAllMeasurementEq C D)
    (rho : DensityMatrix 𝕜 (BitBasis W))
    (F : Effect 𝕜 (BitBasis W)) :
    Effect.bornValue F (C.toOperator.evolve rho) =
      Effect.bornValue F (D.toOperator.evolve rho) :=
  AllMeasurementEq.bornValue_eq h rho F

@[refl]
theorem refl (C : UnitaryCircuit 𝕜 W) : CircuitAllMeasurementEq C C :=
  AllMeasurementEq.refl _

@[symm]
theorem symm (h : CircuitAllMeasurementEq C D) :
    CircuitAllMeasurementEq D C :=
  AllMeasurementEq.symm h

@[trans]
theorem trans (hCD : CircuitAllMeasurementEq C D)
    (hDE : CircuitAllMeasurementEq D E) : CircuitAllMeasurementEq C E :=
  AllMeasurementEq.trans hCD hDE

/-- Evaluated all-physical-measurement equality is an equivalence relation. -/
theorem equivalence : Equivalence (@CircuitAllMeasurementEq 𝕜 W _ _) :=
  ⟨refl, symm, trans⟩

/-- Agreement on all genuine effects recovers complete circuit channel equality. -/
theorem channelEq (h : CircuitAllMeasurementEq C D) : CircuitChannelEq C D :=
  AllMeasurementEq.channelEq h

/-- Appending related early and later pairs preserves all-measurement equality. -/
theorem append {C1 C2 D1 D2 : UnitaryCircuit 𝕜 W}
    (h1 : CircuitAllMeasurementEq C1 D1)
    (h2 : CircuitAllMeasurementEq C2 D2) :
    CircuitAllMeasurementEq (C1.append C2) (D1.append D2) := by
  rw [iff_toOperator, UnitaryCircuit.toOperator_append,
    UnitaryCircuit.toOperator_append]
  exact AllMeasurementEq.followedBy h1 h2

/-- A common later certified circuit preserves all physical measurements. -/
theorem append_same_later (L : UnitaryCircuit 𝕜 W)
    (h : CircuitAllMeasurementEq C D) :
    CircuitAllMeasurementEq (C.append L) (D.append L) :=
  append h (refl L)

/-- A common earlier certified circuit preserves all physical measurements. -/
theorem prepend_same_earlier (E : UnitaryCircuit 𝕜 W)
    (h : CircuitAllMeasurementEq C D) :
    CircuitAllMeasurementEq (E.append C) (E.append D) :=
  append (refl E) h

end CircuitAllMeasurementEq

/-- Circuit channel equality is equivalent to all genuine-effect agreement. -/
theorem circuitChannelEq_iff_allMeasurementEq
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    (C D : UnitaryCircuit 𝕜 W) :
    CircuitChannelEq C D ↔ CircuitAllMeasurementEq C D :=
  channelEq_iff_allMeasurementEq C.toOperator D.toOperator

/-! ## Exact evaluator equality -/

namespace ExactCircuitEq

variable {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]

/-- Exact equality of two certified circuit evaluators implies channel equality. -/
theorem circuitChannelEq {C D : UnitaryCircuit 𝕜 W}
    (h : ExactCircuitEq C.circuit D.circuit) : CircuitChannelEq C D :=
  ChannelEq.of_matrix_eq (by simpa using h.eval_eq)

/-- Exact evaluator equality implies agreement on all physical measurements. -/
theorem circuitAllMeasurementEq {C D : UnitaryCircuit 𝕜 W}
    (h : ExactCircuitEq C.circuit D.circuit) :
    CircuitAllMeasurementEq C D :=
  (circuitChannelEq h).allMeasurementEq

end ExactCircuitEq

/-! ## Real and complex phase characterizations -/

namespace RealCircuitGlobalSignEq

variable {W : Type u} [Fintype W]

/-- One evaluator-wide real sign gives equality of the induced circuit channels. -/
theorem circuitChannelEq {C D : RealUnitaryCircuit W}
    (h : RealCircuitGlobalSignEq C.circuit D.circuit) :
    CircuitChannelEq C D := by
  change ChannelEq C.toOperator D.toOperator
  apply RealGlobalSignEq.channelEq
  simpa only [UnitaryCircuit.toOperator_coe] using h.eval

/-- One evaluator-wide real sign preserves every physical measurement. -/
theorem circuitAllMeasurementEq {C D : RealUnitaryCircuit W}
    (h : RealCircuitGlobalSignEq C.circuit D.circuit) :
    CircuitAllMeasurementEq C D :=
  (circuitChannelEq h).allMeasurementEq

end RealCircuitGlobalSignEq

namespace ComplexCircuitGlobalPhaseEq

variable {W : Type u} [Fintype W]

/-- One evaluator-wide complex phase gives equality of the induced circuit channels. -/
theorem circuitChannelEq {C D : ComplexUnitaryCircuit W}
    (h : ComplexCircuitGlobalPhaseEq C.circuit D.circuit) :
    CircuitChannelEq C D := by
  change ChannelEq C.toOperator D.toOperator
  apply ComplexGlobalPhaseEq.channelEq
  simpa only [UnitaryCircuit.toOperator_coe] using h.eval

/-- One evaluator-wide complex phase preserves every physical measurement. -/
theorem circuitAllMeasurementEq {C D : ComplexUnitaryCircuit W}
    (h : ComplexCircuitGlobalPhaseEq C.circuit D.circuit) :
    CircuitAllMeasurementEq C D :=
  (circuitChannelEq h).allMeasurementEq

end ComplexCircuitGlobalPhaseEq

namespace CircuitChannelEq

/-- Equal real circuit channels differ by one evaluator-wide sign. -/
theorem realGlobalSignEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitChannelEq C D) :
    RealCircuitGlobalSignEq C.circuit D.circuit := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change RealGlobalSignEq C.circuit.eval D.circuit.eval
  simpa only [UnitaryCircuit.toOperator_coe] using
    (realGlobalSignEq_iff_channelEq C.toOperator D.toOperator).mpr h

/-- Equal complex circuit channels differ by one evaluator-wide unit phase. -/
theorem complexGlobalPhaseEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitChannelEq C D) :
    ComplexCircuitGlobalPhaseEq C.circuit D.circuit := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change ComplexGlobalPhaseEq C.circuit.eval D.circuit.eval
  simpa only [UnitaryCircuit.toOperator_coe] using
    (complexGlobalPhaseEq_iff_channelEq C.toOperator D.toOperator).mpr h

/-- Equal real circuit channels act identically on all normalized pure rays. -/
theorem realProjectiveActionEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitChannelEq C D) :
    RealCircuitProjectiveActionEq C.circuit D.circuit := by
  change RealProjectiveActionEq C.circuit.eval D.circuit.eval
  simpa only [UnitaryCircuit.toOperator_coe] using
    ChannelEq.realProjectiveActionEq h

/-- Equal complex circuit channels act identically on all normalized pure rays. -/
theorem complexProjectiveActionEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitChannelEq C D) :
    ComplexCircuitProjectiveActionEq C.circuit D.circuit := by
  change ComplexProjectiveActionEq C.circuit.eval D.circuit.eval
  simpa only [UnitaryCircuit.toOperator_coe] using
    ChannelEq.complexProjectiveActionEq h

end CircuitChannelEq

/-- Real circuit global-sign equality is exactly equality of the induced channels. -/
theorem realCircuitGlobalSignEq_iff_channelEq
    {W : Type u} [Fintype W]
    (C D : RealUnitaryCircuit W) :
    RealCircuitGlobalSignEq C.circuit D.circuit ↔ CircuitChannelEq C D := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change RealGlobalSignEq C.circuit.eval D.circuit.eval ↔
    ChannelEq C.toOperator D.toOperator
  simpa only [UnitaryCircuit.toOperator_coe] using
    realGlobalSignEq_iff_channelEq C.toOperator D.toOperator

/-- Complex circuit global-phase equality is exactly equality of the induced channels. -/
theorem complexCircuitGlobalPhaseEq_iff_channelEq
    {W : Type u} [Fintype W]
    (C D : ComplexUnitaryCircuit W) :
    ComplexCircuitGlobalPhaseEq C.circuit D.circuit ↔ CircuitChannelEq C D := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change ComplexGlobalPhaseEq C.circuit.eval D.circuit.eval ↔
    ChannelEq C.toOperator D.toOperator
  simpa only [UnitaryCircuit.toOperator_coe] using
    complexGlobalPhaseEq_iff_channelEq C.toOperator D.toOperator

/-- Normalized real projective circuit action is exactly channel equality. -/
theorem realCircuitProjectiveActionEq_iff_channelEq
    {W : Type u} [Fintype W]
    (C D : RealUnitaryCircuit W) :
    RealCircuitProjectiveActionEq C.circuit D.circuit ↔
      CircuitChannelEq C D := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change RealProjectiveActionEq C.circuit.eval D.circuit.eval ↔
    ChannelEq C.toOperator D.toOperator
  simpa only [UnitaryCircuit.toOperator_coe] using
    realProjectiveActionEq_iff_channelEq C.toOperator D.toOperator

/-- Normalized complex projective circuit action is exactly channel equality. -/
theorem complexCircuitProjectiveActionEq_iff_channelEq
    {W : Type u} [Fintype W]
    (C D : ComplexUnitaryCircuit W) :
    ComplexCircuitProjectiveActionEq C.circuit D.circuit ↔
      CircuitChannelEq C D := by
  letI : Nonempty (BitBasis W) := ⟨fun _ ↦ false⟩
  change ComplexProjectiveActionEq C.circuit.eval D.circuit.eval ↔
    ChannelEq C.toOperator D.toOperator
  simpa only [UnitaryCircuit.toOperator_coe] using
    complexProjectiveActionEq_iff_channelEq C.toOperator D.toOperator

end QuaternionicComputing.Semantics
