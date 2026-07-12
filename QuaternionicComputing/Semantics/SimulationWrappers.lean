module

public import QuaternionicComputing.Semantics.Simulation
public import QuaternionicComputing.Matrix.QuaternionRealification
public import QuaternionicComputing.Simulation.QuaternionToReal
public import QuaternionicComputing.Simulation.Scheduled
public import QuaternionicComputing.Simulation.CompiledResources

/-!
# Proof-bearing wrappers for exact cross-model simulations

This leaf classifies the existing matrix, placed-gate, ordered-circuit,
scheduled-circuit, composed, and conditional-compiler comparisons with the
directional relations from `Semantics.Simulation`.

The coefficient types below are raw coordinate pairs. They make the strongest
amplitude intertwinings explicit without asserting normalization, a factorized
top subsystem, ray equality, decoded outcomes, density evolution, or channel
equality. Likewise, every operator theorem keeps its embedding, reindexing,
schedule, or supplied compiler visible; none is same-space circuit equality.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

open QuaternionicComputing.Circuit

universe u v w

/-! ## Rectangular matrix state intertwinings -/

/--
Complex matrix realification intertwines every real pair of canonical-column
coefficients. The source matrix may be rectangular.
-/
theorem realifyMatrix_allCoefficient_stateIntertwining
    {O : Type u} {I : Type v} [Fintype I]
    (A : Matrix O I ℂ) :
    AllTopStateIntertwining
      (fun top : ℝ × ℝ ↦
        State.realTopCombination top.1 top.2)
      (fun top : ℝ × ℝ ↦
        State.realTopCombination top.1 top.2)
      A (QuaternionicComputing.Matrix.realify A) := by
  intro top input
  exact State.realify_mulVec_realTopCombination A top.1 top.2 input

/--
Quaternionic matrix complexification intertwines every complex pair of
canonical-column coefficients. The source matrix may be rectangular.
-/
theorem complexifyMatrix_allCoefficient_stateIntertwining
    {O : Type u} {I : Type v} [Fintype I]
    (A : Matrix O I ℍ[ℝ]) :
    AllTopStateIntertwining
      (fun top : ℂ × ℂ ↦
        State.complexTopCombination top.1 top.2)
      (fun top : ℂ × ℂ ↦
        State.complexTopCombination top.1 top.2)
      A (QuaternionicComputing.Quaternion.complexify A) := by
  intro top input
  exact State.complexify_mulVec_complexTopCombination A top.1 top.2 input

/-! ## Equation 63 reindexing and placed gates -/

/--
The direct Equation 63 real representation is exactly the composed
quaternion-to-complex-to-real embedding after its named row and column
reindexings. This is a matrix representation theorem, not a circuit translator.
-/
theorem directRealify_exactOperatorEmbedding
    {O : Type u} {I : Type v} (A : Matrix O I ℍ[ℝ]) :
    ExactOperatorEmbedding
      (fun source ↦
        Matrix.reindex
          (QuaternionicComputing.Quaternion.eq63PaperToComposed O).symm
          (QuaternionicComputing.Quaternion.eq63PaperToComposed I).symm
          (QuaternionicComputing.Matrix.realify
            (QuaternionicComputing.Quaternion.complexify source)))
      A (QuaternionicComputing.Quaternion.directRealify A) :=
  QuaternionicComputing.Quaternion.directRealify_eq_reindex A

/-- A translated placed complex gate exactly embeds its full denotation. -/
theorem realifyPlacedGate_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (gate : PlacedGate ℂ W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireRealify gate.denote
      (QuaternionicComputing.Circuit.realifyPlacedGate gate).denote :=
  QuaternionicComputing.Circuit.realifyPlacedGate_denote gate

/-- A translated placed quaternionic gate exactly embeds its full denotation. -/
theorem complexifyPlacedGate_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (gate : PlacedGate ℍ[ℝ] W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireComplexify gate.denote
      (QuaternionicComputing.Circuit.complexifyPlacedGate gate).denote :=
  QuaternionicComputing.Circuit.complexifyPlacedGate_denote gate

/-! ## Primary ordered-circuit simulations -/

/-- The realified circuit operator is exactly the wire-realified source operator. -/
theorem realifyCircuit_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℂ W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireRealify
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.realifyCircuit circuit)) :=
  QuaternionicComputing.Simulation.eval_realifyCircuit circuit

/-- The complexified circuit operator is exactly the wire-complexified source operator. -/
theorem complexifyCircuit_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireComplexify
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit circuit)) :=
  QuaternionicComputing.Simulation.eval_complexifyCircuit circuit

/--
The realified circuit intertwines every real pair of wire-facing column
coefficients, including both canonical specializations.
-/
theorem realifyCircuit_allCoefficient_stateIntertwining
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℂ W) :
    AllTopStateIntertwining
      (fun top : ℝ × ℝ ↦
        QuaternionicComputing.Simulation.wireRealTopCombination top.1 top.2)
      (fun top : ℝ × ℝ ↦
        QuaternionicComputing.Simulation.wireRealTopCombination top.1 top.2)
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.realifyCircuit circuit)) := by
  intro top input
  exact
    QuaternionicComputing.Simulation.eval_realifyCircuit_mulVec_wireRealTopCombination
      circuit top.1 top.2 input

/--
The complexified circuit intertwines every complex pair of wire-facing column
coefficients, including both canonical specializations.
-/
theorem complexifyCircuit_allCoefficient_stateIntertwining
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    AllTopStateIntertwining
      (fun top : ℂ × ℂ ↦
        QuaternionicComputing.Simulation.wireComplexTopCombination top.1 top.2)
      (fun top : ℂ × ℂ ↦
        QuaternionicComputing.Simulation.wireComplexTopCombination top.1 top.2)
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit circuit)) := by
  intro top input
  exact
    QuaternionicComputing.Simulation.eval_complexifyCircuit_mulVec_wireComplexTopCombination
      circuit top.1 top.2 input

/-! ## One supplied legal schedule -/

/--
Complexification embeds the operator of one supplied legal schedule. It does
not select a schedule or compare that schedule with any other one.
-/
theorem scheduledComplexifyCircuit_exactOperatorEmbedding
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type w} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireComplexify
      (schedule.scheduledEval gates)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit
          (schedule.scheduledCircuit gates))) :=
  QuaternionicComputing.Simulation.eval_complexify_scheduledCircuit
    schedule gates

/--
For one supplied schedule, complexification intertwines every complex pair of
column coefficients with the exact scheduled source operator.
-/
theorem scheduledComplexifyCircuit_allCoefficient_stateIntertwining
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type w} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    AllTopStateIntertwining
      (fun top : ℂ × ℂ ↦
        QuaternionicComputing.Simulation.wireComplexTopCombination top.1 top.2)
      (fun top : ℂ × ℂ ↦
        QuaternionicComputing.Simulation.wireComplexTopCombination top.1 top.2)
      (schedule.scheduledEval gates)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit
          (schedule.scheduledCircuit gates))) := by
  intro top input
  rw [QuaternionicComputing.Simulation.eval_complexify_scheduledCircuit]
  exact
    QuaternionicComputing.Simulation.wireComplexify_mulVec_wireComplexTopCombination
      (schedule.scheduledEval gates) top.1 top.2 input

/--
Injective complexification preserves a supplied operator gap between two
legal schedules; it does not assert that arbitrary schedules differ.
-/
theorem scheduledComplexifyCircuit_eval_ne_of_source_ne
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {W : Type w} [Fintype W] {precedes : ι → ι → Prop}
    (first second : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W)
    (h : first.scheduledEval gates ≠ second.scheduledEval gates) :
    OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit
          (first.scheduledCircuit gates)) ≠
      OrderedCircuit.eval
        (QuaternionicComputing.Simulation.complexifyCircuit
          (second.scheduledCircuit gates)) :=
  QuaternionicComputing.Simulation.eval_complexify_scheduledCircuit_ne_of_scheduledEval_ne
    first second gates h

/-! ## Composed quaternion-to-real simulation -/

/--
The twice-translated real circuit exactly implements the composed wire-facing
complexification then realification of the quaternionic source operator.
-/
theorem quaternionToRealCircuit_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding
      (QuaternionicComputing.Circuit.wireRealify ∘
        QuaternionicComputing.Circuit.wireComplexify)
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.quaternionToRealCircuit circuit)) := by
  exact QuaternionicComputing.Simulation.eval_quaternionToRealCircuit circuit

/--
The composed circuit intertwines arbitrary inner complex and outer real
coefficient pairs. The nested coordinate order is explicit and has no
top/bottom product-state interpretation.
-/
theorem quaternionToRealCircuit_allCoefficient_stateIntertwining
    {W : Type w} [Fintype W]
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    AllTopStateIntertwining
      (fun top : (ℂ × ℂ) × (ℝ × ℝ) ↦
        QuaternionicComputing.Simulation.wireRealTopCombination
          top.2.1 top.2.2 ∘
        QuaternionicComputing.Simulation.wireComplexTopCombination
          top.1.1 top.1.2)
      (fun top : (ℂ × ℂ) × (ℝ × ℝ) ↦
        QuaternionicComputing.Simulation.wireRealTopCombination
          top.2.1 top.2.2 ∘
        QuaternionicComputing.Simulation.wireComplexTopCombination
          top.1.1 top.1.2)
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (QuaternionicComputing.Simulation.quaternionToRealCircuit circuit)) := by
  intro top input
  change OrderedCircuit.eval
      (QuaternionicComputing.Simulation.realifyCircuit
        (QuaternionicComputing.Simulation.complexifyCircuit circuit)) *ᵥ
      QuaternionicComputing.Simulation.wireRealTopCombination
        top.2.1 top.2.2
        (QuaternionicComputing.Simulation.wireComplexTopCombination
          top.1.1 top.1.2 input) = _
  rw [
    QuaternionicComputing.Simulation.eval_realifyCircuit_mulVec_wireRealTopCombination]
  exact congrArg
    (QuaternionicComputing.Simulation.wireRealTopCombination
      top.2.1 top.2.2)
    (QuaternionicComputing.Simulation.eval_complexifyCircuit_mulVec_wireComplexTopCombination
      circuit top.1.1 top.1.2 input)

/-! ## Conditional exact compilation -/

/--
A supplied exact real compiler preserves the embedded complex circuit operator.
This theorem does not provide or synthesize the compiler.
-/
theorem compileRealifyCircuit_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (compiler : ExactGateCompiler ℝ (AddedWire W))
    (circuit : OrderedCircuit ℂ W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireRealify
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (compiler.compileCircuit
          (QuaternionicComputing.Simulation.realifyCircuit circuit))) :=
  QuaternionicComputing.Simulation.eval_compile_realifyCircuit compiler circuit

/--
A supplied exact complex compiler preserves the embedded quaternionic circuit
operator. This theorem does not provide or synthesize the compiler.
-/
theorem compileComplexifyCircuit_exactOperatorEmbedding
    {W : Type w} [Fintype W]
    (compiler : ExactGateCompiler ℂ (AddedWire W))
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding
      QuaternionicComputing.Circuit.wireComplexify
      (OrderedCircuit.eval circuit)
      (OrderedCircuit.eval
        (compiler.compileCircuit
          (QuaternionicComputing.Simulation.complexifyCircuit circuit))) :=
  QuaternionicComputing.Simulation.eval_compile_complexifyCircuit compiler circuit

end QuaternionicComputing.Semantics
