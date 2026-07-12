module

public import QuaternionicComputing.Semantics.ChannelAudit
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit
public import QuaternionicComputing.Semantics.StatePhaseAudit
public import QuaternionicComputing.Semantics.BasisBehaviorAudit
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Circuit.ProductInputOrderingWitness

/-!
# Same-space semantic hierarchy audit

This non-root leaf packages the strictness and incomparability witnesses used
by Goal 2 Stage 8.  It deliberately reuses the checked rational unitary,
state-phase, certified-classical, and quaternionic ordering diagnostics rather
than repeating their arithmetic.  In particular, every channel statement is
about a bundled real or complex unitary, every state witness is normalized,
and the quaternionic schedule comparison below is explicitly restricted to
one supplied ground input.

The public root does not import this file.  Stable Stage 8 hierarchy arrows
are consumed in a separate aggregate section appended after those leaves have
strict-compiled.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.HierarchyAudit

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

open OperatorPhase.ComplexRealAudit

/-! ## Bundled real and complex unitary twist families -/

/-- The checked rational real rotation, bundled for density-channel semantics. -/
def realRotationOperator : RealUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix realRotation realRotation_mem_unitary

/-- The checked input-column sign twist, bundled as a real unitary. -/
def realInputTwistOperator : RealUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix realInputTwist realInputTwist_mem_unitary

/-- The checked output-row sign twist, bundled as a real unitary. -/
def realOutputTwistOperator : RealUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix realOutputTwist realOutputTwist_mem_unitary

/-- The checked rational complex rotation, bundled for density-channel semantics. -/
def complexRotationOperator : ComplexUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix complexRotation complexRotation_mem_unitary

/-- The checked input-column complex phase twist, bundled as a complex unitary. -/
def complexInputTwistOperator : ComplexUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix complexInputTwist complexInputTwist_mem_unitary

/-- The checked output-row complex phase twist, bundled as a complex unitary. -/
def complexOutputTwistOperator : ComplexUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix complexOutputTwist complexOutputTwist_mem_unitary

/--
The real input-column twist preserves every basis preparation but is neither
an output-row sign relation nor an all-pure-input, channel, or all-effect
equivalence.
-/
theorem real_inputTwist_hierarchy_boundary :
    RealInputBasisSignEq
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realInputTwistOperator : Matrix Bool Bool ℝ) ∧
      ¬ RealOutputBasisSignEq
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realInputTwistOperator : Matrix Bool Bool ℝ) ∧
      BasisMeasurementEq State.realWeight
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realInputTwistOperator : Matrix Bool Bool ℝ) ∧
      ¬ PureInputBasisMeasurementEq State.realWeight
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realInputTwistOperator : Matrix Bool Bool ℝ) ∧
      ¬ ChannelEq realRotationOperator realInputTwistOperator ∧
      ¬ AllMeasurementEq realRotationOperator realInputTwistOperator := by
  have hinput : RealInputBasisSignEq
      (realRotationOperator : Matrix Bool Bool ℝ)
      (realInputTwistOperator : Matrix Bool Bool ℝ) := by
    simpa [realRotationOperator, realInputTwistOperator] using
      realRotation_inputTwist
  have hnotOutput : ¬ RealOutputBasisSignEq
      (realRotationOperator : Matrix Bool Bool ℝ)
      (realInputTwistOperator : Matrix Bool Bool ℝ) := by
    simpa [realRotationOperator, realInputTwistOperator] using
      realInputTwist_not_output
  have hnotPure : ¬ PureInputBasisMeasurementEq State.realWeight
      (realRotationOperator : Matrix Bool Bool ℝ)
      (realInputTwistOperator : Matrix Bool Bool ℝ) := by
    simpa [realRotationOperator, realInputTwistOperator] using
      realInputTwist_not_pureInputBasisMeasurementEq
  have hnotChannel : ¬ ChannelEq
      realRotationOperator realInputTwistOperator := by
    intro hchannel
    apply realInputTwist_not_global
    exact (realGlobalSignEq_iff_channelEq
      realRotationOperator realInputTwistOperator).2 hchannel
  have hnotAll : ¬ AllMeasurementEq
      realRotationOperator realInputTwistOperator := by
    intro hall
    exact hnotChannel hall.channelEq
  exact ⟨hinput, hnotOutput, hinput.basisMeasurementEq, hnotPure,
    hnotChannel, hnotAll⟩

/--
The real output-row twist preserves basis statistics for every normalized
pure input, but it is neither an input-column sign relation nor a channel or
all-effect equivalence.
-/
theorem real_outputTwist_hierarchy_boundary :
    ¬ RealInputBasisSignEq
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realOutputTwistOperator : Matrix Bool Bool ℝ) ∧
      RealOutputBasisSignEq
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realOutputTwistOperator : Matrix Bool Bool ℝ) ∧
      BasisMeasurementEq State.realWeight
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realOutputTwistOperator : Matrix Bool Bool ℝ) ∧
      PureInputBasisMeasurementEq State.realWeight
        (realRotationOperator : Matrix Bool Bool ℝ)
        (realOutputTwistOperator : Matrix Bool Bool ℝ) ∧
      ¬ ChannelEq realRotationOperator realOutputTwistOperator ∧
      ¬ AllMeasurementEq realRotationOperator realOutputTwistOperator := by
  have houtput : RealOutputBasisSignEq
      (realRotationOperator : Matrix Bool Bool ℝ)
      (realOutputTwistOperator : Matrix Bool Bool ℝ) := by
    simpa [realRotationOperator, realOutputTwistOperator] using
      realRotation_outputTwist
  have hnotInput : ¬ RealInputBasisSignEq
      (realRotationOperator : Matrix Bool Bool ℝ)
      (realOutputTwistOperator : Matrix Bool Bool ℝ) := by
    simpa [realRotationOperator, realOutputTwistOperator] using
      realOutputTwist_not_input
  have hnotChannel : ¬ ChannelEq
      realRotationOperator realOutputTwistOperator := by
    intro hchannel
    apply realOutputTwist_not_global
    exact (realGlobalSignEq_iff_channelEq
      realRotationOperator realOutputTwistOperator).2 hchannel
  have hnotAll : ¬ AllMeasurementEq
      realRotationOperator realOutputTwistOperator := by
    intro hall
    exact hnotChannel hall.channelEq
  exact ⟨hnotInput, houtput, houtput.basisMeasurementEq,
    houtput.pureInputBasisMeasurementEq, hnotChannel, hnotAll⟩

/-- Complex input-column phases have the same strict hierarchy boundary. -/
theorem complex_inputTwist_hierarchy_boundary :
    ComplexInputBasisPhaseEq
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexInputTwistOperator : Matrix Bool Bool ℂ) ∧
      ¬ ComplexOutputBasisPhaseEq
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexInputTwistOperator : Matrix Bool Bool ℂ) ∧
      BasisMeasurementEq State.complexWeight
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexInputTwistOperator : Matrix Bool Bool ℂ) ∧
      ¬ PureInputBasisMeasurementEq State.complexWeight
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexInputTwistOperator : Matrix Bool Bool ℂ) ∧
      ¬ ChannelEq complexRotationOperator complexInputTwistOperator ∧
      ¬ AllMeasurementEq complexRotationOperator complexInputTwistOperator := by
  have hinput : ComplexInputBasisPhaseEq
      (complexRotationOperator : Matrix Bool Bool ℂ)
      (complexInputTwistOperator : Matrix Bool Bool ℂ) := by
    simpa [complexRotationOperator, complexInputTwistOperator] using
      complexRotation_inputTwist
  have hnotOutput : ¬ ComplexOutputBasisPhaseEq
      (complexRotationOperator : Matrix Bool Bool ℂ)
      (complexInputTwistOperator : Matrix Bool Bool ℂ) := by
    simpa [complexRotationOperator, complexInputTwistOperator] using
      complexInputTwist_not_output
  have hnotPure : ¬ PureInputBasisMeasurementEq State.complexWeight
      (complexRotationOperator : Matrix Bool Bool ℂ)
      (complexInputTwistOperator : Matrix Bool Bool ℂ) := by
    simpa [complexRotationOperator, complexInputTwistOperator] using
      complexInputTwist_not_pureInputBasisMeasurementEq
  have hnotChannel : ¬ ChannelEq
      complexRotationOperator complexInputTwistOperator := by
    intro hchannel
    apply complexInputTwist_not_global
    exact (complexGlobalPhaseEq_iff_channelEq
      complexRotationOperator complexInputTwistOperator).2 hchannel
  have hnotAll : ¬ AllMeasurementEq
      complexRotationOperator complexInputTwistOperator := by
    intro hall
    exact hnotChannel hall.channelEq
  exact ⟨hinput, hnotOutput, hinput.basisMeasurementEq, hnotPure,
    hnotChannel, hnotAll⟩

/-- Complex output-row phases preserve all pure-input basis statistics but not channels. -/
theorem complex_outputTwist_hierarchy_boundary :
    ¬ ComplexInputBasisPhaseEq
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexOutputTwistOperator : Matrix Bool Bool ℂ) ∧
      ComplexOutputBasisPhaseEq
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexOutputTwistOperator : Matrix Bool Bool ℂ) ∧
      BasisMeasurementEq State.complexWeight
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexOutputTwistOperator : Matrix Bool Bool ℂ) ∧
      PureInputBasisMeasurementEq State.complexWeight
        (complexRotationOperator : Matrix Bool Bool ℂ)
        (complexOutputTwistOperator : Matrix Bool Bool ℂ) ∧
      ¬ ChannelEq complexRotationOperator complexOutputTwistOperator ∧
      ¬ AllMeasurementEq complexRotationOperator complexOutputTwistOperator := by
  have houtput : ComplexOutputBasisPhaseEq
      (complexRotationOperator : Matrix Bool Bool ℂ)
      (complexOutputTwistOperator : Matrix Bool Bool ℂ) := by
    simpa [complexRotationOperator, complexOutputTwistOperator] using
      complexRotation_outputTwist
  have hnotInput : ¬ ComplexInputBasisPhaseEq
      (complexRotationOperator : Matrix Bool Bool ℂ)
      (complexOutputTwistOperator : Matrix Bool Bool ℂ) := by
    simpa [complexRotationOperator, complexOutputTwistOperator] using
      complexOutputTwist_not_input
  have hnotChannel : ¬ ChannelEq
      complexRotationOperator complexOutputTwistOperator := by
    intro hchannel
    apply complexOutputTwist_not_global
    exact (complexGlobalPhaseEq_iff_channelEq
      complexRotationOperator complexOutputTwistOperator).2 hchannel
  have hnotAll : ¬ AllMeasurementEq
      complexRotationOperator complexOutputTwistOperator := by
    intro hall
    exact hnotChannel hall.channelEq
  exact ⟨hnotInput, houtput, houtput.basisMeasurementEq,
    houtput.pureInputBasisMeasurementEq, hnotChannel, hnotAll⟩

/-! ## Explicit basis-measurement converse failures -/

/-- Basis measurements recover neither phase branch nor all-pure/channel behavior over `ℝ`. -/
theorem real_basisMeasurement_converse_failures :
    (∃ U V : RealUnitaryOperator Bool,
      BasisMeasurementEq State.realWeight (U : Matrix Bool Bool ℝ) V ∧
        ¬ RealOutputBasisSignEq (U : Matrix Bool Bool ℝ) V ∧
        ¬ PureInputBasisMeasurementEq State.realWeight
          (U : Matrix Bool Bool ℝ) V ∧
        ¬ ChannelEq U V) ∧
      (∃ U V : RealUnitaryOperator Bool,
        BasisMeasurementEq State.realWeight (U : Matrix Bool Bool ℝ) V ∧
          ¬ RealInputBasisSignEq (U : Matrix Bool Bool ℝ) V) := by
  exact ⟨⟨realRotationOperator, realInputTwistOperator,
      real_inputTwist_hierarchy_boundary.2.2.1,
      real_inputTwist_hierarchy_boundary.2.1,
      real_inputTwist_hierarchy_boundary.2.2.2.1,
      real_inputTwist_hierarchy_boundary.2.2.2.2.1⟩,
    ⟨realRotationOperator, realOutputTwistOperator,
      real_outputTwist_hierarchy_boundary.2.2.1,
      real_outputTwist_hierarchy_boundary.1⟩⟩

/-- Basis measurements have the analogous failed converses over `ℂ`. -/
theorem complex_basisMeasurement_converse_failures :
    (∃ U V : ComplexUnitaryOperator Bool,
      BasisMeasurementEq State.complexWeight (U : Matrix Bool Bool ℂ) V ∧
        ¬ ComplexOutputBasisPhaseEq (U : Matrix Bool Bool ℂ) V ∧
        ¬ PureInputBasisMeasurementEq State.complexWeight
          (U : Matrix Bool Bool ℂ) V ∧
        ¬ ChannelEq U V) ∧
      (∃ U V : ComplexUnitaryOperator Bool,
        BasisMeasurementEq State.complexWeight (U : Matrix Bool Bool ℂ) V ∧
          ¬ ComplexInputBasisPhaseEq (U : Matrix Bool Bool ℂ) V) := by
  exact ⟨⟨complexRotationOperator, complexInputTwistOperator,
      complex_inputTwist_hierarchy_boundary.2.2.1,
      complex_inputTwist_hierarchy_boundary.2.1,
      complex_inputTwist_hierarchy_boundary.2.2.2.1,
      complex_inputTwist_hierarchy_boundary.2.2.2.2.1⟩,
    ⟨complexRotationOperator, complexOutputTwistOperator,
      complex_outputTwist_hierarchy_boundary.2.2.1,
      complex_outputTwist_hierarchy_boundary.1⟩⟩

end QuaternionicComputing.Semantics.HierarchyAudit
