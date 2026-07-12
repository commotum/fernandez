module

public import QuaternionicComputing.Semantics.ChannelAudit
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit
public import QuaternionicComputing.Semantics.StatePhaseAudit
public import QuaternionicComputing.Semantics.BasisBehaviorAudit
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Semantics.Hierarchy.Operator
public import QuaternionicComputing.Circuit.ProductInputOrderingWitness
public import QuaternionicComputing.Matrix.KroneckerCommute

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

/-! ## Equal complex distributions do not determine a ray -/

/-- A normalized rational complex state with coordinates `3/5, 4/5`. -/
def complexCoordinateState : State.ComplexState Bool :=
  OperatorPhase.ComplexRealAudit.complexThreeFour

/-- Rotate only the `4/5` coordinate by `I`, preserving both basis weights. -/
def complexCoordinateTwistState : State.ComplexState Bool :=
  ⟨fun x ↦ if x then (4 / 5 : ℂ) * Complex.I else 3 / 5, by
    norm_num [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, Complex.normSq_apply, Fintype.univ_bool]⟩

/-- The coordinate twist preserves every computational-basis weight. -/
theorem complexCoordinate_states_basisWeightEq :
    BasisWeightEq State.complexWeight
      complexCoordinateState complexCoordinateTwistState := by
  intro x
  cases x <;>
    norm_num [State.basisWeight, State.complexWeight,
      complexCoordinateState, complexCoordinateTwistState,
      OperatorPhase.ComplexRealAudit.complexThreeFour,
      Complex.normSq_apply]

/-- The two rational states therefore induce the same normalized distribution. -/
theorem complexCoordinate_states_normalizedDistributionEq :
    NormalizedDistributionEq State.complexWeight State.complexWeight_nonneg
      complexCoordinateState complexCoordinateTwistState :=
  complexCoordinate_states_basisWeightEq.normalizedDistributionEq

/-- The coordinate-dependent phase cannot be one global complex right phase. -/
theorem complexCoordinate_states_not_phaseEq :
    ¬ ComplexStatePhaseEq complexCoordinateState complexCoordinateTwistState := by
  rintro ⟨eta, _, heta⟩
  have hfalse := congrFun heta false
  have htrue := congrFun heta true
  have hfalseRe := congrArg Complex.re hfalse
  have hfalseIm := congrArg Complex.im hfalse
  have heta_one : eta = 1 := by
    apply Complex.ext <;>
      norm_num [complexCoordinateState, complexCoordinateTwistState,
        OperatorPhase.ComplexRealAudit.complexThreeFour,
        Complex.mul_re, Complex.mul_im] at hfalseRe hfalseIm ⊢ <;>
      linarith
  subst eta
  have htrueIm := congrArg Complex.im htrue
  norm_num [complexCoordinateState, complexCoordinateTwistState,
    OperatorPhase.ComplexRealAudit.complexThreeFour] at htrueIm

/-- Equal normalized basis distributions need not give equal complex-ray constructors. -/
theorem complexCoordinate_rays_ne :
    State.ComplexRay.mk complexCoordinateState ≠
      State.ComplexRay.mk complexCoordinateTwistState := by
  intro h
  exact complexCoordinate_states_not_phaseEq
    (ComplexStatePhaseEq.iff_complexRay_mk_eq.mpr h)

/-- Complete normalized complex distribution/ray separation package. -/
theorem complex_distribution_not_ray_boundary :
    BasisWeightEq State.complexWeight
        complexCoordinateState complexCoordinateTwistState ∧
      NormalizedDistributionEq State.complexWeight State.complexWeight_nonneg
        complexCoordinateState complexCoordinateTwistState ∧
      ¬ ComplexStatePhaseEq
        complexCoordinateState complexCoordinateTwistState ∧
      State.ComplexRay.mk complexCoordinateState ≠
        State.ComplexRay.mk complexCoordinateTwistState :=
  ⟨complexCoordinate_states_basisWeightEq,
    complexCoordinate_states_normalizedDistributionEq,
    complexCoordinate_states_not_phaseEq,
    complexCoordinate_rays_ne⟩

/-! ## Quaternionic product-ordering boundaries -/

/--
The normalized outputs of the two legal product-orderings have the same full
basis distribution but are neither one right-phase state nor one ray.
-/
theorem quaternion_ground_outputs_distribution_not_ray :
    BasisWeightEq State.quaternionWeight
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      ¬ QuaternionStatePhaseEq
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
        State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput := by
  have hweights : BasisWeightEq State.quaternionWeight
      Circuit.ProductInputOrderingWitness.iThenJGroundOutput
      Circuit.ProductInputOrderingWitness.jThenIGroundOutput :=
    Circuit.ProductInputOrderingWitness.ground_outputs_basis_weights_eq
  have hnotPhase : ¬ QuaternionStatePhaseEq
      Circuit.ProductInputOrderingWitness.iThenJGroundOutput
      Circuit.ProductInputOrderingWitness.jThenIGroundOutput :=
    Circuit.ProductInputOrderingWitness.ground_outputs_not_rightPhaseEquivalent
  refine ⟨hweights, hnotPhase, ?_⟩
  intro h
  exact hnotPhase (QuaternionStatePhaseEq.iff_quaternionRay_mk_eq.mpr h)

/-- The two scheduled operators agree on every basis weight of the ground input. -/
theorem quaternion_schedules_ground_outputWeightEqAt :
    OutputWeightEqAt State.quaternionWeight
      (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
        Circuit.OrderingWitness.gateFamily)
      (Circuit.OrderingWitness.jThenISchedule.scheduledEval
        Circuit.OrderingWitness.gateFamily)
      Circuit.ProductInputOrderingWitness.groundColumn := by
  intro x
  exact Circuit.ProductInputOrderingWitness.ground_output_basis_weights_eq x

/-- The same schedules disagree on the existing normalized interference input. -/
theorem quaternion_schedules_not_pureInputBasisMeasurementEq :
    ¬ PureInputBasisMeasurementEq State.quaternionWeight
      (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
        Circuit.OrderingWitness.gateFamily)
      (Circuit.OrderingWitness.jThenISchedule.scheduledEval
        Circuit.OrderingWitness.gateFamily) := by
  intro h
  have h00 := h Circuit.OrderingWitness.inputState
    Circuit.OrderingWitness.basis00
  apply Circuit.OrderingWitness.output_basis00_weight_ne
  simpa [OutputWeightEqAt, BasisWeightEq,
    State.basisWeight, State.quaternionWeight,
    Circuit.OrderingWitness.iThenJOutput,
    Circuit.OrderingWitness.jThenIOutput,
    Circuit.LegalSchedule.scheduledEval] using h00

/--
Exact input scope of the quaternionic ordering example: equality at the one
ground input coexists with failure over all normalized pure inputs.
-/
theorem quaternion_scheduled_fixedInput_boundary :
    OutputWeightEqAt State.quaternionWeight
        (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily)
        (Circuit.OrderingWitness.jThenISchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily)
        Circuit.ProductInputOrderingWitness.groundColumn ∧
      ¬ PureInputBasisMeasurementEq State.quaternionWeight
        (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily)
        (Circuit.OrderingWitness.jThenISchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily) :=
  ⟨quaternion_schedules_ground_outputWeightEqAt,
    quaternion_schedules_not_pureInputBasisMeasurementEq⟩

/-! ## Reused diagnostic boundaries -/

/-- Existing normalized left-phase failure, with all four normalization certificates. -/
theorem normalized_quaternion_leftPhase_rejection :
    State.quaternionTotalWeight StatePhaseAudit.normalizedPhaseWitnessInput = 1 ∧
      State.quaternionTotalWeight
        StatePhaseAudit.normalizedLeftPhaseWitnessInput = 1 ∧
      State.quaternionTotalWeight StatePhaseAudit.normalizedPhaseWitnessOutput = 1 ∧
      State.quaternionTotalWeight
        StatePhaseAudit.normalizedLeftPhaseWitnessOutput = 1 ∧
      Quaternion.LeftPhaseEquivalent
        StatePhaseAudit.normalizedLeftPhaseWitnessInput
        StatePhaseAudit.normalizedPhaseWitnessInput ∧
      ¬ Quaternion.LeftPhaseEquivalent
        StatePhaseAudit.normalizedLeftPhaseWitnessOutput
        StatePhaseAudit.normalizedPhaseWitnessOutput := by
  rcases StatePhaseAudit.normalizedWitness_all_totalWeights with
    ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4,
    StatePhaseAudit.normalized_leftPhaseEquivalent_i_input,
    StatePhaseAudit.normalized_not_leftPhaseEquivalent_gate_i_input⟩

/-- The existing nonmonomial real rotations expose vacuity of raw transitions. -/
theorem raw_transition_vacuity_boundary :
    BasisBehaviorAudit.realRotation35 ∈
        unitary (Matrix Bool Bool ℝ) ∧
      BasisBehaviorAudit.realRotation513 ∈
        unitary (Matrix Bool Bool ℝ) ∧
      BasisTransitionRelationEq RealUnitSign
        BasisBehaviorAudit.realRotation35
        BasisBehaviorAudit.realRotation513 ∧
      ¬ BasisMeasurementEq State.realWeight
        BasisBehaviorAudit.realRotation35
        BasisBehaviorAudit.realRotation513 ∧
      (¬ ∃ p, RealBasisPermutationImplementation
        BasisBehaviorAudit.realRotation35 p) ∧
      (¬ ∃ p, RealBasisPermutationImplementation
        BasisBehaviorAudit.realRotation513 p) := by
  rcases BasisBehaviorAudit.unitary_vacuity_witness with
    ⟨hU, hV, _, _, hnoU, hnoV, htransition, hmeasure⟩
  exact ⟨hU, hV, htransition, hmeasure, hnoU, hnoV⟩

/-- In dimension one, a unit quaternion may fix every right ray without being central. -/
theorem quaternion_rankOne_projective_kernel_boundary :
    quaternionRankOneScalar Quaternion.j ∈
        unitary (Matrix Unit Unit ℍ[ℝ]) ∧
      QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar Quaternion.j) ∧
      ¬ QuaternionCentralSignEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar Quaternion.j) :=
  quaternionRankOneJ_exception

/-! ## Certified-classical exact equivalence aggregates -/

/-- All nine matrix equivalences remain restricted to supplied certificates. -/
theorem certified_matrix_equivalences
    {I : Type*} [DecidableEq I]
    {UR VR : Matrix I I ℝ} {UC VC : Matrix I I ℂ}
    {UQ VQ : Matrix I I ℍ[ℝ]}
    {pR qR pC qC pQ qQ : Equiv.Perm I}
    (hUR : RealBasisPermutationImplementation UR pR)
    (hVR : RealBasisPermutationImplementation VR qR)
    (hUC : ComplexBasisPermutationImplementation UC pC)
    (hVC : ComplexBasisPermutationImplementation VC qC)
    (hUQ : QuaternionBasisPermutationImplementation UQ pQ)
    (hVQ : QuaternionBasisPermutationImplementation VQ qQ) :
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
        BasisMeasurementEq State.quaternionWeight UQ VQ) :=
  ⟨sameBasisBehavior_iff_realInputBasisSignEq hUR hVR,
    sameBasisBehavior_iff_realOutputBasisSignEq hUR hVR,
    sameBasisBehavior_iff_realBasisMeasurementEq hUR hVR,
    sameBasisBehavior_iff_complexInputBasisPhaseEq hUC hVC,
    sameBasisBehavior_iff_complexOutputBasisPhaseEq hUC hVC,
    sameBasisBehavior_iff_complexBasisMeasurementEq hUC hVC,
    sameBasisBehavior_iff_quaternionInputRightPhaseEq hUQ hVQ,
    sameBasisBehavior_iff_quaternionOutputLeftPhaseEq hUQ hVQ,
    sameBasisBehavior_iff_quaternionBasisMeasurementEq hUQ hVQ⟩

/-- All nine circuit equivalences remain restricted to certified circuit bundles. -/
theorem certified_circuit_equivalences
    {W : Type*} [Fintype W]
    (CR DR : RealBasisClassicalCircuit W)
    (CC DC : ComplexBasisClassicalCircuit W)
    (CQ DQ : QuaternionBasisClassicalCircuit W) :
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
        BasisMeasurementEq State.quaternionWeight
          CQ.circuit.eval DQ.circuit.eval) :=
  ⟨SameCircuitBasisBehavior.iff_realCircuitInputBasisSignEq,
    SameCircuitBasisBehavior.iff_realCircuitOutputBasisSignEq,
    SameCircuitBasisBehavior.iff_realBasisMeasurementEq,
    SameCircuitBasisBehavior.iff_complexCircuitInputBasisPhaseEq,
    SameCircuitBasisBehavior.iff_complexCircuitOutputBasisPhaseEq,
    SameCircuitBasisBehavior.iff_complexBasisMeasurementEq,
    SameCircuitBasisBehavior.iff_quaternionCircuitInputRightPhaseEq,
    SameCircuitBasisBehavior.iff_quaternionCircuitOutputLeftPhaseEq,
    SameCircuitBasisBehavior.iff_quaternionBasisMeasurementEq⟩

/-! ## Exact Stage 8 stable-API aggregates -/

/-!
The following twelve theorem groups consume the `49` Stage 8 stable exports
exactly once: `9` from `Hierarchy.OutputPhase`, `13` from `Hierarchy.State`,
and `27` from `Hierarchy.Operator`.
-/

/-- Consumer for the three scalar-specialized basis-input consequences. -/
theorem outputPhase_basisConsequences_api
    {O I : Type*} [Fintype I]
    {UR VR : Matrix O I ℝ} {UC VC : Matrix O I ℂ}
    {UQ VQ : Matrix O I ℍ[ℝ]}
    (hR : PureInputBasisMeasurementEq State.realWeight UR VR)
    (hC : PureInputBasisMeasurementEq State.complexWeight UC VC)
    (hQ : PureInputBasisMeasurementEq State.quaternionWeight UQ VQ) :
    BasisMeasurementEq State.realWeight UR VR ∧
      BasisMeasurementEq State.complexWeight UC VC ∧
      BasisMeasurementEq State.quaternionWeight UQ VQ :=
  ⟨PureInputBasisMeasurementEq.realBasisMeasurementEq hR,
    PureInputBasisMeasurementEq.complexBasisMeasurementEq hC,
    PureInputBasisMeasurementEq.quaternionBasisMeasurementEq hQ⟩

/-- Consumer for all three rectangular row-functional converse theorems. -/
theorem outputPhase_rowConverses_api
    {O I : Type*} [Fintype I]
    {UR VR : Matrix O I ℝ} {UC VC : Matrix O I ℂ}
    {UQ VQ : Matrix O I ℍ[ℝ]}
    (hR : PureInputBasisMeasurementEq State.realWeight UR VR)
    (hC : PureInputBasisMeasurementEq State.complexWeight UC VC)
    (hQ : PureInputBasisMeasurementEq State.quaternionWeight UQ VQ) :
    RealOutputBasisSignEq UR VR ∧
      ComplexOutputBasisPhaseEq UC VC ∧
      QuaternionOutputLeftPhaseEq UQ VQ :=
  ⟨PureInputBasisMeasurementEq.realOutputBasisSignEq hR,
    PureInputBasisMeasurementEq.complexOutputBasisPhaseEq hC,
    PureInputBasisMeasurementEq.quaternionOutputLeftPhaseEq hQ⟩

/-- Consumer for the three exact output-phase/all-pure characterizations. -/
theorem outputPhase_characterizations_api
    {O I : Type*} [Fintype I]
    (UR VR : Matrix O I ℝ) (UC VC : Matrix O I ℂ)
    (UQ VQ : Matrix O I ℍ[ℝ]) :
    (RealOutputBasisSignEq UR VR ↔
        PureInputBasisMeasurementEq State.realWeight UR VR) ∧
      (ComplexOutputBasisPhaseEq UC VC ↔
        PureInputBasisMeasurementEq State.complexWeight UC VC) ∧
      (QuaternionOutputLeftPhaseEq UQ VQ ↔
        PureInputBasisMeasurementEq State.quaternionWeight UQ VQ) :=
  ⟨realOutputBasisSignEq_iff_pureInputBasisMeasurementEq UR VR,
    complexOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq UC VC,
    quaternionOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq UQ VQ⟩

/-! ## Local axiom endpoints -/

#print axioms real_inputTwist_hierarchy_boundary
#print axioms real_outputTwist_hierarchy_boundary
#print axioms complex_inputTwist_hierarchy_boundary
#print axioms complex_outputTwist_hierarchy_boundary
#print axioms real_basisMeasurement_converse_failures
#print axioms complex_basisMeasurement_converse_failures
#print axioms complex_distribution_not_ray_boundary
#print axioms quaternion_ground_outputs_distribution_not_ray
#print axioms quaternion_scheduled_fixedInput_boundary
#print axioms normalized_quaternion_leftPhase_rejection
#print axioms raw_transition_vacuity_boundary
#print axioms quaternion_rankOne_projective_kernel_boundary
#print axioms certified_matrix_equivalences
#print axioms certified_circuit_equivalences

end QuaternionicComputing.Semantics.HierarchyAudit
