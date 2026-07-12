module

public import QuaternionicComputing.Semantics.ChannelAudit
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit
public import QuaternionicComputing.Semantics.StatePhaseAudit
public import QuaternionicComputing.Semantics.BasisBehaviorAudit
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Semantics.Hierarchy.Operator
public import QuaternionicComputing.Semantics.Hierarchy.State
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

open scoped Matrix Kronecker Quaternion

namespace QuaternionicComputing.Semantics.HierarchyAudit

universe u v

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

/-- Consumer for the three finite-distribution extensional characterizations. -/
theorem finiteDistribution_characterizations_api
    {I : Type u} [Fintype I]
    (mu nu : State.FiniteDistribution I) :
    (mu = nu ↔
        ∀ x : I, mu.eventWeight {x} = nu.eventWeight {x}) ∧
      (mu = nu ↔
        ∀ event : Finset I, mu.eventWeight event = nu.eventWeight event) ∧
      (mu = nu ↔
        ∀ (J : Type u) [Fintype J] (f : I → J),
          @State.FiniteDistribution.pushforward I J _ _ mu f =
            @State.FiniteDistribution.pushforward I J _ _ nu f) :=
  ⟨State.FiniteDistribution.eq_iff_singletonEventWeight_eq,
    State.FiniteDistribution.eq_iff_eventWeight_eq,
    State.FiniteDistribution.eq_iff_allPushforward_eq_sameUniverse⟩

/-- Consumer for all four normalized-state event and pushforward wrappers. -/
theorem normalizedState_observationCharacterizations_api
    {R : Type u} {I : Type v} [Fintype I]
    (weight : R → ℝ) (hweight : ∀ z, 0 ≤ weight z)
    (a b : State.NormalizedState I R weight) :
    (NormalizedDistributionEq weight hweight a b ↔
        ∀ event : Finset I,
          (State.FiniteDistribution.ofNormalizedState
              weight hweight a).eventWeight event =
            (State.FiniteDistribution.ofNormalizedState
              weight hweight b).eventWeight event) ∧
      (NormalizedDistributionEq weight hweight a b ↔
        ∀ (J : Type v) [Fintype J] (f : I → J),
          @State.FiniteDistribution.pushforward I J _ _
              (State.FiniteDistribution.ofNormalizedState weight hweight a) f =
            @State.FiniteDistribution.pushforward I J _ _
              (State.FiniteDistribution.ofNormalizedState weight hweight b) f) ∧
      (BasisWeightEq weight a b ↔
        ∀ event : Finset I,
          (State.FiniteDistribution.ofNormalizedState
              weight hweight a).eventWeight event =
            (State.FiniteDistribution.ofNormalizedState
              weight hweight b).eventWeight event) ∧
      (BasisWeightEq weight a b ↔
        ∀ (J : Type v) [Fintype J] (f : I → J),
          @State.FiniteDistribution.pushforward I J _ _
              (State.FiniteDistribution.ofNormalizedState weight hweight a) f =
            @State.FiniteDistribution.pushforward I J _ _
              (State.FiniteDistribution.ofNormalizedState weight hweight b) f) :=
  ⟨normalizedDistributionEq_iff_eventWeight_eq weight hweight a b,
    normalizedDistributionEq_iff_allPushforward_eq_sameUniverse
      weight hweight a b,
    basisWeightEq_iff_eventWeight_eq weight hweight a b,
    basisWeightEq_iff_allPushforward_eq_sameUniverse weight hweight a b⟩

/-- Consumer for all six exact-representative/ray/basis-weight arrows. -/
theorem stateRay_chain_api
    {I : Type u} [Fintype I]
    {aR bR : State.RealState I}
    {aC bC : State.ComplexState I}
    {aQ bQ : State.QuaternionState I}
    (hR : ExactStateEq aR bR)
    (hC : ExactStateEq aC bC)
    (hQ : ExactStateEq aQ bQ) :
    State.RealRay.mk aR = State.RealRay.mk bR ∧
      State.ComplexRay.mk aC = State.ComplexRay.mk bC ∧
      State.QuaternionRay.mk aQ = State.QuaternionRay.mk bQ ∧
      BasisWeightEq State.realWeight aR bR ∧
      BasisWeightEq State.complexWeight aC bC ∧
      BasisWeightEq State.quaternionWeight aQ bQ := by
  have hRray := ExactStateEq.realRay_mk_eq hR
  have hCray := ExactStateEq.complexRay_mk_eq hC
  have hQray := ExactStateEq.quaternionRay_mk_eq hQ
  exact ⟨hRray, hCray, hQray,
    RealStatePhaseEq.basisWeightEq_of_realRay_mk_eq hRray,
    ComplexStatePhaseEq.basisWeightEq_of_complexRay_mk_eq hCray,
    QuaternionStatePhaseEq.basisWeightEq_of_quaternionRay_mk_eq hQray⟩

/-- Consumer for the two real/complex global-phase/projective kernel iff theorems. -/
theorem operator_projectiveKernel_api
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (UR VR : RealUnitaryOperator I)
    (UC VC : ComplexUnitaryOperator I) :
    (RealGlobalSignEq (UR : Matrix I I ℝ) (VR : Matrix I I ℝ) ↔
        RealProjectiveActionEq
          (UR : Matrix I I ℝ) (VR : Matrix I I ℝ)) ∧
      (ComplexGlobalPhaseEq
          (UC : Matrix I I ℂ) (VC : Matrix I I ℂ) ↔
        ComplexProjectiveActionEq
          (UC : Matrix I I ℂ) (VC : Matrix I I ℂ)) :=
  ⟨realGlobalSignEq_iff_projectiveActionEq UR VR,
    complexGlobalPhaseEq_iff_projectiveActionEq UC VC⟩

/-- Consumer for all six matrix-level consequences of `ChannelEq`. -/
theorem channel_hierarchy_api
    {IR IC : Type*}
    [Fintype IR] [DecidableEq IR] [Fintype IC] [DecidableEq IC]
    {UR VR : RealUnitaryOperator IR}
    {UC VC : ComplexUnitaryOperator IC}
    (hR : ChannelEq UR VR) (hC : ChannelEq UC VC) :
    PureInputBasisMeasurementEq State.realWeight
        (UR : Matrix IR IR ℝ) (VR : Matrix IR IR ℝ) ∧
      PureInputBasisMeasurementEq State.complexWeight
        (UC : Matrix IC IC ℂ) (VC : Matrix IC IC ℂ) ∧
      RealOutputBasisSignEq
        (UR : Matrix IR IR ℝ) (VR : Matrix IR IR ℝ) ∧
      ComplexOutputBasisPhaseEq
        (UC : Matrix IC IC ℂ) (VC : Matrix IC IC ℂ) ∧
      BasisMeasurementEq State.realWeight
        (UR : Matrix IR IR ℝ) (VR : Matrix IR IR ℝ) ∧
      BasisMeasurementEq State.complexWeight
        (UC : Matrix IC IC ℂ) (VC : Matrix IC IC ℂ) :=
  ⟨ChannelEq.realPureInputBasisMeasurementEq hR,
    ChannelEq.complexPureInputBasisMeasurementEq hC,
    ChannelEq.realOutputBasisSignEq hR,
    ChannelEq.complexOutputBasisPhaseEq hC,
    ChannelEq.realBasisMeasurementEq hR,
    ChannelEq.complexBasisMeasurementEq hC⟩

/-- Consumer for all four matrix-level consequences of `AllMeasurementEq`. -/
theorem allMeasurement_hierarchy_api
    {IR IC : Type*}
    [Fintype IR] [DecidableEq IR] [Fintype IC] [DecidableEq IC]
    {UR VR : RealUnitaryOperator IR}
    {UC VC : ComplexUnitaryOperator IC}
    (hR : AllMeasurementEq UR VR) (hC : AllMeasurementEq UC VC) :
    PureInputBasisMeasurementEq State.realWeight
        (UR : Matrix IR IR ℝ) (VR : Matrix IR IR ℝ) ∧
      PureInputBasisMeasurementEq State.complexWeight
        (UC : Matrix IC IC ℂ) (VC : Matrix IC IC ℂ) ∧
      BasisMeasurementEq State.realWeight
        (UR : Matrix IR IR ℝ) (VR : Matrix IR IR ℝ) ∧
      BasisMeasurementEq State.complexWeight
        (UC : Matrix IC IC ℂ) (VC : Matrix IC IC ℂ) :=
  ⟨AllMeasurementEq.realPureInputBasisMeasurementEq hR,
    AllMeasurementEq.complexPureInputBasisMeasurementEq hC,
    AllMeasurementEq.realBasisMeasurementEq hR,
    AllMeasurementEq.complexBasisMeasurementEq hC⟩

/-- Consumer for the five evaluator-backed circuit characterizations. -/
theorem circuit_characterizations_api
    {W : Type*} [Fintype W]
    (R C : Circuit.OrderedCircuit ℝ W)
    (K L : Circuit.OrderedCircuit ℂ W)
    (Q T : Circuit.OrderedCircuit ℍ[ℝ] W)
    (UR VR : RealUnitaryCircuit W)
    (UC VC : ComplexUnitaryCircuit W) :
    (RealCircuitOutputBasisSignEq R C ↔
        PureInputBasisMeasurementEq State.realWeight R.eval C.eval) ∧
      (ComplexCircuitOutputBasisPhaseEq K L ↔
        PureInputBasisMeasurementEq State.complexWeight K.eval L.eval) ∧
      (QuaternionCircuitOutputLeftPhaseEq Q T ↔
        PureInputBasisMeasurementEq State.quaternionWeight Q.eval T.eval) ∧
      (RealCircuitGlobalSignEq UR.circuit VR.circuit ↔
        RealCircuitProjectiveActionEq UR.circuit VR.circuit) ∧
      (ComplexCircuitGlobalPhaseEq UC.circuit VC.circuit ↔
        ComplexCircuitProjectiveActionEq UC.circuit VC.circuit) :=
  ⟨realCircuitOutputBasisSignEq_iff_pureInputBasisMeasurementEq R C,
    complexCircuitOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq K L,
    quaternionCircuitOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq Q T,
    realCircuitGlobalSignEq_iff_projectiveActionEq UR VR,
    complexCircuitGlobalPhaseEq_iff_projectiveActionEq UC VC⟩

/-- Consumer for all six consequences of `CircuitChannelEq`. -/
theorem circuitChannel_hierarchy_api
    {WR WC : Type*} [Fintype WR] [Fintype WC]
    {UR VR : RealUnitaryCircuit WR}
    {UC VC : ComplexUnitaryCircuit WC}
    (hR : CircuitChannelEq UR VR) (hC : CircuitChannelEq UC VC) :
    PureInputBasisMeasurementEq State.realWeight
        UR.circuit.eval VR.circuit.eval ∧
      PureInputBasisMeasurementEq State.complexWeight
        UC.circuit.eval VC.circuit.eval ∧
      RealCircuitOutputBasisSignEq UR.circuit VR.circuit ∧
      ComplexCircuitOutputBasisPhaseEq UC.circuit VC.circuit ∧
      BasisMeasurementEq State.realWeight UR.circuit.eval VR.circuit.eval ∧
      BasisMeasurementEq State.complexWeight UC.circuit.eval VC.circuit.eval :=
  ⟨CircuitChannelEq.realPureInputBasisMeasurementEq hR,
    CircuitChannelEq.complexPureInputBasisMeasurementEq hC,
    CircuitChannelEq.realOutputBasisSignEq hR,
    CircuitChannelEq.complexOutputBasisPhaseEq hC,
    CircuitChannelEq.realBasisMeasurementEq hR,
    CircuitChannelEq.complexBasisMeasurementEq hC⟩

/-- Consumer for all four consequences of `CircuitAllMeasurementEq`. -/
theorem circuitAllMeasurement_hierarchy_api
    {WR WC : Type*} [Fintype WR] [Fintype WC]
    {UR VR : RealUnitaryCircuit WR}
    {UC VC : ComplexUnitaryCircuit WC}
    (hR : CircuitAllMeasurementEq UR VR)
    (hC : CircuitAllMeasurementEq UC VC) :
    PureInputBasisMeasurementEq State.realWeight
        UR.circuit.eval VR.circuit.eval ∧
      PureInputBasisMeasurementEq State.complexWeight
        UC.circuit.eval VC.circuit.eval ∧
      BasisMeasurementEq State.realWeight UR.circuit.eval VR.circuit.eval ∧
      BasisMeasurementEq State.complexWeight UC.circuit.eval VC.circuit.eval :=
  ⟨CircuitAllMeasurementEq.realPureInputBasisMeasurementEq hR,
    CircuitAllMeasurementEq.complexPureInputBasisMeasurementEq hC,
    CircuitAllMeasurementEq.realBasisMeasurementEq hR,
    CircuitAllMeasurementEq.complexBasisMeasurementEq hC⟩

/-! ### Explicit rectangular and finite-type boundaries -/

/--
The three output-phase iff theorems instantiate uniformly on a genuine
`3 × 2` rectangle, an empty input type, and an empty output type.
-/
theorem outputPhase_rectangular_empty_boundaries_api
    (RR SR : Matrix (Fin 3) Bool ℝ)
    (RC SC : Matrix (Fin 3) Bool ℂ)
    (RQ SQ : Matrix (Fin 3) Bool ℍ[ℝ])
    (EIR EIS : Matrix Unit Empty ℝ)
    (EIC EIT : Matrix Unit Empty ℂ)
    (EIQ EIU : Matrix Unit Empty ℍ[ℝ])
    (EOR EOS : Matrix Empty Unit ℝ)
    (EOC EOT : Matrix Empty Unit ℂ)
    (EOQ EOU : Matrix Empty Unit ℍ[ℝ]) :
    (RealOutputBasisSignEq RR SR ↔
        PureInputBasisMeasurementEq State.realWeight RR SR) ∧
      (ComplexOutputBasisPhaseEq RC SC ↔
        PureInputBasisMeasurementEq State.complexWeight RC SC) ∧
      (QuaternionOutputLeftPhaseEq RQ SQ ↔
        PureInputBasisMeasurementEq State.quaternionWeight RQ SQ) ∧
      (RealOutputBasisSignEq EIR EIS ↔
        PureInputBasisMeasurementEq State.realWeight EIR EIS) ∧
      (ComplexOutputBasisPhaseEq EIC EIT ↔
        PureInputBasisMeasurementEq State.complexWeight EIC EIT) ∧
      (QuaternionOutputLeftPhaseEq EIQ EIU ↔
        PureInputBasisMeasurementEq State.quaternionWeight EIQ EIU) ∧
      (RealOutputBasisSignEq EOR EOS ↔
        PureInputBasisMeasurementEq State.realWeight EOR EOS) ∧
      (ComplexOutputBasisPhaseEq EOC EOT ↔
        PureInputBasisMeasurementEq State.complexWeight EOC EOT) ∧
      (QuaternionOutputLeftPhaseEq EOQ EOU ↔
        PureInputBasisMeasurementEq State.quaternionWeight EOQ EOU) := by
  rcases outputPhase_characterizations_api RR SR RC SC RQ SQ with
    ⟨hRR, hRC, hRQ⟩
  rcases outputPhase_characterizations_api EIR EIS EIC EIT EIQ EIU with
    ⟨hIR, hIC, hIQ⟩
  rcases outputPhase_characterizations_api EOR EOS EOC EOT EOQ EOU with
    ⟨hOR, hOC, hOQ⟩
  exact ⟨hRR, hRC, hRQ, hIR, hIC, hIQ, hOR, hOC, hOQ⟩

/-- The unique concrete probability distribution on `Unit`. -/
def unitFiniteDistribution : State.FiniteDistribution Unit where
  weight _ := 1
  nonnegative _ := by norm_num
  normalized := by simp

/-- A probability distribution cannot inhabit the empty outcome type. -/
theorem emptyFiniteDistribution_isEmpty :
    IsEmpty (State.FiniteDistribution Empty) :=
  ⟨fun mu ↦ by simpa using mu.normalized⟩

/--
The empty boundary is constructive impossibility; the `Unit` boundary is an
actual event and same-universe pushforward consumer.
-/
theorem finiteDistribution_empty_unit_boundaries_api :
    IsEmpty (State.FiniteDistribution Empty) ∧
      ((unitFiniteDistribution = unitFiniteDistribution ↔
        ∀ event : Finset Unit,
          unitFiniteDistribution.eventWeight event =
            unitFiniteDistribution.eventWeight event) ∧
      (unitFiniteDistribution = unitFiniteDistribution ↔
        ∀ (J : Type) [Fintype J] (f : Unit → J),
          @State.FiniteDistribution.pushforward Unit J _ _
              unitFiniteDistribution f =
            @State.FiniteDistribution.pushforward Unit J _ _
              unitFiniteDistribution f)) := by
  have hUnit := finiteDistribution_characterizations_api
    unitFiniteDistribution unitFiniteDistribution
  exact ⟨emptyFiniteDistribution_isEmpty, hUnit.2.1, hUnit.2.2⟩

/-- The concrete normalized real state on the singleton outcome type. -/
def unitRealState : State.RealState Unit :=
  ⟨fun _ ↦ 1, by
    simp [State.totalWeight, State.basisWeight, State.realWeight]⟩

/-- A normalized real state cannot inhabit an empty coordinate type. -/
theorem emptyRealState_isEmpty : IsEmpty (State.RealState Empty) :=
  ⟨fun a ↦ by simpa [State.totalWeight] using a.property⟩

/--
The normalized-state empty boundary is constructive impossibility; the
singleton state concretely exercises both observation iff theorems.
-/
theorem normalizedState_empty_unit_boundaries_api :
    IsEmpty (State.RealState Empty) ∧
      ((NormalizedDistributionEq State.realWeight State.realWeight_nonneg
          unitRealState unitRealState ↔
        ∀ event : Finset Unit,
          (State.FiniteDistribution.ofNormalizedState State.realWeight
              State.realWeight_nonneg unitRealState).eventWeight event =
            (State.FiniteDistribution.ofNormalizedState State.realWeight
              State.realWeight_nonneg unitRealState).eventWeight event) ∧
      (NormalizedDistributionEq State.realWeight State.realWeight_nonneg
          unitRealState unitRealState ↔
        ∀ (J : Type) [Fintype J] (f : Unit → J),
          @State.FiniteDistribution.pushforward Unit J _ _
              (State.FiniteDistribution.ofNormalizedState State.realWeight
                State.realWeight_nonneg unitRealState) f =
            @State.FiniteDistribution.pushforward Unit J _ _
              (State.FiniteDistribution.ofNormalizedState State.realWeight
                State.realWeight_nonneg unitRealState) f)) := by
  have hUnit := normalizedState_observationCharacterizations_api
    State.realWeight State.realWeight_nonneg unitRealState unitRealState
  exact ⟨emptyRealState_isEmpty, hUnit.1, hUnit.2.1⟩

/-! ## Existing strictness, preservation, and ordering consumers -/

/-- Real and complex global phase are strictly weaker than exact equality on unitaries. -/
theorem real_complex_exact_global_strictness :
    OperatorPhase.ComplexRealAudit.realRotation ∈
        unitary (Matrix Bool Bool ℝ) ∧
      OperatorPhase.ComplexRealAudit.realNegRotation ∈
        unitary (Matrix Bool Bool ℝ) ∧
      RealGlobalSignEq
        OperatorPhase.ComplexRealAudit.realRotation
        OperatorPhase.ComplexRealAudit.realNegRotation ∧
      ¬ ExactOperatorEq
        OperatorPhase.ComplexRealAudit.realRotation
        OperatorPhase.ComplexRealAudit.realNegRotation ∧
      OperatorPhase.ComplexRealAudit.complexRotation ∈
        unitary (Matrix Bool Bool ℂ) ∧
      OperatorPhase.ComplexRealAudit.complexIRotation ∈
        unitary (Matrix Bool Bool ℂ) ∧
      ComplexGlobalPhaseEq
        OperatorPhase.ComplexRealAudit.complexRotation
        OperatorPhase.ComplexRealAudit.complexIRotation ∧
      ¬ ExactOperatorEq
        OperatorPhase.ComplexRealAudit.complexRotation
        OperatorPhase.ComplexRealAudit.complexIRotation :=
  ⟨OperatorPhase.ComplexRealAudit.realRotation_mem_unitary,
    OperatorPhase.ComplexRealAudit.realNegRotation_mem_unitary,
    OperatorPhase.ComplexRealAudit.realRotation_neg_global,
    OperatorPhase.ComplexRealAudit.realRotation_neg_not_exact,
    OperatorPhase.ComplexRealAudit.complexRotation_mem_unitary,
    OperatorPhase.ComplexRealAudit.complexIRotation_mem_unitary,
    OperatorPhase.ComplexRealAudit.complexRotation_I_global,
    OperatorPhase.ComplexRealAudit.complexRotation_I_not_exact⟩

/-- Exact and global/central phase preserve all certified matrix permutations. -/
theorem certified_matrix_preservation_api
    {I : Type*} [DecidableEq I]
    {UR VR : Matrix I I ℝ} {UC VC : Matrix I I ℂ}
    {UQ VQ : Matrix I I ℍ[ℝ]}
    {pR qR pC qC pQ qQ : Equiv.Perm I}
    (hUR : RealBasisPermutationImplementation UR pR)
    (hVR : RealBasisPermutationImplementation VR qR)
    (hUC : ComplexBasisPermutationImplementation UC pC)
    (hVC : ComplexBasisPermutationImplementation VC qC)
    (hUQ : QuaternionBasisPermutationImplementation UQ pQ)
    (hVQ : QuaternionBasisPermutationImplementation VQ qQ)
    (heR : ExactOperatorEq UR VR)
    (heC : ExactOperatorEq UC VC)
    (heQ : ExactOperatorEq UQ VQ)
    (hpR : RealGlobalSignEq UR VR)
    (hpC : ComplexGlobalPhaseEq UC VC)
    (hpQ : QuaternionCentralSignEq UQ VQ) :
    SameBasisBehavior hUR hVR ∧ SameBasisBehavior hUC hVC ∧
      SameBasisBehavior hUQ hVQ ∧ SameBasisBehavior hUR hVR ∧
      SameBasisBehavior hUC hVC ∧ SameBasisBehavior hUQ hVQ :=
  ⟨ExactOperatorEq.realSameBasisBehavior heR hUR hVR,
    ExactOperatorEq.complexSameBasisBehavior heC hUC hVC,
    ExactOperatorEq.quaternionSameBasisBehavior heQ hUQ hVQ,
    RealGlobalSignEq.sameBasisBehavior hpR hUR hVR,
    ComplexGlobalPhaseEq.sameBasisBehavior hpC hUC hVC,
    QuaternionCentralSignEq.sameBasisBehavior hpQ hUQ hVQ⟩

/-- Exact and global/central phase preserve all certified circuit permutations. -/
theorem certified_circuit_preservation_api
    {W : Type*} [Fintype W]
    {CR DR : RealBasisClassicalCircuit W}
    {CC DC : ComplexBasisClassicalCircuit W}
    {CQ DQ : QuaternionBasisClassicalCircuit W}
    (heR : ExactCircuitEq CR.circuit DR.circuit)
    (heC : ExactCircuitEq CC.circuit DC.circuit)
    (heQ : ExactCircuitEq CQ.circuit DQ.circuit)
    (hpR : RealCircuitGlobalSignEq CR.circuit DR.circuit)
    (hpC : ComplexCircuitGlobalPhaseEq CC.circuit DC.circuit)
    (hpQ : QuaternionCircuitCentralSignEq CQ.circuit DQ.circuit) :
    SameCircuitBasisBehavior CR DR ∧ SameCircuitBasisBehavior CC DC ∧
      SameCircuitBasisBehavior CQ DQ ∧ SameCircuitBasisBehavior CR DR ∧
      SameCircuitBasisBehavior CC DC ∧ SameCircuitBasisBehavior CQ DQ :=
  ⟨ExactCircuitEq.realSameCircuitBasisBehavior heR,
    ExactCircuitEq.complexSameCircuitBasisBehavior heC,
    ExactCircuitEq.quaternionSameCircuitBasisBehavior heQ,
    RealCircuitGlobalSignEq.sameCircuitBasisBehavior hpR,
    ComplexCircuitGlobalPhaseEq.sameCircuitBasisBehavior hpC,
    QuaternionCircuitCentralSignEq.sameCircuitBasisBehavior hpQ⟩

/--
Commuting scheduled denotations are order-independent, while the existing
quaternionic schedule and one-by-one Kronecker witnesses exhibit the exact
noncommutative failures.
-/
theorem schedule_kronecker_boundary_api
    {R ι W : Type*} [Semiring R] [Fintype ι] [DecidableEq ι] [Fintype W]
    {precedes : ι → ι → Prop}
    (s t : Circuit.LegalSchedule ι precedes)
    (gates : ι → Circuit.PlacedGate R W)
    (hcomm : Pairwise fun i j : ι ↦
      Commute (gates i).denote (gates j).denote) :
    s.scheduledEval gates = t.scheduledEval gates ∧
      Circuit.OrderingWitness.iThenJSchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily ≠
        Circuit.OrderingWitness.jThenISchedule.scheduledEval
          Circuit.OrderingWitness.gateFamily ∧
      (¬ QuaternionicComputing.Matrix.IsZeroOneMatrix
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
            Quaternion.i) ∧
        ¬ QuaternionicComputing.Matrix.IsZeroOneMatrix
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
            Quaternion.j) ∧
        (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i) *
            (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i ⊗ₖ
              QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j) =
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j *
              QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i) ⊗ₖ
            (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i *
              QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j)) ∧
      ¬ ((QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1 ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i) *
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1) =
        (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1 *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.j) ⊗ₖ
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne Quaternion.i *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1)) :=
  ⟨Circuit.LegalSchedule.scheduledEval_eq_of_pairwise_commute s t gates hcomm,
    Circuit.OrderingWitness.scheduled_operators_ne,
    QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_without_zeroOne,
    QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_i_j_failure⟩

/-! ## Local axiom endpoints -/

#print axioms outputPhase_basisConsequences_api
#print axioms outputPhase_rowConverses_api
#print axioms outputPhase_characterizations_api
#print axioms finiteDistribution_characterizations_api
#print axioms normalizedState_observationCharacterizations_api
#print axioms stateRay_chain_api
#print axioms operator_projectiveKernel_api
#print axioms channel_hierarchy_api
#print axioms allMeasurement_hierarchy_api
#print axioms circuit_characterizations_api
#print axioms circuitChannel_hierarchy_api
#print axioms circuitAllMeasurement_hierarchy_api
#print axioms outputPhase_rectangular_empty_boundaries_api
#print axioms finiteDistribution_empty_unit_boundaries_api
#print axioms normalizedState_empty_unit_boundaries_api
#print axioms real_complex_exact_global_strictness
#print axioms certified_matrix_preservation_api
#print axioms certified_circuit_preservation_api
#print axioms schedule_kronecker_boundary_api
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
