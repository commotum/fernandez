module

public import QuaternionicComputing.Semantics.Hierarchy.OutputPhase
public import QuaternionicComputing.Semantics.ChannelCircuit
public import QuaternionicComputing.Semantics.OperatorPhase.QuaternionCircuit

/-!
# Same-space operator and circuit semantic hierarchy

This leaf exposes the remaining covering arrows in the real and complex
unitary hierarchy and lifts the output-row characterization through
`OrderedCircuit.eval`.  It composes the already checked channel/projective
kernel with `Hierarchy.OutputPhase`; it does not reprove either result.

Channel equality still means equality of complete density evolution and
all-measurement equality still quantifies over genuine effects.  The
conclusions below are deliberately weaker computational-basis observations.
Conversely, output-row phase or all-pure-input basis agreement is not promoted
to channel equality; the non-root hierarchy audit supplies exact unitary
counterexamples.

The quaternionic declarations in this leaf are limited to the evaluator-backed
output-left-phase characterization.  There is no quaternionic density or
channel claim.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Direct phase/projective kernel edges -/

/-- On inhabited real unitary spaces, global sign is exactly projective action. -/
theorem realGlobalSignEq_iff_projectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : RealUnitaryOperator I) :
    RealGlobalSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔
      RealProjectiveActionEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  (realGlobalSignEq_iff_channelEq U V).trans
    (realProjectiveActionEq_iff_channelEq U V).symm

/-- On inhabited complex unitary spaces, global phase is exactly projective action. -/
theorem complexGlobalPhaseEq_iff_projectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : ComplexUnitaryOperator I) :
    ComplexGlobalPhaseEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔
      ComplexProjectiveActionEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  (complexGlobalPhaseEq_iff_channelEq U V).trans
    (complexProjectiveActionEq_iff_channelEq U V).symm

/-! ## Computational-basis consequences of physical channel equality -/

namespace ChannelEq

/-- Equal real channels agree on basis outcomes for every normalized pure input. -/
theorem realPureInputBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : ChannelEq U V) :
    PureInputBasisMeasurementEq State.realWeight
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.realProjectiveActionEq.pureInputBasisMeasurementEq

/-- Equal complex channels agree on basis outcomes for every normalized pure input. -/
theorem complexPureInputBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : ChannelEq U V) :
    PureInputBasisMeasurementEq State.complexWeight
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.complexProjectiveActionEq.pureInputBasisMeasurementEq

/-- Equal real channels differ by one unit sign on each output row. -/
theorem realOutputBasisSignEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : ChannelEq U V) :
    RealOutputBasisSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.realPureInputBasisMeasurementEq.realOutputBasisSignEq

/-- Equal complex channels differ by one unit phase on each output row. -/
theorem complexOutputBasisPhaseEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : ChannelEq U V) :
    ComplexOutputBasisPhaseEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.complexPureInputBasisMeasurementEq.complexOutputBasisPhaseEq

/-- Equal real channels agree on every computational-basis transition weight. -/
theorem realBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : ChannelEq U V) :
    BasisMeasurementEq State.realWeight
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.realPureInputBasisMeasurementEq.realBasisMeasurementEq

/-- Equal complex channels agree on every computational-basis transition weight. -/
theorem complexBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : ChannelEq U V) :
    BasisMeasurementEq State.complexWeight
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.complexPureInputBasisMeasurementEq.complexBasisMeasurementEq

end ChannelEq

namespace AllMeasurementEq

/-- All genuine-effect agreement implies every real pure-input basis statistic. -/
theorem realPureInputBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : AllMeasurementEq U V) :
    PureInputBasisMeasurementEq State.realWeight
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.channelEq.realPureInputBasisMeasurementEq

/-- All genuine-effect agreement implies every complex pure-input basis statistic. -/
theorem complexPureInputBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : AllMeasurementEq U V) :
    PureInputBasisMeasurementEq State.complexWeight
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.channelEq.complexPureInputBasisMeasurementEq

/-- All genuine-effect agreement implies real basis-transition agreement. -/
theorem realBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : AllMeasurementEq U V) :
    BasisMeasurementEq State.realWeight
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.channelEq.realBasisMeasurementEq

/-- All genuine-effect agreement implies complex basis-transition agreement. -/
theorem complexBasisMeasurementEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : AllMeasurementEq U V) :
    BasisMeasurementEq State.complexWeight
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.channelEq.complexBasisMeasurementEq

end AllMeasurementEq

/-! ## Evaluator-backed output-row characterizations -/

/-- Real circuit evaluators have output-row signs iff all pure-input basis weights agree. -/
theorem realCircuitOutputBasisSignEq_iff_pureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℝ W) :
    RealCircuitOutputBasisSignEq C D ↔
      PureInputBasisMeasurementEq State.realWeight C.eval D.eval := by
  change RealOutputBasisSignEq C.eval D.eval ↔
    PureInputBasisMeasurementEq State.realWeight C.eval D.eval
  exact realOutputBasisSignEq_iff_pureInputBasisMeasurementEq C.eval D.eval

/-- Complex circuit evaluators have output-row phases iff all pure-input basis weights agree. -/
theorem complexCircuitOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℂ W) :
    ComplexCircuitOutputBasisPhaseEq C D ↔
      PureInputBasisMeasurementEq State.complexWeight C.eval D.eval := by
  change ComplexOutputBasisPhaseEq C.eval D.eval ↔
    PureInputBasisMeasurementEq State.complexWeight C.eval D.eval
  exact complexOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq C.eval D.eval

/-- Quaternionic circuit evaluators have output-left phases iff all pure basis weights agree. -/
theorem quaternionCircuitOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W) :
    QuaternionCircuitOutputLeftPhaseEq C D ↔
      PureInputBasisMeasurementEq State.quaternionWeight C.eval D.eval := by
  change QuaternionOutputLeftPhaseEq C.eval D.eval ↔
    PureInputBasisMeasurementEq State.quaternionWeight C.eval D.eval
  exact quaternionOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq C.eval D.eval

/-- Real circuit global sign is exactly projective evaluator action. -/
theorem realCircuitGlobalSignEq_iff_projectiveActionEq
    {W : Type u} [Fintype W]
    (C D : RealUnitaryCircuit W) :
    RealCircuitGlobalSignEq C.circuit D.circuit ↔
      RealCircuitProjectiveActionEq C.circuit D.circuit :=
  (realCircuitGlobalSignEq_iff_channelEq C D).trans
    (realCircuitProjectiveActionEq_iff_channelEq C D).symm

/-- Complex circuit global phase is exactly projective evaluator action. -/
theorem complexCircuitGlobalPhaseEq_iff_projectiveActionEq
    {W : Type u} [Fintype W]
    (C D : ComplexUnitaryCircuit W) :
    ComplexCircuitGlobalPhaseEq C.circuit D.circuit ↔
      ComplexCircuitProjectiveActionEq C.circuit D.circuit :=
  (complexCircuitGlobalPhaseEq_iff_channelEq C D).trans
    (complexCircuitProjectiveActionEq_iff_channelEq C D).symm

namespace CircuitChannelEq

/-- Equal real circuit channels agree on every normalized pure-input basis statistic. -/
theorem realPureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitChannelEq C D) :
    PureInputBasisMeasurementEq State.realWeight C.circuit.eval D.circuit.eval := by
  simpa only [UnitaryCircuit.toOperator_coe] using
    ChannelEq.realPureInputBasisMeasurementEq h

/-- Equal complex circuit channels agree on every normalized pure-input basis statistic. -/
theorem complexPureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitChannelEq C D) :
    PureInputBasisMeasurementEq State.complexWeight C.circuit.eval D.circuit.eval := by
  simpa only [UnitaryCircuit.toOperator_coe] using
    ChannelEq.complexPureInputBasisMeasurementEq h

/-- Equal real circuit channels differ by one sign on each evaluator output row. -/
theorem realOutputBasisSignEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitChannelEq C D) :
    RealCircuitOutputBasisSignEq C.circuit D.circuit :=
  (realCircuitOutputBasisSignEq_iff_pureInputBasisMeasurementEq
    C.circuit D.circuit).2 h.realPureInputBasisMeasurementEq

/-- Equal complex circuit channels differ by one phase on each evaluator output row. -/
theorem complexOutputBasisPhaseEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitChannelEq C D) :
    ComplexCircuitOutputBasisPhaseEq C.circuit D.circuit :=
  (complexCircuitOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq
    C.circuit D.circuit).2 h.complexPureInputBasisMeasurementEq

/-- Equal real circuit channels agree on every basis transition weight. -/
theorem realBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitChannelEq C D) :
    BasisMeasurementEq State.realWeight C.circuit.eval D.circuit.eval :=
  h.realPureInputBasisMeasurementEq.realBasisMeasurementEq

/-- Equal complex circuit channels agree on every basis transition weight. -/
theorem complexBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitChannelEq C D) :
    BasisMeasurementEq State.complexWeight C.circuit.eval D.circuit.eval :=
  h.complexPureInputBasisMeasurementEq.complexBasisMeasurementEq

end CircuitChannelEq

namespace CircuitAllMeasurementEq

/-- All-effect equality of real circuit evaluators implies all pure basis statistics. -/
theorem realPureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitAllMeasurementEq C D) :
    PureInputBasisMeasurementEq State.realWeight C.circuit.eval D.circuit.eval :=
  h.channelEq.realPureInputBasisMeasurementEq

/-- All-effect equality of complex circuit evaluators implies all pure basis statistics. -/
theorem complexPureInputBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitAllMeasurementEq C D) :
    PureInputBasisMeasurementEq State.complexWeight C.circuit.eval D.circuit.eval :=
  h.channelEq.complexPureInputBasisMeasurementEq

/-- All-effect equality of real circuit evaluators implies basis-transition agreement. -/
theorem realBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : RealUnitaryCircuit W} (h : CircuitAllMeasurementEq C D) :
    BasisMeasurementEq State.realWeight C.circuit.eval D.circuit.eval :=
  h.channelEq.realBasisMeasurementEq

/-- All-effect equality of complex circuit evaluators implies basis-transition agreement. -/
theorem complexBasisMeasurementEq
    {W : Type u} [Fintype W]
    {C D : ComplexUnitaryCircuit W} (h : CircuitAllMeasurementEq C D) :
    BasisMeasurementEq State.complexWeight C.circuit.eval D.circuit.eval :=
  h.channelEq.complexBasisMeasurementEq

end CircuitAllMeasurementEq

end QuaternionicComputing.Semantics
