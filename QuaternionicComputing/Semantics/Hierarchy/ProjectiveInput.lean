module

public import QuaternionicComputing.Semantics.Hierarchy.Operator

/-!
# Projective action determines input-column phase

Projective operator agreement quantifies every normalized pure input, so in
particular it sees every computational-basis input.  Specializing to those
inputs proves the missing covering arrows from raw or normalized projective
action to the corresponding input-column phase relation.

These implications hold for arbitrary rectangular matrices with a finite
input type.  No unitarity, nonempty-index, channel, or cross-model hypothesis
is used.  The circuit declarations are evaluator-backed consequences and say
nothing about gate lists, schedules, or resources.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Raw projective action -/

namespace RealRawProjectiveActionEq

/-- Raw real projective action determines one sign for each input column. -/
theorem inputBasisSignEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : RealRawProjectiveActionEq U V) :
    RealInputBasisSignEq U V := by
  classical
  choose s hs hcolumn using fun x ↦
    Real.signEquivalent_symm (h (Pi.single x (1 : ℝ)))
  refine ⟨s, hs, ?_⟩
  intro y x
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
    congrFun (hcolumn x) y

end RealRawProjectiveActionEq

namespace ComplexRawProjectiveActionEq

/-- Raw complex projective action determines one right phase per input column. -/
theorem inputBasisPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : ComplexRawProjectiveActionEq U V) :
    ComplexInputBasisPhaseEq U V := by
  classical
  choose eta heta hcolumn using fun x ↦
    Complex.rightPhaseEquivalent_symm (h (Pi.single x (1 : ℂ)))
  refine ⟨eta, heta, ?_⟩
  intro y x
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
    congrFun (hcolumn x) y

end ComplexRawProjectiveActionEq

namespace QuaternionRawProjectiveActionEq

/--
Raw quaternionic projective action determines one unit right phase per input
column.  The multiplication side is inherited from `RightPhaseEquivalent`.
-/
theorem inputRightPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]}
    (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionInputRightPhaseEq U V := by
  classical
  choose phi hphi hcolumn using fun x ↦
    Quaternion.rightPhaseEquivalent_symm
      (h (Pi.single x (1 : ℍ[ℝ])))
  refine ⟨phi, hphi, ?_⟩
  intro y x
  simpa [Matrix.col_apply] using congrFun (hcolumn x) y

end QuaternionRawProjectiveActionEq

/-! ## Normalized projective action -/

namespace RealProjectiveActionEq

/-- Normalized real projective action determines every input-column sign. -/
theorem inputBasisSignEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : RealProjectiveActionEq U V) :
    RealInputBasisSignEq U V :=
  h.rawProjectiveActionEq.inputBasisSignEq

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

/-- Normalized complex projective action determines every input-column phase. -/
theorem inputBasisPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : ComplexProjectiveActionEq U V) :
    ComplexInputBasisPhaseEq U V :=
  h.rawProjectiveActionEq.inputBasisPhaseEq

end ComplexProjectiveActionEq

namespace QuaternionProjectiveActionEq

/--
Normalized quaternionic projective action determines every input-column
phase, with the phase multiplying strictly on the right.
-/
theorem inputRightPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]}
    (h : QuaternionProjectiveActionEq U V) :
    QuaternionInputRightPhaseEq U V :=
  h.rawProjectiveActionEq.inputRightPhaseEq

end QuaternionProjectiveActionEq

/-! ## Evaluator-backed circuit consequences -/

namespace RealCircuitProjectiveActionEq

/-- Projectively equal real circuit evaluators have input-column signs. -/
theorem inputBasisSignEq
    {W : Type u} [Fintype W]
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitProjectiveActionEq C D) :
    RealCircuitInputBasisSignEq C D :=
  h.eval.inputBasisSignEq

end RealCircuitProjectiveActionEq

namespace ComplexCircuitProjectiveActionEq

/-- Projectively equal complex circuit evaluators have input-column phases. -/
theorem inputBasisPhaseEq
    {W : Type u} [Fintype W]
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexCircuitInputBasisPhaseEq C D :=
  h.eval.inputBasisPhaseEq

end ComplexCircuitProjectiveActionEq

namespace QuaternionCircuitProjectiveActionEq

/--
Projectively equal quaternionic circuit evaluators have input-column phases
on the right.
-/
theorem inputRightPhaseEq
    {W : Type u} [Fintype W]
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitProjectiveActionEq C D) :
    QuaternionCircuitInputRightPhaseEq C D :=
  h.eval.inputRightPhaseEq

end QuaternionCircuitProjectiveActionEq

end QuaternionicComputing.Semantics
