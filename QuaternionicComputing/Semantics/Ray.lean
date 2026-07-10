module

public import QuaternionicComputing.State.Ray
public import QuaternionicComputing.Semantics.StatePhase

/-!
# Semantic equality of normalized rays

This leaf identifies the representative-level real, complex, and
quaternionic normalized state-phase relations with literal equality of their
corresponding ray constructors.  Quaternionic phase remains strictly on the
right through the underlying `QuaternionRay` quotient.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Semantics

universe u

namespace RealStatePhaseEq

/--
Real normalized states are sign-equivalent exactly when they define the same real ray.
-/
@[simp]
theorem iff_realRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.RealState I} :
    RealStatePhaseEq a b ↔ State.RealRay.mk a = State.RealRay.mk b :=
  State.RealRay.mk_eq_mk_iff.symm

end RealStatePhaseEq

namespace ComplexStatePhaseEq

/--
Complex normalized states are right-phase-equivalent exactly when they define the same complex ray.
-/
@[simp]
theorem iff_complexRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.ComplexState I} :
    ComplexStatePhaseEq a b ↔ State.ComplexRay.mk a = State.ComplexRay.mk b :=
  State.ComplexRay.mk_eq_mk_iff.symm

end ComplexStatePhaseEq

namespace QuaternionStatePhaseEq

/--
Quaternionic normalized states are right-phase-equivalent exactly when they define the same
quaternionic ray.
-/
@[simp]
theorem iff_quaternionRay_mk_eq {I : Type u} [Fintype I]
    {a b : State.QuaternionState I} :
    QuaternionStatePhaseEq a b ↔
      State.QuaternionRay.mk a = State.QuaternionRay.mk b :=
  State.QuaternionRay.mk_eq_mk_iff.symm

end QuaternionStatePhaseEq

end QuaternionicComputing.Semantics
