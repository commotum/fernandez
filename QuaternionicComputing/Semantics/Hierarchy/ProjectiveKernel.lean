module

public import QuaternionicComputing.Semantics.Hierarchy.ProjectiveInput

/-!
# Real and complex projective kernels for arbitrary matrices

Raw projective agreement forces a single matrix-wide scalar over the real or
complex numbers.  The proof works for arbitrary rectangular matrices with a
finite input type: it needs no unitarity, square-matrix, nonempty-index, or
output-finiteness hypothesis.

The key argument combines the input-column and output-row phase witnesses.
Columns whose supports overlap have the same phase immediately.  For disjoint
supports, projective agreement on the sum of two basis columns forces their
phases to agree.  The zero matrix (including empty input or output types) is
handled separately.

Quaternionic projective agreement deliberately has no analogous conclusion:
noncentral unit quaternions give genuine projective operators that are not
central-sign equivalent.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe u v w

private theorem globalScalarEq_of_column_row_rawRay
    {K : Type u} [Field K]
    {O : Type v} {I : Type w} [Fintype I]
    {U V : Matrix O I K} {unitScalar : K → Prop}
    (hOne : unitScalar 1)
    (s : I → K) (hs : ∀ x, unitScalar (s x))
    (hcol : ∀ y x, V y x = U y x * s x)
    (t : O → K) (hrow : ∀ y x, V y x = t y * U y x)
    (hraw : ∀ psi : I → K,
      ∃ r : K, V *ᵥ psi = fun y ↦ (U *ᵥ psi) y * r) :
    ∃ a : K, unitScalar a ∧ V = a • U := by
  classical
  by_cases hU : U = 0
  · have hV : V = 0 := by
      funext y x
      rw [hcol, hU]
      simp
    exact ⟨1, hOne, by rw [hU, hV]; simp⟩
  · have hpivot : ∃ y x, U y x ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hU
      funext y x
      exact hnone y x
    rcases hpivot with ⟨y0, x0, hy0x0⟩
    have hphase_eq_row {y : O} {x : I} (hnz : U y x ≠ 0) :
        s x = t y := by
      apply mul_left_cancel₀ hnz
      calc
        U y x * s x = V y x := (hcol y x).symm
        _ = t y * U y x := hrow y x
        _ = U y x * t y := mul_comm _ _
    have hs_common (x : I) (hx : ∃ y, U y x ≠ 0) : s x = s x0 := by
      rcases hx with ⟨y, hyx⟩
      by_cases hoverlap : ∃ z, U z x ≠ 0 ∧ U z x0 ≠ 0
      · rcases hoverlap with ⟨z, hzx, hzx0⟩
        exact (hphase_eq_row hzx).trans (hphase_eq_row hzx0).symm
      · push Not at hoverlap
        have hyx0 : U y x0 = 0 := hoverlap y hyx
        have hy0x : U y0 x = 0 := by
          by_contra hy0x
          exact hy0x0 (hoverlap y0 hy0x)
        rcases hraw (Pi.single x 1 + Pi.single x0 1) with ⟨r, hsum⟩
        rw [Matrix.mulVec_add, Matrix.mulVec_add] at hsum
        have hsum_apply (z : O) :
            V z x + V z x0 = (U z x + U z x0) * r := by
          simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
            Pi.add_apply] using congrFun hsum z
        have hsx_r : s x = r := by
          apply mul_left_cancel₀ hyx
          calc
            U y x * s x = V y x := (hcol y x).symm
            _ = V y x + V y x0 := by rw [hcol y x0, hyx0]; simp
            _ = (U y x + U y x0) * r := hsum_apply y
            _ = U y x * r := by rw [hyx0]; simp
        have hsx0_r : s x0 = r := by
          apply mul_left_cancel₀ hy0x0
          calc
            U y0 x0 * s x0 = V y0 x0 := (hcol y0 x0).symm
            _ = V y0 x + V y0 x0 := by rw [hcol y0 x, hy0x]; simp
            _ = (U y0 x + U y0 x0) * r := hsum_apply y0
            _ = U y0 x0 * r := by rw [hy0x]; simp
        exact hsx_r.trans hsx0_r.symm
    refine ⟨s x0, hs x0, ?_⟩
    funext y x
    simp only [Matrix.smul_apply, smul_eq_mul]
    by_cases hyx : U y x = 0
    · rw [hcol, hyx]
      simp
    · rw [hcol, hs_common x ⟨y, hyx⟩, mul_comm]

/-! ## Raw projective action -/

namespace RealRawProjectiveActionEq

/--
Raw real projective agreement is exactly one global sign, even for arbitrary
rectangular matrices and empty index types.
-/
theorem globalSignEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : RealRawProjectiveActionEq U V) :
    RealGlobalSignEq U V := by
  rcases h.inputBasisSignEq with ⟨s, hs, hcol⟩
  rcases h.projectiveActionEq.pureInputBasisMeasurementEq.realOutputBasisSignEq with
    ⟨t, _, hrow⟩
  apply globalScalarEq_of_column_row_rawRay (unitScalar := fun a : ℝ ↦ a * a = 1)
    (by norm_num) s hs hcol t hrow
  intro psi
  rcases Real.signEquivalent_symm (h psi) with ⟨r, _, hr⟩
  exact ⟨r, hr⟩

end RealRawProjectiveActionEq

namespace ComplexRawProjectiveActionEq

/--
Raw complex projective agreement is exactly one global unit phase, even for
arbitrary rectangular matrices and empty index types.
-/
theorem globalPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : ComplexRawProjectiveActionEq U V) :
    ComplexGlobalPhaseEq U V := by
  rcases h.inputBasisPhaseEq with ⟨eta, heta, hcol⟩
  rcases
      h.projectiveActionEq.pureInputBasisMeasurementEq.complexOutputBasisPhaseEq with
    ⟨theta, _, hrow⟩
  apply globalScalarEq_of_column_row_rawRay
    (unitScalar := fun a : ℂ ↦ Complex.normSq a = 1)
    (by simp) eta heta hcol theta hrow
  intro psi
  rcases Complex.rightPhaseEquivalent_symm (h psi) with ⟨r, _, hr⟩
  exact ⟨r, hr⟩

end ComplexRawProjectiveActionEq

/-! ## Normalized projective action -/

namespace RealProjectiveActionEq

/-- Normalized real projective agreement determines one global sign. -/
theorem globalSignEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : RealProjectiveActionEq U V) : RealGlobalSignEq U V :=
  h.rawProjectiveActionEq.globalSignEq

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

/-- Normalized complex projective agreement determines one global unit phase. -/
theorem globalPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : ComplexProjectiveActionEq U V) : ComplexGlobalPhaseEq U V :=
  h.rawProjectiveActionEq.globalPhaseEq

end ComplexProjectiveActionEq

/-! ## Evaluator-backed circuit consequences -/

namespace RealCircuitProjectiveActionEq

/-- Projectively equal real circuit evaluators differ by one global sign. -/
theorem globalSignEq
    {W : Type u} [Fintype W]
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitProjectiveActionEq C D) :
    RealCircuitGlobalSignEq C D :=
  h.eval.globalSignEq

end RealCircuitProjectiveActionEq

namespace ComplexCircuitProjectiveActionEq

/-- Projectively equal complex circuit evaluators differ by one global phase. -/
theorem globalPhaseEq
    {W : Type u} [Fintype W]
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexCircuitGlobalPhaseEq C D :=
  h.eval.globalPhaseEq

end ComplexCircuitProjectiveActionEq

end QuaternionicComputing.Semantics
