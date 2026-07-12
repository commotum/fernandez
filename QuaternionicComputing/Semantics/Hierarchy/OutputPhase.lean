module

public import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal
public import QuaternionicComputing.Semantics.OperatorPhase.Quaternion

/-!
# Output-row phase from all-pure-input basis measurements

This leaf proves the exact ambiguity left by computational-basis measurements
after every normalized pure input.  For arbitrary rectangular matrices with a
finite input type, that ambiguity is precisely one unit phase per output row:
a real sign, a complex phase, or a quaternionic phase multiplying on the left.

The proof first extends normalized-input measurement agreement to every raw
input by explicit normalization.  It then compares the kernels of each pair
of output-row functionals.  A zero row is handled separately.  Otherwise, a
nonzero pivot `x₀` gives the phase `V y x₀ * (U y x₀)⁻¹`, and a
two-coordinate kernel vector forces the same phase at every entry of the row.
This argument is valid without unitarity, a nonempty index hypothesis, or a
nonzero-row premise.

Empty input and output types are included.  With empty input, both matrices
have entryless rows and the output-phase relation holds even though the
normalized-input quantification is empty.  With empty output, both relations
are vacuous in the output coordinate.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Scalar-specialized basis-input consequences -/

namespace PureInputBasisMeasurementEq

/-- All-pure-input real basis statistics include all computational-basis inputs. -/
theorem realBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : PureInputBasisMeasurementEq State.realWeight U V) :
    BasisMeasurementEq State.realWeight U V := by
  classical
  apply h.basisMeasurementEq
  intro x
  simp [State.totalWeight, State.basisWeight, State.realWeight,
    Pi.single_apply]

/-- All-pure-input complex basis statistics include all computational-basis inputs. -/
theorem complexBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : PureInputBasisMeasurementEq State.complexWeight U V) :
    BasisMeasurementEq State.complexWeight U V := by
  classical
  apply h.basisMeasurementEq
  intro x
  simp [State.totalWeight, State.basisWeight, State.complexWeight,
    Pi.single_apply]

/-- All-pure-input quaternionic basis statistics include all computational-basis inputs. -/
theorem quaternionBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]}
    (h : PureInputBasisMeasurementEq State.quaternionWeight U V) :
    BasisMeasurementEq State.quaternionWeight U V := by
  classical
  apply h.basisMeasurementEq
  intro x
  simp [State.totalWeight, State.basisWeight, State.quaternionWeight,
    Pi.single_apply]

end PureInputBasisMeasurementEq

/-! ## Extending normalized-input agreement to raw inputs -/

private theorem realTotalWeight_eq_zero_iff
    {I : Type v} [Fintype I] (psi : I → ℝ) :
    State.realTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, psi i * psi i) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ mul_self_nonneg (psi i))).trans (by
      simp [funext_iff])

private theorem realRawOutputWeightEqAt
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : PureInputBasisMeasurementEq State.realWeight U V) :
    ∀ psi : I → ℝ, OutputWeightEqAt State.realWeight U V psi := by
  intro psi y
  by_cases hpsi : psi = 0
  · subst psi
    simp
  · let t : ℝ := State.realTotalWeight psi
    have ht0 : t ≠ 0 := by
      intro ht
      apply hpsi
      exact (realTotalWeight_eq_zero_iff psi).mp ht
    have ht_nonneg : 0 ≤ t := State.realTotalWeight_nonneg psi
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
    let r : ℝ := (Real.sqrt t)⁻¹
    have hsqrt0 : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht_pos
    have hr0 : r ≠ 0 := inv_ne_zero hsqrt0
    have hscaled : State.realTotalWeight (fun i ↦ psi i * r) = 1 := by
      rw [State.realTotalWeight_right_mul]
      change t * (r * r) = 1
      rw [show r = (Real.sqrt t)⁻¹ from rfl]
      field_simp
      nlinarith [Real.sq_sqrt ht_nonneg]
    let phi : State.RealState I := ⟨fun i ↦ psi i * r, hscaled⟩
    have hp := h phi y
    change State.realWeight ((U *ᵥ (fun i ↦ psi i * r)) y) =
      State.realWeight ((V *ᵥ (fun i ↦ psi i * r)) y) at hp
    rw [State.real_mulVec_right_mul, State.real_mulVec_right_mul] at hp
    change ((U *ᵥ psi) y * r) * ((U *ᵥ psi) y * r) =
      ((V *ᵥ psi) y * r) * ((V *ᵥ psi) y * r) at hp
    have hr2 : r * r ≠ 0 := mul_ne_zero hr0 hr0
    change ((U *ᵥ psi) y) * ((U *ᵥ psi) y) =
      ((V *ᵥ psi) y) * ((V *ᵥ psi) y)
    apply mul_right_cancel₀ hr2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hp

private theorem complexTotalWeight_eq_zero_iff
    {I : Type v} [Fintype I] (psi : I → ℂ) :
    State.complexTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, Complex.normSq (psi i)) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ Complex.normSq_nonneg (psi i))).trans (by
      simp [funext_iff])

private theorem complexRawOutputWeightEqAt
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : PureInputBasisMeasurementEq State.complexWeight U V) :
    ∀ psi : I → ℂ, OutputWeightEqAt State.complexWeight U V psi := by
  intro psi y
  by_cases hpsi : psi = 0
  · subst psi
    simp
  · let t : ℝ := State.complexTotalWeight psi
    have ht0 : t ≠ 0 := by
      intro ht
      apply hpsi
      exact (complexTotalWeight_eq_zero_iff psi).mp ht
    have ht_nonneg : 0 ≤ t := State.complexTotalWeight_nonneg psi
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
    let r : ℝ := (Real.sqrt t)⁻¹
    have hsqrt0 : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht_pos
    have hr0 : r ≠ 0 := inv_ne_zero hsqrt0
    have hscaled :
        State.complexTotalWeight (fun i ↦ psi i * (r : ℂ)) = 1 := by
      rw [State.complexTotalWeight_right_mul, Complex.normSq_ofReal]
      change t * (r * r) = 1
      rw [show r = (Real.sqrt t)⁻¹ from rfl]
      field_simp
      nlinarith [Real.sq_sqrt ht_nonneg]
    let phi : State.ComplexState I :=
      ⟨fun i ↦ psi i * (r : ℂ), hscaled⟩
    have hp := h phi y
    change State.complexWeight
      ((U *ᵥ (fun i ↦ psi i * (r : ℂ))) y) =
      State.complexWeight
        ((V *ᵥ (fun i ↦ psi i * (r : ℂ))) y) at hp
    rw [State.complex_mulVec_right_mul,
      State.complex_mulVec_right_mul] at hp
    change Complex.normSq ((U *ᵥ psi) y * (r : ℂ)) =
      Complex.normSq ((V *ᵥ psi) y * (r : ℂ)) at hp
    simp only [Complex.normSq_mul, Complex.normSq_ofReal] at hp
    have hr2 : r * r ≠ 0 := mul_ne_zero hr0 hr0
    change Complex.normSq ((U *ᵥ psi) y) =
      Complex.normSq ((V *ᵥ psi) y)
    exact mul_right_cancel₀ hr2 hp

private theorem quaternionTotalWeight_eq_zero_iff
    {I : Type v} [Fintype I] (psi : I → ℍ[ℝ]) :
    State.quaternionTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, _root_.Quaternion.normSq (psi i)) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ _root_.Quaternion.normSq_nonneg)).trans (by
      simp [funext_iff])

private theorem quaternionRawOutputWeightEqAt
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]}
    (h : PureInputBasisMeasurementEq State.quaternionWeight U V) :
    ∀ psi : I → ℍ[ℝ], OutputWeightEqAt State.quaternionWeight U V psi := by
  intro psi y
  by_cases hpsi : psi = 0
  · subst psi
    simp
  · let t : ℝ := State.quaternionTotalWeight psi
    have ht0 : t ≠ 0 := by
      intro ht
      apply hpsi
      exact (quaternionTotalWeight_eq_zero_iff psi).mp ht
    have ht_nonneg : 0 ≤ t := State.quaternionTotalWeight_nonneg psi
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
    let r : ℝ := (Real.sqrt t)⁻¹
    have hsqrt0 : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht_pos
    have hr0 : r ≠ 0 := inv_ne_zero hsqrt0
    have hscaled :
        State.quaternionTotalWeight (psi <• (r : ℍ[ℝ])) = 1 := by
      rw [State.quaternionTotalWeight_right_smul,
        _root_.Quaternion.normSq_coe]
      change t * r ^ 2 = 1
      rw [show r = (Real.sqrt t)⁻¹ from rfl, inv_pow]
      field_simp
      nlinarith [Real.sq_sqrt ht_nonneg]
    let phi : State.QuaternionState I :=
      ⟨psi <• (r : ℍ[ℝ]), hscaled⟩
    have hp := h phi y
    change State.quaternionWeight
      ((U *ᵥ (psi <• (r : ℍ[ℝ]))) y) =
      State.quaternionWeight
        ((V *ᵥ (psi <• (r : ℍ[ℝ]))) y) at hp
    rw [State.quaternion_mulVec_right_smul,
      State.quaternion_mulVec_right_smul] at hp
    change _root_.Quaternion.normSq ((U *ᵥ psi) y * (r : ℍ[ℝ])) =
      _root_.Quaternion.normSq ((V *ᵥ psi) y * (r : ℍ[ℝ])) at hp
    simp only [map_mul, _root_.Quaternion.normSq_coe] at hp
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    exact mul_right_cancel₀ hr2 hp

/-! ## Row-functional separation -/

namespace PureInputBasisMeasurementEq

/--
All normalized pure-input real basis statistics force one unit sign per output
row.  The matrices may be rectangular; only the input type is finite.
-/
theorem realOutputBasisSignEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ}
    (h : PureInputBasisMeasurementEq State.realWeight U V) :
    RealOutputBasisSignEq U V := by
  classical
  have hraw := realRawOutputWeightEqAt h
  have hrow (y : O) :
      ∃ s : ℝ, s * s = 1 ∧ ∀ x, V y x = s * U y x := by
    by_cases hzero : ∀ x, U y x = 0
    · refine ⟨1, by norm_num, ?_⟩
      intro x
      have hw : U y x * U y x = V y x * V y x := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight,
          State.realWeight] using hraw (Pi.single x (1 : ℝ)) y
      rw [hzero x] at hw
      have hv0 : V y x = 0 := mul_self_eq_zero.mp (by simpa using hw.symm)
      simpa [hv0] using (hzero x).symm
    · simp only [not_forall] at hzero
      rcases hzero with ⟨x0, hx0⟩
      let s : ℝ := V y x0 * (U y x0)⁻¹
      have hw0 : U y x0 * U y x0 = V y x0 * V y x0 := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight,
          State.realWeight] using hraw (Pi.single x0 (1 : ℝ)) y
      have hs : s * s = 1 := by
        dsimp only [s]
        field_simp [hx0]
        nlinarith [hw0]
      refine ⟨s, hs, ?_⟩
      intro x
      by_cases hxx0 : x = x0
      · subst x
        simp [s, hx0]
      · let c : ℝ := -((U y x0)⁻¹ * U y x)
        let psi : I → ℝ := Pi.single x 1 + Pi.single x0 c
        have hUpsi : (U *ᵥ psi) y = 0 := by
          simp [psi, c, Matrix.mulVec_add, hx0]
        have hw := hraw psi y
        change ((U *ᵥ psi) y) * ((U *ᵥ psi) y) =
          ((V *ᵥ psi) y) * ((V *ᵥ psi) y) at hw
        rw [hUpsi] at hw
        have hVpsi : (V *ᵥ psi) y = 0 :=
          mul_self_eq_zero.mp (by simpa using hw.symm)
        simp [psi, c, Matrix.mulVec_add] at hVpsi
        change V y x = s * U y x
        simp only [s, mul_assoc]
        rw [← sub_eq_zero]
        simpa [sub_eq_add_neg, mul_neg, mul_assoc] using hVpsi
  choose s hs hentry using hrow
  exact ⟨s, hs, hentry⟩

/--
All normalized pure-input complex basis statistics force one unit phase per
output row.  The matrices may be rectangular; only the input type is finite.
-/
theorem complexOutputBasisPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ}
    (h : PureInputBasisMeasurementEq State.complexWeight U V) :
    ComplexOutputBasisPhaseEq U V := by
  classical
  have hraw := complexRawOutputWeightEqAt h
  have hrow (y : O) :
      ∃ eta : ℂ, Complex.normSq eta = 1 ∧
        ∀ x, V y x = eta * U y x := by
    by_cases hzero : ∀ x, U y x = 0
    · refine ⟨1, by simp, ?_⟩
      intro x
      have hw : Complex.normSq (U y x) = Complex.normSq (V y x) := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight] using
          hraw (Pi.single x (1 : ℂ)) y
      rw [hzero x] at hw
      have hv0 : V y x = 0 := Complex.normSq_eq_zero.mp (by
        simpa using hw.symm)
      simpa [hv0] using (hzero x).symm
    · simp only [not_forall] at hzero
      rcases hzero with ⟨x0, hx0⟩
      let eta : ℂ := V y x0 * (U y x0)⁻¹
      have hw0 : Complex.normSq (U y x0) =
          Complex.normSq (V y x0) := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight] using
          hraw (Pi.single x0 (1 : ℂ)) y
      have hnorm0 : Complex.normSq (U y x0) ≠ 0 :=
        mt Complex.normSq_eq_zero.mp hx0
      have heta : Complex.normSq eta = 1 := by
        simp only [eta, Complex.normSq_mul, Complex.normSq_inv]
        rw [← hw0]
        exact mul_inv_cancel₀ hnorm0
      refine ⟨eta, heta, ?_⟩
      intro x
      by_cases hxx0 : x = x0
      · subst x
        simp [eta, hx0]
      · let c : ℂ := -((U y x0)⁻¹ * U y x)
        let psi : I → ℂ := Pi.single x 1 + Pi.single x0 c
        have hUpsi : (U *ᵥ psi) y = 0 := by
          simp [psi, c, Matrix.mulVec_add, hx0]
        have hw := hraw psi y
        change Complex.normSq ((U *ᵥ psi) y) =
          Complex.normSq ((V *ᵥ psi) y) at hw
        rw [hUpsi] at hw
        have hVpsi : (V *ᵥ psi) y = 0 :=
          Complex.normSq_eq_zero.mp (by simpa using hw.symm)
        simp [psi, c, Matrix.mulVec_add] at hVpsi
        change V y x = eta * U y x
        simp only [eta, mul_assoc]
        rw [← sub_eq_zero]
        simpa [sub_eq_add_neg, mul_neg, mul_assoc] using hVpsi
  choose eta heta hentry using hrow
  exact ⟨eta, heta, hentry⟩

/--
All normalized pure-input quaternionic basis statistics force one unit left
phase per output row.  The multiplication order is
`V y x = theta y * U y x`; no commutativity is used.
-/
theorem quaternionOutputLeftPhaseEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]}
    (h : PureInputBasisMeasurementEq State.quaternionWeight U V) :
    QuaternionOutputLeftPhaseEq U V := by
  classical
  have hraw := quaternionRawOutputWeightEqAt h
  have hrow (y : O) :
      ∃ theta : ℍ[ℝ], _root_.Quaternion.normSq theta = 1 ∧
        ∀ x, V y x = theta * U y x := by
    by_cases hzero : ∀ x, U y x = 0
    · refine ⟨1, by simp, ?_⟩
      intro x
      have hw : _root_.Quaternion.normSq (U y x) =
          _root_.Quaternion.normSq (V y x) := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight] using
          hraw (Pi.single x (1 : ℍ[ℝ])) y
      rw [hzero x] at hw
      have hv0 : V y x = 0 := _root_.Quaternion.normSq_eq_zero.mp (by
        simpa using hw.symm)
      simpa [hv0] using (hzero x).symm
    · simp only [not_forall] at hzero
      rcases hzero with ⟨x0, hx0⟩
      let theta : ℍ[ℝ] := V y x0 * (U y x0)⁻¹
      have hw0 : _root_.Quaternion.normSq (U y x0) =
          _root_.Quaternion.normSq (V y x0) := by
        simpa [OutputWeightEqAt, BasisWeightEq, State.basisWeight] using
          hraw (Pi.single x0 (1 : ℍ[ℝ])) y
      have hnorm0 : _root_.Quaternion.normSq (U y x0) ≠ 0 :=
        _root_.Quaternion.normSq_ne_zero.mpr hx0
      have htheta : _root_.Quaternion.normSq theta = 1 := by
        simp only [theta, map_mul, _root_.Quaternion.normSq_inv]
        rw [← hw0]
        exact mul_inv_cancel₀ hnorm0
      refine ⟨theta, htheta, ?_⟩
      intro x
      by_cases hxx0 : x = x0
      · subst x
        simp only [theta, mul_assoc]
        rw [inv_mul_cancel₀ hx0, mul_one]
      · let c : ℍ[ℝ] := -((U y x0)⁻¹ * U y x)
        let psi : I → ℍ[ℝ] := Pi.single x 1 + Pi.single x0 c
        have hUpsi : (U *ᵥ psi) y = 0 := by
          simp [psi, c, Matrix.mulVec_add, hx0]
        have hw := hraw psi y
        change _root_.Quaternion.normSq ((U *ᵥ psi) y) =
          _root_.Quaternion.normSq ((V *ᵥ psi) y) at hw
        rw [hUpsi] at hw
        have hVpsi : (V *ᵥ psi) y = 0 :=
          _root_.Quaternion.normSq_eq_zero.mp (by simpa using hw.symm)
        simp [psi, c, Matrix.mulVec_add] at hVpsi
        change V y x = theta * U y x
        simp only [theta, mul_assoc]
        rw [← sub_eq_zero]
        simpa [sub_eq_add_neg, mul_neg, mul_assoc] using hVpsi
  choose theta htheta hentry using hrow
  exact ⟨theta, htheta, hentry⟩

end PureInputBasisMeasurementEq

/-! ## Exact characterizations -/

/--
For arbitrary rectangular real matrices with finite input, output-row sign
equality is exactly all-pure-input computational-basis measurement agreement.
-/
theorem realOutputBasisSignEq_iff_pureInputBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℝ) :
    RealOutputBasisSignEq U V ↔
      PureInputBasisMeasurementEq State.realWeight U V :=
  ⟨RealOutputBasisSignEq.pureInputBasisMeasurementEq,
    PureInputBasisMeasurementEq.realOutputBasisSignEq⟩

/--
For arbitrary rectangular complex matrices with finite input, output-row phase
equality is exactly all-pure-input computational-basis measurement agreement.
-/
theorem complexOutputBasisPhaseEq_iff_pureInputBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℂ) :
    ComplexOutputBasisPhaseEq U V ↔
      PureInputBasisMeasurementEq State.complexWeight U V :=
  ⟨ComplexOutputBasisPhaseEq.pureInputBasisMeasurementEq,
    PureInputBasisMeasurementEq.complexOutputBasisPhaseEq⟩

/--
For arbitrary rectangular quaternionic matrices with finite input, output-row
left phase is exactly all-pure-input computational-basis measurement agreement.
-/
theorem quaternionOutputLeftPhaseEq_iff_pureInputBasisMeasurementEq
    {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℍ[ℝ]) :
    QuaternionOutputLeftPhaseEq U V ↔
      PureInputBasisMeasurementEq State.quaternionWeight U V :=
  ⟨QuaternionOutputLeftPhaseEq.pureInputBasisMeasurementEq,
    PureInputBasisMeasurementEq.quaternionOutputLeftPhaseEq⟩

end QuaternionicComputing.Semantics
