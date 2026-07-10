module

public import QuaternionicComputing.Semantics.StatePhase

/-!
# Quaternionic operator phase semantics

This low-dependency leaf separates five same-space comparisons for
quaternionic matrices: one central real sign, an input-column family acting on
the right, an output-row family acting on the left, projective action on every
raw column, and projective action on every normalized pure input.

The raw and normalized projective-action relations are equivalent for every
finite input type.  The nonzero-column direction normalizes by a positive real
central scalar and treats the zero column separately.  No unitarity or
nonemptiness premise is needed for that bridge.

This file contains no circuit wrappers, dimension-sensitive projective-kernel
characterization, rank-one exception, channel semantics, or diagnostics.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Operator relations -/

/--
Quaternionic matrices agree up to one central real unit sign, oriented as
`V = s • U`.  This deliberately excludes arbitrary unit quaternions.
-/
def QuaternionCentralSignEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℍ[ℝ]) : Prop :=
  ∃ s : ℝ, s * s = 1 ∧ V = s • U

/--
Each input column of `V` is the corresponding column of `U` times a unit
quaternion on the right.
-/
def QuaternionInputRightPhaseEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℍ[ℝ]) : Prop :=
  ∃ phi : I → ℍ[ℝ],
    (∀ x, _root_.Quaternion.normSq (phi x) = 1) ∧
      ∀ y x, V y x = U y x * phi x

/-- Each output row of `V` is a unit quaternion times the corresponding row of `U` on the left. -/
def QuaternionOutputLeftPhaseEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℍ[ℝ]) : Prop :=
  ∃ theta : O → ℍ[ℝ],
    (∀ y, _root_.Quaternion.normSq (theta y) = 1) ∧
      ∀ y x, V y x = theta y * U y x

/-- Quaternionic matrices have the same right ray action on every raw input column. -/
def QuaternionRawProjectiveActionEq {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℍ[ℝ]) : Prop :=
  ∀ psi : I → ℍ[ℝ],
    Quaternion.RightPhaseEquivalent (U *ᵥ psi) (V *ᵥ psi)

/-- Quaternionic matrices have the same right ray action on every normalized pure input. -/
def QuaternionProjectiveActionEq {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℍ[ℝ]) : Prop :=
  ∀ psi : State.QuaternionState I,
    Quaternion.RightPhaseEquivalent
      (U *ᵥ (psi : I → ℍ[ℝ])) (V *ᵥ (psi : I → ℍ[ℝ]))

/-! ## Equivalence laws -/

namespace QuaternionCentralSignEq

variable {O : Type u} {I : Type v}
variable {U V T : Matrix O I ℍ[ℝ]}

@[refl]
theorem refl (U : Matrix O I ℍ[ℝ]) : QuaternionCentralSignEq U U :=
  ⟨1, by norm_num, by simp⟩

@[symm]
theorem symm (h : QuaternionCentralSignEq U V) :
    QuaternionCentralSignEq V U := by
  rcases h with ⟨s, hs, rfl⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_smul, hs, one_smul]

@[trans]
theorem trans (hUV : QuaternionCentralSignEq U V)
    (hVT : QuaternionCentralSignEq V T) : QuaternionCentralSignEq U T := by
  rcases hUV with ⟨s, hs, hV⟩
  rcases hVT with ⟨t, ht, hT⟩
  refine ⟨t * s, ?_, ?_⟩
  · calc
      (t * s) * (t * s) = (t * t) * (s * s) := by ring
      _ = 1 := by rw [ht, hs, one_mul]
  · rw [hT, hV, smul_smul]

/-- Quaternionic central-sign equality is an equivalence relation. -/
theorem equivalence : Equivalence (@QuaternionCentralSignEq O I) :=
  ⟨refl, symm, trans⟩

end QuaternionCentralSignEq

namespace QuaternionInputRightPhaseEq

variable {O : Type u} {I : Type v}
variable {U V T : Matrix O I ℍ[ℝ]}

@[refl]
theorem refl (U : Matrix O I ℍ[ℝ]) : QuaternionInputRightPhaseEq U U := by
  refine ⟨fun _ ↦ 1, fun _ ↦ by simp, ?_⟩
  simp

@[symm]
theorem symm (h : QuaternionInputRightPhaseEq U V) :
    QuaternionInputRightPhaseEq V U := by
  rcases h with ⟨phi, hphi, hV⟩
  refine ⟨fun x ↦ star (phi x), fun x ↦ by simpa using hphi x, ?_⟩
  intro y x
  change U y x = V y x * star (phi x)
  calc
    U y x = U y x * 1 := by rw [mul_one]
    _ = U y x * (phi x * star (phi x)) := by
      rw [_root_.Quaternion.self_mul_star, hphi]
      simp
    _ = (U y x * phi x) * star (phi x) := by rw [mul_assoc]
    _ = V y x * star (phi x) := by rw [hV]

@[trans]
theorem trans (hUV : QuaternionInputRightPhaseEq U V)
    (hVT : QuaternionInputRightPhaseEq V T) :
    QuaternionInputRightPhaseEq U T := by
  rcases hUV with ⟨phi, hphi, hV⟩
  rcases hVT with ⟨theta, htheta, hT⟩
  refine ⟨fun x ↦ phi x * theta x, ?_, ?_⟩
  · intro x
    rw [map_mul, hphi, htheta, one_mul]
  · intro y x
    rw [hT, hV, mul_assoc]

/-- Quaternionic input-right-phase equality is an equivalence relation. -/
theorem equivalence : Equivalence (@QuaternionInputRightPhaseEq O I) :=
  ⟨refl, symm, trans⟩

end QuaternionInputRightPhaseEq

namespace QuaternionOutputLeftPhaseEq

variable {O : Type u} {I : Type v}
variable {U V T : Matrix O I ℍ[ℝ]}

@[refl]
theorem refl (U : Matrix O I ℍ[ℝ]) : QuaternionOutputLeftPhaseEq U U := by
  refine ⟨fun _ ↦ 1, fun _ ↦ by simp, ?_⟩
  simp

@[symm]
theorem symm (h : QuaternionOutputLeftPhaseEq U V) :
    QuaternionOutputLeftPhaseEq V U := by
  rcases h with ⟨theta, htheta, hV⟩
  refine ⟨fun y ↦ star (theta y), fun y ↦ by simpa using htheta y, ?_⟩
  intro y x
  change U y x = star (theta y) * V y x
  calc
    U y x = 1 * U y x := by rw [one_mul]
    _ = (star (theta y) * theta y) * U y x := by
      rw [_root_.Quaternion.star_mul_self, htheta]
      simp
    _ = star (theta y) * (theta y * U y x) := by rw [mul_assoc]
    _ = star (theta y) * V y x := by rw [hV]

@[trans]
theorem trans (hUV : QuaternionOutputLeftPhaseEq U V)
    (hVT : QuaternionOutputLeftPhaseEq V T) :
    QuaternionOutputLeftPhaseEq U T := by
  rcases hUV with ⟨theta, htheta, hV⟩
  rcases hVT with ⟨kappa, hkappa, hT⟩
  refine ⟨fun y ↦ kappa y * theta y, ?_, ?_⟩
  · intro y
    rw [map_mul, hkappa, htheta, one_mul]
  · intro y x
    rw [hT, hV, mul_assoc]

/-- Quaternionic output-left-phase equality is an equivalence relation. -/
theorem equivalence : Equivalence (@QuaternionOutputLeftPhaseEq O I) :=
  ⟨refl, symm, trans⟩

end QuaternionOutputLeftPhaseEq

namespace QuaternionRawProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V T : Matrix O I ℍ[ℝ]}

@[refl]
theorem refl (U : Matrix O I ℍ[ℝ]) : QuaternionRawProjectiveActionEq U U :=
  fun _ ↦ Quaternion.rightPhaseEquivalent_refl _

@[symm]
theorem symm (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionRawProjectiveActionEq V U :=
  fun psi ↦ Quaternion.rightPhaseEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : QuaternionRawProjectiveActionEq U V)
    (hVT : QuaternionRawProjectiveActionEq V T) :
    QuaternionRawProjectiveActionEq U T :=
  fun psi ↦ Quaternion.rightPhaseEquivalent_trans (hUV psi) (hVT psi)

/-- Quaternionic raw projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@QuaternionRawProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

end QuaternionRawProjectiveActionEq

namespace QuaternionProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V T : Matrix O I ℍ[ℝ]}

@[refl]
theorem refl (U : Matrix O I ℍ[ℝ]) : QuaternionProjectiveActionEq U U :=
  fun _ ↦ Quaternion.rightPhaseEquivalent_refl _

@[symm]
theorem symm (h : QuaternionProjectiveActionEq U V) :
    QuaternionProjectiveActionEq V U :=
  fun psi ↦ Quaternion.rightPhaseEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : QuaternionProjectiveActionEq U V)
    (hVT : QuaternionProjectiveActionEq V T) :
    QuaternionProjectiveActionEq U T :=
  fun psi ↦ Quaternion.rightPhaseEquivalent_trans (hUV psi) (hVT psi)

/-- Quaternionic normalized projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@QuaternionProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

end QuaternionProjectiveActionEq

/-! ## Exact lifts -/

namespace QuaternionCentralSignEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- Exact quaternionic operator equality implies central-sign equality. -/
theorem of_exact (h : ExactOperatorEq U V) : QuaternionCentralSignEq U V := by
  subst V
  exact refl U

end QuaternionCentralSignEq

namespace QuaternionInputRightPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- Exact quaternionic operator equality implies input-right-phase equality. -/
theorem of_exact (h : ExactOperatorEq U V) : QuaternionInputRightPhaseEq U V := by
  subst V
  exact refl U

end QuaternionInputRightPhaseEq

namespace QuaternionOutputLeftPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- Exact quaternionic operator equality implies output-left-phase equality. -/
theorem of_exact (h : ExactOperatorEq U V) : QuaternionOutputLeftPhaseEq U V := by
  subst V
  exact refl U

end QuaternionOutputLeftPhaseEq

namespace QuaternionRawProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℍ[ℝ]}

/-- Exact quaternionic operator equality implies raw projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) :
    QuaternionRawProjectiveActionEq U V := by
  subst V
  exact refl U

end QuaternionRawProjectiveActionEq

namespace QuaternionProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℍ[ℝ]}

/-- Exact quaternionic operator equality implies normalized projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) : QuaternionProjectiveActionEq U V := by
  subst V
  exact refl U

end QuaternionProjectiveActionEq

/-! ## Raw and normalized projective action -/

private theorem quaternionTotalWeight_eq_zero_iff
    {I : Type u} [Fintype I] (psi : I → ℍ[ℝ]) :
    State.quaternionTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, _root_.Quaternion.normSq (psi i)) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ _root_.Quaternion.normSq_nonneg)).trans (by
      simp [funext_iff])

namespace QuaternionRawProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℍ[ℝ]}

/-- Raw projective-action equality restricts to every normalized pure input. -/
theorem projectiveActionEq (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionProjectiveActionEq U V :=
  fun psi ↦ h psi

end QuaternionRawProjectiveActionEq

namespace QuaternionProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℍ[ℝ]}

/-!
Every nonzero raw column can be normalized by a nonzero central real scalar.
Cancelling that scalar transports the phase witness back to the raw column;
the zero column is handled separately.
-/
theorem rawProjectiveActionEq (h : QuaternionProjectiveActionEq U V) :
    QuaternionRawProjectiveActionEq U V := by
  intro psi
  by_cases hpsi : psi = 0
  · subst psi
    simpa only [Matrix.mulVec_zero] using
      Quaternion.rightPhaseEquivalent_refl (0 : O → ℍ[ℝ])
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
    have hscaled : State.quaternionTotalWeight (psi <• (r : ℍ[ℝ])) = 1 := by
      rw [State.quaternionTotalWeight_right_smul,
        _root_.Quaternion.normSq_coe]
      change t * r ^ 2 = 1
      rw [show r = (Real.sqrt t)⁻¹ from rfl, inv_pow]
      field_simp
      nlinarith [Real.sq_sqrt ht_nonneg]
    let phi : State.QuaternionState I := ⟨psi <• (r : ℍ[ℝ]), hscaled⟩
    rcases h phi with ⟨eta, heta, heq⟩
    refine ⟨eta, heta, ?_⟩
    have heq' :
        (U *ᵥ psi) <• (r : ℍ[ℝ]) =
          ((V *ᵥ psi) <• (r : ℍ[ℝ])) <• eta := by
      simpa only [phi, State.quaternion_mulVec_right_smul] using heq
    funext y
    have hy := congrFun heq' y
    change (U *ᵥ psi) y * (r : ℍ[ℝ]) =
      ((V *ᵥ psi) y * (r : ℍ[ℝ])) * eta at hy
    simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop] at ⊢
    have hrH0 : (r : ℍ[ℝ]) ≠ 0 := by
      intro hr
      apply hr0
      have hre := congrArg (fun q : ℍ[ℝ] ↦ q.re) hr
      simpa using hre
    calc
      (U *ᵥ psi) y = ((U *ᵥ psi) y * (r : ℍ[ℝ])) * (r : ℍ[ℝ])⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hrH0, mul_one]
      _ = (((V *ᵥ psi) y * (r : ℍ[ℝ])) * eta) * (r : ℍ[ℝ])⁻¹ := by
        rw [hy]
      _ = (((V *ᵥ psi) y * eta) * (r : ℍ[ℝ])) * (r : ℍ[ℝ])⁻¹ := by
        congr 1
        calc
          ((V *ᵥ psi) y * (r : ℍ[ℝ])) * eta =
              (V *ᵥ psi) y * ((r : ℍ[ℝ]) * eta) := by rw [mul_assoc]
          _ = (V *ᵥ psi) y * (eta * (r : ℍ[ℝ])) := by
            rw [_root_.Quaternion.coe_commutes]
          _ = ((V *ᵥ psi) y * eta) * (r : ℍ[ℝ]) := by rw [mul_assoc]
      _ = (V *ᵥ psi) y * eta := by
        rw [mul_assoc, mul_inv_cancel₀ hrH0, mul_one]

end QuaternionProjectiveActionEq

/-- Raw and normalized quaternionic projective action are equivalent on every finite input type. -/
theorem quaternionRawProjectiveActionEq_iff_projectiveActionEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]} :
    QuaternionRawProjectiveActionEq U V ↔ QuaternionProjectiveActionEq U V :=
  ⟨QuaternionRawProjectiveActionEq.projectiveActionEq,
    QuaternionProjectiveActionEq.rawProjectiveActionEq⟩

/-! ## Central-sign implications and unitarity -/

namespace QuaternionCentralSignEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- One central real sign specializes to a constant input-right-phase family. -/
theorem inputRightPhaseEq (h : QuaternionCentralSignEq U V) :
    QuaternionInputRightPhaseEq U V := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨fun _ ↦ (s : ℍ[ℝ]), fun _ ↦ by
    simpa [_root_.Quaternion.normSq_coe, pow_two] using hs, ?_⟩
  intro y x
  have hv := congrFun (congrFun hV y) x
  change V y x = U y x * (s : ℍ[ℝ])
  rw [hv]
  change s • U y x = U y x * (s : ℍ[ℝ])
  rw [← _root_.Quaternion.coe_mul_eq_smul]
  exact _root_.Quaternion.coe_commutes s (U y x)

/-- One central real sign specializes to a constant output-left-phase family. -/
theorem outputLeftPhaseEq (h : QuaternionCentralSignEq U V) :
    QuaternionOutputLeftPhaseEq U V := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨fun _ ↦ (s : ℍ[ℝ]), fun _ ↦ by
    simpa [_root_.Quaternion.normSq_coe, pow_two] using hs, ?_⟩
  intro y x
  have hv := congrFun (congrFun hV y) x
  change V y x = (s : ℍ[ℝ]) * U y x
  rw [hv]
  change s • U y x = (s : ℍ[ℝ]) * U y x
  exact (_root_.Quaternion.coe_mul_eq_smul s (U y x)).symm

/-- One central real sign gives equal right-ray action on every raw input column. -/
theorem rawProjectiveActionEq [Fintype I] (h : QuaternionCentralSignEq U V) :
    QuaternionRawProjectiveActionEq U V := by
  rcases h with ⟨s, hs, hV⟩
  intro psi
  apply Quaternion.rightPhaseEquivalent_symm
  refine ⟨(s : ℍ[ℝ]), ?_, ?_⟩
  · simpa [_root_.Quaternion.normSq_coe, pow_two] using hs
  · rw [hV, Matrix.smul_mulVec]
    funext y
    simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop]
    rw [← _root_.Quaternion.coe_mul_eq_smul]
    exact _root_.Quaternion.coe_commutes s ((U *ᵥ psi) y)

/-- One central real sign gives equal right-ray action on every normalized pure input. -/
theorem projectiveActionEq [Fintype I] (h : QuaternionCentralSignEq U V) :
    QuaternionProjectiveActionEq U V :=
  h.rawProjectiveActionEq.projectiveActionEq

/-- Multiplication by one central real unit sign preserves quaternionic unitarity. -/
theorem mem_unitary [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]} (h : QuaternionCentralSignEq U V)
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ])) :
    V ∈ unitary (Matrix I I ℍ[ℝ]) := by
  rcases h with ⟨s, hs, rfl⟩
  rw [Unitary.mem_iff] at hU ⊢
  rcases hU with ⟨hstar, hself⟩
  have hstar_smul : star (s • U) = s • star U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    funext y x
    exact _root_.Quaternion.star_smul s (U x y)
  constructor
  · rw [hstar_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
      one_smul, hstar]
  · rw [hstar_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
      one_smul, hself]

/-- Centrally sign-equivalent quaternionic square matrices are unitary simultaneously. -/
theorem mem_unitary_iff [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]} (h : QuaternionCentralSignEq U V) :
    U ∈ unitary (Matrix I I ℍ[ℝ]) ↔
      V ∈ unitary (Matrix I I ℍ[ℝ]) :=
  ⟨h.mem_unitary, h.symm.mem_unitary⟩

end QuaternionCentralSignEq

/-! ## Measurement consequences -/

namespace QuaternionInputRightPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- Input-column right phases preserve all basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : QuaternionInputRightPhaseEq U V) :
    BasisMeasurementEq State.quaternionWeight U V := by
  rcases h with ⟨phi, hphi, hV⟩
  intro x y
  simp only [State.quaternionWeight_apply, hV, map_mul, hphi, mul_one]

end QuaternionInputRightPhaseEq

namespace QuaternionOutputLeftPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℍ[ℝ]}

/-- Output-row left phases preserve all basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : QuaternionOutputLeftPhaseEq U V) :
    BasisMeasurementEq State.quaternionWeight U V := by
  rcases h with ⟨theta, htheta, hV⟩
  intro x y
  simp only [State.quaternionWeight_apply, hV, map_mul, htheta, one_mul]

/-- Output-row left phases factor pointwise through matrix-vector multiplication. -/
theorem mulVec_eq (h : QuaternionOutputLeftPhaseEq U V) [Fintype I]
    (psi : I → ℍ[ℝ]) :
    ∃ theta : O → ℍ[ℝ],
      (∀ y, _root_.Quaternion.normSq (theta y) = 1) ∧
        V *ᵥ psi = fun y ↦ theta y * (U *ᵥ psi) y := by
  rcases h with ⟨theta, htheta, hV⟩
  refine ⟨theta, htheta, ?_⟩
  funext y
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hV y x, mul_assoc]

/-- Output-row left phases preserve basis measurements for every normalized input. -/
theorem pureInputBasisMeasurementEq [Fintype I]
    (h : QuaternionOutputLeftPhaseEq U V) :
    PureInputBasisMeasurementEq State.quaternionWeight U V := by
  intro psi
  rcases h.mulVec_eq (psi : I → ℍ[ℝ]) with ⟨theta, htheta, hout⟩
  intro y
  change State.quaternionWeight ((U *ᵥ (psi : I → ℍ[ℝ])) y) =
    State.quaternionWeight ((V *ᵥ (psi : I → ℍ[ℝ])) y)
  rw [congrFun hout y]
  simp [State.quaternionWeight, map_mul, htheta y]

end QuaternionOutputLeftPhaseEq

namespace QuaternionProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℍ[ℝ]}

/-- Quaternionic projective-action equality preserves every pure-input basis measurement. -/
theorem pureInputBasisMeasurementEq (h : QuaternionProjectiveActionEq U V) :
    PureInputBasisMeasurementEq State.quaternionWeight U V :=
  fun psi y ↦ State.rightPhaseEquivalent_quaternionBasisWeight (h psi) y

end QuaternionProjectiveActionEq

end QuaternionicComputing.Semantics
