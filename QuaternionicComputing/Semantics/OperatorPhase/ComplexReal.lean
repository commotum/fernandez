module

public import QuaternionicComputing.Semantics.StatePhase

/-!
# Real and complex operator phase semantics

This leaf separates four real operator comparisons and their four complex
counterparts: one global phase, an input-column phase family, an output-row
phase family, and equality of projective action on every normalized pure
input.  The formulas retain their semantic orientation: global phase acts by
`V = phase • U`, input phase acts on each matrix entry on the right, and
output phase acts on each matrix entry on the left.

The relations are defined for rectangular matrices whenever possible.  This
file proves their equivalence laws, their valid exact/global/observational
implications, and preservation of square-matrix unitarity by one global
phase.  It intentionally contains no circuit wrappers, quaternionic operator
phase, channels, or strictness witnesses.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Operator relations -/

/-- Real matrices agree up to one global unit sign, oriented as `V = s • U`. -/
def RealGlobalSignEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℝ) : Prop :=
  ∃ s : ℝ, s * s = 1 ∧ V = s • U

/-- Complex matrices agree up to one global unit phase, oriented as `V = η • U`. -/
def ComplexGlobalPhaseEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℂ) : Prop :=
  ∃ eta : ℂ, Complex.normSq eta = 1 ∧ V = eta • U

/-- Each input column of `V` is the corresponding column of `U` times a unit sign. -/
def RealInputBasisSignEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℝ) : Prop :=
  ∃ s : I → ℝ, (∀ x, s x * s x = 1) ∧
    ∀ y x, V y x = U y x * s x

/-- Each input column of `V` is the corresponding column of `U` times a unit phase. -/
def ComplexInputBasisPhaseEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℂ) : Prop :=
  ∃ eta : I → ℂ, (∀ x, Complex.normSq (eta x) = 1) ∧
    ∀ y x, V y x = U y x * eta x

/-- Each output row of `V` is a unit sign times the corresponding row of `U`. -/
def RealOutputBasisSignEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℝ) : Prop :=
  ∃ s : O → ℝ, (∀ y, s y * s y = 1) ∧
    ∀ y x, V y x = s y * U y x

/-- Each output row of `V` is a unit phase times the corresponding row of `U`. -/
def ComplexOutputBasisPhaseEq {O : Type u} {I : Type v}
    (U V : Matrix O I ℂ) : Prop :=
  ∃ eta : O → ℂ, (∀ y, Complex.normSq (eta y) = 1) ∧
    ∀ y x, V y x = eta y * U y x

/-- Real matrices have the same projective action on every normalized pure input. -/
def RealProjectiveActionEq {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℝ) : Prop :=
  ∀ psi : State.RealState I,
    Real.SignEquivalent (U *ᵥ (psi : I → ℝ)) (V *ᵥ (psi : I → ℝ))

/-- Complex matrices have the same projective action on every normalized pure input. -/
def ComplexProjectiveActionEq {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℂ) : Prop :=
  ∀ psi : State.ComplexState I,
    Complex.RightPhaseEquivalent (U *ᵥ (psi : I → ℂ))
      (V *ᵥ (psi : I → ℂ))

/-! ## Equivalence laws -/

namespace RealGlobalSignEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℝ}

@[refl]
theorem refl (U : Matrix O I ℝ) : RealGlobalSignEq U U :=
  ⟨1, by norm_num, by simp⟩

@[symm]
theorem symm (h : RealGlobalSignEq U V) : RealGlobalSignEq V U := by
  rcases h with ⟨s, hs, rfl⟩
  refine ⟨s, hs, ?_⟩
  funext y x
  change U y x = s * (s * U y x)
  rw [← mul_assoc, hs, one_mul]

@[trans]
theorem trans (hUV : RealGlobalSignEq U V)
    (hVT : RealGlobalSignEq V T) : RealGlobalSignEq U T := by
  rcases hUV with ⟨s, hs, hV⟩
  rcases hVT with ⟨t, ht, hT⟩
  refine ⟨t * s, ?_, ?_⟩
  · calc
      (t * s) * (t * s) = (t * t) * (s * s) := by ring
      _ = 1 := by rw [ht, hs, one_mul]
  · rw [hT, hV, smul_smul]

/-- Real global-sign equality is an equivalence relation. -/
theorem equivalence : Equivalence (@RealGlobalSignEq O I) :=
  ⟨refl, symm, trans⟩

end RealGlobalSignEq

namespace ComplexGlobalPhaseEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℂ}

@[refl]
theorem refl (U : Matrix O I ℂ) : ComplexGlobalPhaseEq U U :=
  ⟨1, by simp, by simp⟩

@[symm]
theorem symm (h : ComplexGlobalPhaseEq U V) :
    ComplexGlobalPhaseEq V U := by
  rcases h with ⟨eta, heta, rfl⟩
  refine ⟨star eta, by simpa using heta, ?_⟩
  rw [smul_smul]
  funext y x
  change U y x = ((starRingEnd ℂ) eta * eta) * U y x
  rw [mul_comm ((starRingEnd ℂ) eta) eta, Complex.mul_conj, heta]
  simp

@[trans]
theorem trans (hUV : ComplexGlobalPhaseEq U V)
    (hVT : ComplexGlobalPhaseEq V T) : ComplexGlobalPhaseEq U T := by
  rcases hUV with ⟨eta, heta, hV⟩
  rcases hVT with ⟨theta, htheta, hT⟩
  refine ⟨theta * eta, ?_, ?_⟩
  · rw [Complex.normSq_mul, htheta, heta, one_mul]
  · rw [hT, hV, smul_smul]

/-- Complex global-phase equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ComplexGlobalPhaseEq O I) :=
  ⟨refl, symm, trans⟩

end ComplexGlobalPhaseEq

namespace RealInputBasisSignEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℝ}

@[refl]
theorem refl (U : Matrix O I ℝ) : RealInputBasisSignEq U U :=
  ⟨fun _ ↦ 1, fun _ ↦ by norm_num, by simp⟩

@[symm]
theorem symm (h : RealInputBasisSignEq U V) :
    RealInputBasisSignEq V U := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨s, hs, ?_⟩
  intro y x
  rw [hV y x, mul_assoc, hs x, mul_one]

@[trans]
theorem trans (hUV : RealInputBasisSignEq U V)
    (hVT : RealInputBasisSignEq V T) : RealInputBasisSignEq U T := by
  rcases hUV with ⟨s, hs, hV⟩
  rcases hVT with ⟨t, ht, hT⟩
  refine ⟨fun x ↦ s x * t x, ?_, ?_⟩
  · intro x
    calc
      (s x * t x) * (s x * t x) = (s x * s x) * (t x * t x) := by ring
      _ = 1 := by rw [hs x, ht x, one_mul]
  · intro y x
    rw [hT y x, hV y x, mul_assoc]

/-- Real input-basis-sign equality is an equivalence relation. -/
theorem equivalence : Equivalence (@RealInputBasisSignEq O I) :=
  ⟨refl, symm, trans⟩

end RealInputBasisSignEq

namespace ComplexInputBasisPhaseEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℂ}

@[refl]
theorem refl (U : Matrix O I ℂ) : ComplexInputBasisPhaseEq U U :=
  ⟨fun _ ↦ 1, fun _ ↦ by simp, by simp⟩

@[symm]
theorem symm (h : ComplexInputBasisPhaseEq U V) :
    ComplexInputBasisPhaseEq V U := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨fun x ↦ star (eta x), fun x ↦ by simpa using heta x, ?_⟩
  intro y x
  rw [hV y x, mul_assoc]
  change U y x = U y x * (eta x * (starRingEnd ℂ) (eta x))
  rw [Complex.mul_conj, heta x]
  simp

@[trans]
theorem trans (hUV : ComplexInputBasisPhaseEq U V)
    (hVT : ComplexInputBasisPhaseEq V T) :
    ComplexInputBasisPhaseEq U T := by
  rcases hUV with ⟨eta, heta, hV⟩
  rcases hVT with ⟨theta, htheta, hT⟩
  refine ⟨fun x ↦ eta x * theta x, ?_, ?_⟩
  · intro x
    rw [Complex.normSq_mul, heta x, htheta x, one_mul]
  · intro y x
    rw [hT y x, hV y x, mul_assoc]

/-- Complex input-basis-phase equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ComplexInputBasisPhaseEq O I) :=
  ⟨refl, symm, trans⟩

end ComplexInputBasisPhaseEq

namespace RealOutputBasisSignEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℝ}

@[refl]
theorem refl (U : Matrix O I ℝ) : RealOutputBasisSignEq U U :=
  ⟨fun _ ↦ 1, fun _ ↦ by norm_num, by simp⟩

@[symm]
theorem symm (h : RealOutputBasisSignEq U V) :
    RealOutputBasisSignEq V U := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨s, hs, ?_⟩
  intro y x
  rw [hV y x, ← mul_assoc, hs y, one_mul]

@[trans]
theorem trans (hUV : RealOutputBasisSignEq U V)
    (hVT : RealOutputBasisSignEq V T) : RealOutputBasisSignEq U T := by
  rcases hUV with ⟨s, hs, hV⟩
  rcases hVT with ⟨t, ht, hT⟩
  refine ⟨fun y ↦ t y * s y, ?_, ?_⟩
  · intro y
    calc
      (t y * s y) * (t y * s y) = (t y * t y) * (s y * s y) := by ring
      _ = 1 := by rw [ht y, hs y, one_mul]
  · intro y x
    rw [hT y x, hV y x, mul_assoc]

/-- Real output-basis-sign equality is an equivalence relation. -/
theorem equivalence : Equivalence (@RealOutputBasisSignEq O I) :=
  ⟨refl, symm, trans⟩

end RealOutputBasisSignEq

namespace ComplexOutputBasisPhaseEq

variable {O : Type u} {I : Type v} {U V T : Matrix O I ℂ}

@[refl]
theorem refl (U : Matrix O I ℂ) : ComplexOutputBasisPhaseEq U U :=
  ⟨fun _ ↦ 1, fun _ ↦ by simp, by simp⟩

@[symm]
theorem symm (h : ComplexOutputBasisPhaseEq U V) :
    ComplexOutputBasisPhaseEq V U := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨fun y ↦ star (eta y), fun y ↦ by simpa using heta y, ?_⟩
  intro y x
  rw [hV y x, ← mul_assoc]
  change U y x = ((starRingEnd ℂ) (eta y) * eta y) * U y x
  rw [mul_comm ((starRingEnd ℂ) (eta y)) (eta y), Complex.mul_conj,
    heta y]
  simp

@[trans]
theorem trans (hUV : ComplexOutputBasisPhaseEq U V)
    (hVT : ComplexOutputBasisPhaseEq V T) :
    ComplexOutputBasisPhaseEq U T := by
  rcases hUV with ⟨eta, heta, hV⟩
  rcases hVT with ⟨theta, htheta, hT⟩
  refine ⟨fun y ↦ theta y * eta y, ?_, ?_⟩
  · intro y
    rw [Complex.normSq_mul, htheta y, heta y, one_mul]
  · intro y x
    rw [hT y x, hV y x, mul_assoc]

/-- Complex output-basis-phase equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ComplexOutputBasisPhaseEq O I) :=
  ⟨refl, symm, trans⟩

end ComplexOutputBasisPhaseEq

namespace RealProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V T : Matrix O I ℝ}

@[refl]
theorem refl (U : Matrix O I ℝ) : RealProjectiveActionEq U U :=
  fun psi ↦ Real.signEquivalent_refl (U *ᵥ (psi : I → ℝ))

@[symm]
theorem symm (h : RealProjectiveActionEq U V) :
    RealProjectiveActionEq V U :=
  fun psi ↦ Real.signEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : RealProjectiveActionEq U V)
    (hVT : RealProjectiveActionEq V T) : RealProjectiveActionEq U T :=
  fun psi ↦ Real.signEquivalent_trans (hUV psi) (hVT psi)

/-- Real projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@RealProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V T : Matrix O I ℂ}

@[refl]
theorem refl (U : Matrix O I ℂ) : ComplexProjectiveActionEq U U :=
  fun psi ↦ Complex.rightPhaseEquivalent_refl (U *ᵥ (psi : I → ℂ))

@[symm]
theorem symm (h : ComplexProjectiveActionEq U V) :
    ComplexProjectiveActionEq V U :=
  fun psi ↦ Complex.rightPhaseEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : ComplexProjectiveActionEq U V)
    (hVT : ComplexProjectiveActionEq V T) : ComplexProjectiveActionEq U T :=
  fun psi ↦ Complex.rightPhaseEquivalent_trans (hUV psi) (hVT psi)

/-- Complex projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ComplexProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

end ComplexProjectiveActionEq

/-! ## Exact, global-phase, and observational implications -/

namespace RealGlobalSignEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℝ}

/-- Exact real operator equality implies global-sign equality. -/
theorem of_exact (h : ExactOperatorEq U V) : RealGlobalSignEq U V := by
  subst V
  exact refl U

/-- One real global sign specializes to a constant input-column sign family. -/
theorem inputBasisSignEq (h : RealGlobalSignEq U V) :
    RealInputBasisSignEq U V := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨fun _ ↦ s, fun _ ↦ hs, ?_⟩
  intro y x
  have hv := congrFun (congrFun hV y) x
  simpa [mul_comm] using hv

/-- One real global sign specializes to a constant output-row sign family. -/
theorem outputBasisSignEq (h : RealGlobalSignEq U V) :
    RealOutputBasisSignEq U V := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨fun _ ↦ s, fun _ ↦ hs, ?_⟩
  intro y x
  exact congrFun (congrFun hV y) x

/-- One real global sign gives equal projective action on normalized inputs. -/
theorem projectiveActionEq [Fintype I] (h : RealGlobalSignEq U V) :
    RealProjectiveActionEq U V := by
  rcases h with ⟨s, hs, hV⟩
  intro psi
  apply Real.signEquivalent_symm
  refine ⟨s, hs, ?_⟩
  rw [hV, Matrix.smul_mulVec]
  funext y
  simp [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Multiplication by one real global unit sign preserves unitarity. -/
theorem mem_unitary [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℝ} (h : RealGlobalSignEq U V)
    (hU : U ∈ unitary (Matrix I I ℝ)) :
    V ∈ unitary (Matrix I I ℝ) := by
  rcases h with ⟨s, hs, rfl⟩
  rw [Unitary.mem_iff] at hU ⊢
  rcases hU with ⟨hstar, hself⟩
  constructor
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs] using hstar
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs] using hself

/-- Real globally sign-equivalent square matrices are unitary simultaneously. -/
theorem mem_unitary_iff [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℝ} (h : RealGlobalSignEq U V) :
    U ∈ unitary (Matrix I I ℝ) ↔ V ∈ unitary (Matrix I I ℝ) :=
  ⟨h.mem_unitary, h.symm.mem_unitary⟩

end RealGlobalSignEq

namespace ComplexGlobalPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℂ}

/-- Exact complex operator equality implies global-phase equality. -/
theorem of_exact (h : ExactOperatorEq U V) : ComplexGlobalPhaseEq U V := by
  subst V
  exact refl U

/-- One complex global phase specializes to a constant input-column phase family. -/
theorem inputBasisPhaseEq (h : ComplexGlobalPhaseEq U V) :
    ComplexInputBasisPhaseEq U V := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨fun _ ↦ eta, fun _ ↦ heta, ?_⟩
  intro y x
  have hv := congrFun (congrFun hV y) x
  simpa [mul_comm] using hv

/-- One complex global phase specializes to a constant output-row phase family. -/
theorem outputBasisPhaseEq (h : ComplexGlobalPhaseEq U V) :
    ComplexOutputBasisPhaseEq U V := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨fun _ ↦ eta, fun _ ↦ heta, ?_⟩
  intro y x
  exact congrFun (congrFun hV y) x

/-- One complex global phase gives equal projective action on normalized inputs. -/
theorem projectiveActionEq [Fintype I] (h : ComplexGlobalPhaseEq U V) :
    ComplexProjectiveActionEq U V := by
  rcases h with ⟨eta, heta, hV⟩
  intro psi
  apply Complex.rightPhaseEquivalent_symm
  refine ⟨eta, heta, ?_⟩
  rw [hV, Matrix.smul_mulVec]
  funext y
  simp [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Multiplication by one complex global unit phase preserves unitarity. -/
theorem mem_unitary [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℂ} (h : ComplexGlobalPhaseEq U V)
    (hU : U ∈ unitary (Matrix I I ℂ)) :
    V ∈ unitary (Matrix I I ℂ) := by
  rcases h with ⟨eta, heta, rfl⟩
  have hetaLeft : eta * (starRingEnd ℂ) eta = 1 := by
    rw [Complex.mul_conj, heta]
    norm_num
  have hetaRight : (starRingEnd ℂ) eta * eta = 1 := by
    rw [mul_comm, Complex.mul_conj, heta]
    norm_num
  rw [Unitary.mem_iff] at hU ⊢
  rcases hU with ⟨hstar, hself⟩
  constructor
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hetaLeft,
      hetaRight] using hstar
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hetaLeft,
      hetaRight] using hself

/-- Complex globally phase-equivalent square matrices are unitary simultaneously. -/
theorem mem_unitary_iff [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℂ} (h : ComplexGlobalPhaseEq U V) :
    U ∈ unitary (Matrix I I ℂ) ↔ V ∈ unitary (Matrix I I ℂ) :=
  ⟨h.mem_unitary, h.symm.mem_unitary⟩

end ComplexGlobalPhaseEq

namespace RealInputBasisSignEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℝ}

/-- Exact real operator equality implies input-basis-sign equality. -/
theorem of_exact (h : ExactOperatorEq U V) : RealInputBasisSignEq U V := by
  subst V
  exact refl U

/-- An input-column sign family preserves basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : RealInputBasisSignEq U V) :
    BasisMeasurementEq State.realWeight U V := by
  rcases h with ⟨s, hs, hV⟩
  intro x y
  rw [hV y x]
  change U y x * U y x = (U y x * s x) * (U y x * s x)
  calc
    (U y x * U y x) = (U y x * U y x) * 1 := by ring
    _ = (U y x * U y x) * (s x * s x) := by rw [hs x]
    _ = (U y x * s x) * (U y x * s x) := by ring

end RealInputBasisSignEq

namespace ComplexInputBasisPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℂ}

/-- Exact complex operator equality implies input-basis-phase equality. -/
theorem of_exact (h : ExactOperatorEq U V) : ComplexInputBasisPhaseEq U V := by
  subst V
  exact refl U

/-- An input-column phase family preserves basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : ComplexInputBasisPhaseEq U V) :
    BasisMeasurementEq State.complexWeight U V := by
  rcases h with ⟨eta, heta, hV⟩
  intro x y
  rw [hV y x]
  simp [State.complexWeight, Complex.normSq_mul, heta x]

end ComplexInputBasisPhaseEq

namespace RealOutputBasisSignEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℝ}

/-- Exact real operator equality implies output-basis-sign equality. -/
theorem of_exact (h : ExactOperatorEq U V) : RealOutputBasisSignEq U V := by
  subst V
  exact refl U

/-- An output-row sign family preserves basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : RealOutputBasisSignEq U V) :
    BasisMeasurementEq State.realWeight U V := by
  rcases h with ⟨s, hs, hV⟩
  intro x y
  rw [hV y x]
  change U y x * U y x = (s y * U y x) * (s y * U y x)
  calc
    (U y x * U y x) = 1 * (U y x * U y x) := by ring
    _ = (s y * s y) * (U y x * U y x) := by rw [hs y]
    _ = (s y * U y x) * (s y * U y x) := by ring

/-- Output-row signs factor pointwise through matrix-vector multiplication. -/
theorem mulVec_eq (h : RealOutputBasisSignEq U V) [Fintype I]
    (psi : I → ℝ) :
    ∃ s : O → ℝ, (∀ y, s y * s y = 1) ∧
      V *ᵥ psi = fun y ↦ s y * (U *ᵥ psi) y := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨s, hs, ?_⟩
  funext y
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hV y x, mul_assoc]

/-- Output-row sign equality preserves measurements for every normalized input. -/
theorem pureInputBasisMeasurementEq [Fintype I]
    (h : RealOutputBasisSignEq U V) :
    PureInputBasisMeasurementEq State.realWeight U V := by
  intro psi
  rcases h.mulVec_eq (psi : I → ℝ) with ⟨s, hs, hout⟩
  intro y
  change State.realWeight ((U *ᵥ (psi : I → ℝ)) y) =
    State.realWeight ((V *ᵥ (psi : I → ℝ)) y)
  rw [congrFun hout y]
  change (U *ᵥ (psi : I → ℝ)) y * (U *ᵥ (psi : I → ℝ)) y =
    (s y * (U *ᵥ (psi : I → ℝ)) y) *
      (s y * (U *ᵥ (psi : I → ℝ)) y)
  calc
    (U *ᵥ (psi : I → ℝ)) y * (U *ᵥ (psi : I → ℝ)) y =
        1 * ((U *ᵥ (psi : I → ℝ)) y * (U *ᵥ (psi : I → ℝ)) y) := by
      ring
    _ = (s y * s y) *
        ((U *ᵥ (psi : I → ℝ)) y * (U *ᵥ (psi : I → ℝ)) y) := by
      rw [hs y]
    _ = (s y * (U *ᵥ (psi : I → ℝ)) y) *
        (s y * (U *ᵥ (psi : I → ℝ)) y) := by
      ring

end RealOutputBasisSignEq

namespace ComplexOutputBasisPhaseEq

variable {O : Type u} {I : Type v} {U V : Matrix O I ℂ}

/-- Exact complex operator equality implies output-basis-phase equality. -/
theorem of_exact (h : ExactOperatorEq U V) :
    ComplexOutputBasisPhaseEq U V := by
  subst V
  exact refl U

/-- An output-row phase family preserves basis-preparation measurement weights. -/
theorem basisMeasurementEq (h : ComplexOutputBasisPhaseEq U V) :
    BasisMeasurementEq State.complexWeight U V := by
  rcases h with ⟨eta, heta, hV⟩
  intro x y
  rw [hV y x]
  simp [State.complexWeight, Complex.normSq_mul, heta y]

/-- Output-row phases factor pointwise through matrix-vector multiplication. -/
theorem mulVec_eq (h : ComplexOutputBasisPhaseEq U V) [Fintype I]
    (psi : I → ℂ) :
    ∃ eta : O → ℂ, (∀ y, Complex.normSq (eta y) = 1) ∧
      V *ᵥ psi = fun y ↦ eta y * (U *ᵥ psi) y := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨eta, heta, ?_⟩
  funext y
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hV y x, mul_assoc]

/-- Output-row phase equality preserves measurements for every normalized input. -/
theorem pureInputBasisMeasurementEq [Fintype I]
    (h : ComplexOutputBasisPhaseEq U V) :
    PureInputBasisMeasurementEq State.complexWeight U V := by
  intro psi
  rcases h.mulVec_eq (psi : I → ℂ) with ⟨eta, heta, hout⟩
  intro y
  change State.complexWeight ((U *ᵥ (psi : I → ℂ)) y) =
    State.complexWeight ((V *ᵥ (psi : I → ℂ)) y)
  rw [congrFun hout y]
  simp [State.complexWeight, Complex.normSq_mul, heta y]

end ComplexOutputBasisPhaseEq

namespace RealProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℝ}

/-- Exact real operator equality implies projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) : RealProjectiveActionEq U V := by
  subst V
  exact refl U

/-- Real projective-action equality preserves every pure-input basis measurement. -/
theorem pureInputBasisMeasurementEq (h : RealProjectiveActionEq U V) :
    PureInputBasisMeasurementEq State.realWeight U V :=
  fun psi y ↦ State.signEquivalent_realBasisWeight (h psi) y

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℂ}

/-- Exact complex operator equality implies projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) :
    ComplexProjectiveActionEq U V := by
  subst V
  exact refl U

/-- Complex projective-action equality preserves every pure-input basis measurement. -/
theorem pureInputBasisMeasurementEq (h : ComplexProjectiveActionEq U V) :
    PureInputBasisMeasurementEq State.complexWeight U V :=
  fun psi y ↦ State.rightPhaseEquivalent_complexBasisWeight (h psi) y

end ComplexProjectiveActionEq

end QuaternionicComputing.Semantics
