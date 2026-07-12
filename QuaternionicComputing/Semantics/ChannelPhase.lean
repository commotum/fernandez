module

public import QuaternionicComputing.Semantics.Channel
public import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal

/-!
# Real and complex unitary-channel phase kernels

This proof leaf connects the physical channel equality of bundled finite
unitaries to the existing real and complex operator-phase relations.  It first
shows that equal normalized ket--bra matrices determine the same real sign or
complex right phase.  It then extends normalized projective action to every
raw input column by an explicit zero/nonzero normalization argument.

For an inhabited finite space, basis columns and their pairwise sums force a
ray-fixing matrix to be one scalar multiple of the identity.  Consequently,
real global-sign equality, complex global-phase equality, normalized
projective action, raw projective action, and unitary-channel equality have
the expected common kernel.  No determinant argument or dimension-at-least-two
assumption is used.

The physical characterization theorems state `Nonempty I` explicitly.  Empty
index types have no density matrices, so channel equality is vacuous there;
separate boundary theorems record that their square matrices are nevertheless
equal and hence globally phase equivalent.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Equal pure densities determine one phase -/

private theorem pureMatrix_mulVec
    {I : Type u} [Fintype I]
    {𝕜 : Type v} [RCLike 𝕜] (y x : I → 𝕜) :
    DensityMatrix.pureMatrix y *ᵥ x =
      fun i ↦ y i * (star y ⬝ᵥ x) := by
  funext i
  simp [DensityMatrix.pureMatrix, Matrix.mulVec, Matrix.vecMulVec_apply,
    dotProduct, Finset.mul_sum, mul_assoc]

private theorem real_star_dot_eq_total
    {I : Type u} [Fintype I] (x : I → ℝ) :
    star x ⬝ᵥ x = State.realTotalWeight x := by
  simp [State.realTotalWeight, State.totalWeight, State.basisWeight,
    State.realWeight, dotProduct]

private theorem complex_star_dot_eq_total
    {I : Type u} [Fintype I] (x : I → ℂ) :
    star x ⬝ᵥ x = (State.complexTotalWeight x : ℂ) := by
  simp [State.complexTotalWeight, State.totalWeight, State.basisWeight,
    State.complexWeight, dotProduct,
    ← Complex.normSq_eq_conj_mul_self]

/--
Equal real ket--bra matrices, with one ket normalized, differ by one unit sign.

The second ket is automatically normalized because the equal ket--bras have
equal traces, so no redundant normalization premise is required.
-/
theorem realSignEquivalent_of_normalized_pureMatrix_eq
    {I : Type u} [Fintype I] {x y : I → ℝ}
    (hx : star x ⬝ᵥ x = 1)
    (h : DensityMatrix.pureMatrix x = DensityMatrix.pureMatrix y) :
    Real.SignEquivalent x y := by
  have hy : star y ⬝ᵥ y = 1 := by
    calc
      star y ⬝ᵥ y = Matrix.trace (DensityMatrix.pureMatrix y) :=
        (DensityMatrix.trace_pureMatrix y).symm
      _ = Matrix.trace (DensityMatrix.pureMatrix x) :=
        congrArg Matrix.trace h.symm
      _ = star x ⬝ᵥ x := DensityMatrix.trace_pureMatrix x
      _ = 1 := hx
  let s : ℝ := star y ⬝ᵥ x
  have hxy : x = fun i ↦ y i * s := by
    have hv := congrArg (fun A : Matrix I I ℝ ↦ A *ᵥ x) h
    simpa only [pureMatrix_mulVec, hx, mul_one, s] using hv
  refine ⟨s, ?_, hxy⟩
  have hweight := State.realTotalWeight_right_mul y s
  rw [← hxy] at hweight
  rw [← real_star_dot_eq_total, hx, ← real_star_dot_eq_total, hy,
    one_mul] at hweight
  exact hweight.symm

/--
Equal complex ket--bra matrices, with one ket normalized, differ by one unit
right phase.  The second normalization follows from equality of traces.
-/
theorem complexRightPhaseEquivalent_of_normalized_pureMatrix_eq
    {I : Type u} [Fintype I] {x y : I → ℂ}
    (hx : star x ⬝ᵥ x = 1)
    (h : DensityMatrix.pureMatrix x = DensityMatrix.pureMatrix y) :
    Complex.RightPhaseEquivalent x y := by
  have hy : star y ⬝ᵥ y = 1 := by
    calc
      star y ⬝ᵥ y = Matrix.trace (DensityMatrix.pureMatrix y) :=
        (DensityMatrix.trace_pureMatrix y).symm
      _ = Matrix.trace (DensityMatrix.pureMatrix x) :=
        congrArg Matrix.trace h.symm
      _ = star x ⬝ᵥ x := DensityMatrix.trace_pureMatrix x
      _ = 1 := hx
  let eta : ℂ := star y ⬝ᵥ x
  have hxy : x = fun i ↦ y i * eta := by
    have hv := congrArg (fun A : Matrix I I ℂ ↦ A *ᵥ x) h
    simpa only [pureMatrix_mulVec, hx, mul_one, eta] using hv
  refine ⟨eta, ?_, hxy⟩
  have hweight := State.complexTotalWeight_right_mul y eta
  rw [← hxy] at hweight
  have hxw : State.complexTotalWeight x = 1 := by
    have hx' := hx
    rw [complex_star_dot_eq_total] at hx'
    exact_mod_cast hx'
  have hyw : State.complexTotalWeight y = 1 := by
    have hy' := hy
    rw [complex_star_dot_eq_total] at hy'
    exact_mod_cast hy'
  rw [hxw, hyw, one_mul] at hweight
  exact hweight.symm

/-! ## Raw projective action and its equivalence laws -/

/-- Real matrices have sign-equivalent outputs on every raw input column. -/
def RealRawProjectiveActionEq
    {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℝ) : Prop :=
  ∀ psi : I → ℝ, Real.SignEquivalent (U *ᵥ psi) (V *ᵥ psi)

/-- Complex matrices have right-phase-equivalent outputs on every raw input column. -/
def ComplexRawProjectiveActionEq
    {O : Type u} {I : Type v} [Fintype I]
    (U V : Matrix O I ℂ) : Prop :=
  ∀ psi : I → ℂ,
    Complex.RightPhaseEquivalent (U *ᵥ psi) (V *ᵥ psi)

namespace RealRawProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V W : Matrix O I ℝ}

@[refl]
theorem refl (U : Matrix O I ℝ) : RealRawProjectiveActionEq U U :=
  fun psi ↦ Real.signEquivalent_refl (U *ᵥ psi)

@[symm]
theorem symm (h : RealRawProjectiveActionEq U V) :
    RealRawProjectiveActionEq V U :=
  fun psi ↦ Real.signEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : RealRawProjectiveActionEq U V)
    (hVW : RealRawProjectiveActionEq V W) :
    RealRawProjectiveActionEq U W :=
  fun psi ↦ Real.signEquivalent_trans (hUV psi) (hVW psi)

/-- Real raw projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@RealRawProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

/-- Exact real operator equality implies raw projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) :
    RealRawProjectiveActionEq U V := by
  subst V
  exact refl U

/-- Raw real projective action restricts to normalized pure inputs. -/
theorem projectiveActionEq (h : RealRawProjectiveActionEq U V) :
    RealProjectiveActionEq U V :=
  fun psi ↦ h psi

end RealRawProjectiveActionEq

namespace ComplexRawProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V W : Matrix O I ℂ}

@[refl]
theorem refl (U : Matrix O I ℂ) : ComplexRawProjectiveActionEq U U :=
  fun psi ↦ Complex.rightPhaseEquivalent_refl (U *ᵥ psi)

@[symm]
theorem symm (h : ComplexRawProjectiveActionEq U V) :
    ComplexRawProjectiveActionEq V U :=
  fun psi ↦ Complex.rightPhaseEquivalent_symm (h psi)

@[trans]
theorem trans (hUV : ComplexRawProjectiveActionEq U V)
    (hVW : ComplexRawProjectiveActionEq V W) :
    ComplexRawProjectiveActionEq U W :=
  fun psi ↦ Complex.rightPhaseEquivalent_trans (hUV psi) (hVW psi)

/-- Complex raw projective-action equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ComplexRawProjectiveActionEq O I _) :=
  ⟨refl, symm, trans⟩

/-- Exact complex operator equality implies raw projective-action equality. -/
theorem of_exact (h : ExactOperatorEq U V) :
    ComplexRawProjectiveActionEq U V := by
  subst V
  exact refl U

/-- Raw complex projective action restricts to normalized pure inputs. -/
theorem projectiveActionEq (h : ComplexRawProjectiveActionEq U V) :
    ComplexProjectiveActionEq U V :=
  fun psi ↦ h psi

end ComplexRawProjectiveActionEq

/-! ## Extending normalized projective action to raw columns -/

private theorem realTotalWeight_eq_zero_iff
    {I : Type u} [Fintype I] (psi : I → ℝ) :
    State.realTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, psi i * psi i) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ mul_self_nonneg (psi i))).trans (by
      simp [funext_iff])

private theorem complexTotalWeight_eq_zero_iff
    {I : Type u} [Fintype I] (psi : I → ℂ) :
    State.complexTotalWeight psi = 0 ↔ psi = 0 := by
  change (∑ i, Complex.normSq (psi i)) = 0 ↔ psi = 0
  exact (Fintype.sum_eq_zero_iff_of_nonneg
    (fun i ↦ Complex.normSq_nonneg (psi i))).trans (by
      simp [funext_iff])

namespace RealProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℝ}

/--
Normalized real projective action extends to every raw input column.

The zero column is immediate.  A nonzero column is multiplied by the inverse
square root of its total weight, the normalized hypothesis is applied, and
the nonzero real scaling factor is cancelled.
-/
theorem rawProjectiveActionEq (h : RealProjectiveActionEq U V) :
    RealRawProjectiveActionEq U V := by
  intro psi
  by_cases hpsi : psi = 0
  · subst psi
    simpa only [Matrix.mulVec_zero] using
      Real.signEquivalent_refl (0 : O → ℝ)
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
    rcases h phi with ⟨s, hs, heq⟩
    refine ⟨s, hs, ?_⟩
    have heq' :
        (fun i ↦ (U *ᵥ psi) i * r) =
          fun i ↦ ((V *ᵥ psi) i * r) * s := by
      simpa only [phi, State.real_mulVec_right_mul] using heq
    funext i
    have hi := congrFun heq' i
    apply mul_right_cancel₀ hr0
    calc
      (U *ᵥ psi) i * r = ((V *ᵥ psi) i * r) * s := hi
      _ = ((V *ᵥ psi) i * s) * r := by ring

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℂ}

/--
Normalized complex projective action extends to every raw input column by
zero/nonzero normalization and cancellation of a positive real scale.
-/
theorem rawProjectiveActionEq (h : ComplexProjectiveActionEq U V) :
    ComplexRawProjectiveActionEq U V := by
  intro psi
  by_cases hpsi : psi = 0
  · subst psi
    simpa only [Matrix.mulVec_zero] using
      Complex.rightPhaseEquivalent_refl (0 : O → ℂ)
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
    rcases h phi with ⟨eta, heta, heq⟩
    refine ⟨eta, heta, ?_⟩
    have heq' :
        (fun i ↦ (U *ᵥ psi) i * (r : ℂ)) =
          fun i ↦ ((V *ᵥ psi) i * (r : ℂ)) * eta := by
      simpa only [phi, State.complex_mulVec_right_mul] using heq
    funext i
    have hi := congrFun heq' i
    have hrC0 : (r : ℂ) ≠ 0 := by
      exact_mod_cast hr0
    apply mul_right_cancel₀ hrC0
    calc
      (U *ᵥ psi) i * (r : ℂ) =
          ((V *ᵥ psi) i * (r : ℂ)) * eta := hi
      _ = ((V *ᵥ psi) i * eta) * (r : ℂ) := by ring

end ComplexProjectiveActionEq

/-- Raw and normalized real projective action are equivalent on every finite input type. -/
theorem realRawProjectiveActionEq_iff_projectiveActionEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℝ} :
    RealRawProjectiveActionEq U V ↔ RealProjectiveActionEq U V :=
  ⟨RealRawProjectiveActionEq.projectiveActionEq,
    RealProjectiveActionEq.rawProjectiveActionEq⟩

/-- Raw and normalized complex projective action are equivalent on every finite input type. -/
theorem complexRawProjectiveActionEq_iff_projectiveActionEq
    {O : Type u} {I : Type v} [Fintype I]
    {U V : Matrix O I ℂ} :
    ComplexRawProjectiveActionEq U V ↔ ComplexProjectiveActionEq U V :=
  ⟨ComplexRawProjectiveActionEq.projectiveActionEq,
    ComplexProjectiveActionEq.rawProjectiveActionEq⟩

namespace RealGlobalSignEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℝ}

/-- One real global sign gives equal projective action on every raw input. -/
theorem rawProjectiveActionEq (h : RealGlobalSignEq U V) :
    RealRawProjectiveActionEq U V :=
  h.projectiveActionEq.rawProjectiveActionEq

end RealGlobalSignEq

namespace ComplexGlobalPhaseEq

variable {O : Type u} {I : Type v} [Fintype I]
variable {U V : Matrix O I ℂ}

/-- One complex global phase gives equal projective action on every raw input. -/
theorem rawProjectiveActionEq (h : ComplexGlobalPhaseEq U V) :
    ComplexRawProjectiveActionEq U V :=
  h.projectiveActionEq.rawProjectiveActionEq

end ComplexGlobalPhaseEq

/-! ## The inhabited finite projective kernels -/

private def FixesEveryRealRay
    {I : Type u} [Fintype I] (A : Matrix I I ℝ) : Prop :=
  ∀ psi : I → ℝ, Real.SignEquivalent (A *ᵥ psi) psi

private theorem fixesEveryRealRay_globalSign
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (hA : FixesEveryRealRay A) :
    ∃ s : ℝ, s * s = 1 ∧ A = s • (1 : Matrix I I ℝ) := by
  classical
  let i0 : I := Classical.choice inferInstance
  let s : I → ℝ := fun x ↦ (hA (Pi.single x 1)).choose
  have hs (x : I) : s x * s x = 1 :=
    (hA (Pi.single x 1)).choose_spec.1
  have hcol (x : I) :
      A *ᵥ Pi.single x (1 : ℝ) =
        fun i ↦ (Pi.single x (1 : ℝ) : I → ℝ) i * s x :=
    (hA (Pi.single x 1)).choose_spec.2
  have hentry (y x : I) : A y x = if y = x then s x else 0 := by
    have h := congrFun (hcol x) y
    simpa [Pi.single_apply] using h
  have hs_common (x : I) : s x = s i0 := by
    by_cases hxi : x = i0
    · simp [hxi]
    · rcases hA (Pi.single i0 1 + Pi.single x 1) with
        ⟨t, ht, hsum⟩
      rw [Matrix.mulVec_add, hcol i0, hcol x] at hsum
      have hs0 := congrFun hsum i0
      have hsx := congrFun hsum x
      simp [hxi, Ne.symm hxi] at hs0 hsx
      exact hsx.trans hs0.symm
  refine ⟨s i0, hs i0, ?_⟩
  funext y x
  rw [hentry, hs_common x]
  by_cases hyx : y = x
  · subst y
    simp
  · simp [hyx]

namespace RealRawProjectiveActionEq

/--
On an inhabited finite space, a unitary's raw real projective kernel is one
global sign.  Only `U` needs a unitary certificate.
-/
theorem globalSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℝ}
    (hU : U ∈ unitary (Matrix I I ℝ))
    (h : RealRawProjectiveActionEq U V) :
    RealGlobalSignEq U V := by
  let A : Matrix I I ℝ := V * star U
  have hfix : FixesEveryRealRay A := by
    intro psi
    have hp := Real.signEquivalent_symm (h (star U *ᵥ psi))
    simpa only [A, Matrix.mulVec_mulVec,
      Unitary.mul_star_self_of_mem hU, Matrix.one_mulVec] using hp
  rcases fixesEveryRealRay_globalSign A hfix with ⟨s, hs, hA⟩
  refine ⟨s, hs, ?_⟩
  have hmul := congrArg (fun M : Matrix I I ℝ ↦ M * U) hA
  simpa only [A, Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] using hmul

end RealRawProjectiveActionEq

private def FixesEveryComplexRightRay
    {I : Type u} [Fintype I] (A : Matrix I I ℂ) : Prop :=
  ∀ psi : I → ℂ,
    Complex.RightPhaseEquivalent (A *ᵥ psi) psi

private theorem fixesEveryComplexRightRay_globalPhase
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℂ) (hA : FixesEveryComplexRightRay A) :
    ∃ eta : ℂ, Complex.normSq eta = 1 ∧
      A = eta • (1 : Matrix I I ℂ) := by
  classical
  let i0 : I := Classical.choice inferInstance
  let eta : I → ℂ := fun x ↦ (hA (Pi.single x 1)).choose
  have heta (x : I) : Complex.normSq (eta x) = 1 :=
    (hA (Pi.single x 1)).choose_spec.1
  have hcol (x : I) :
      A *ᵥ Pi.single x (1 : ℂ) =
        fun i ↦ (Pi.single x (1 : ℂ) : I → ℂ) i * eta x :=
    (hA (Pi.single x 1)).choose_spec.2
  have hentry (y x : I) : A y x = if y = x then eta x else 0 := by
    have h := congrFun (hcol x) y
    simpa [Pi.single_apply] using h
  have heta_common (x : I) : eta x = eta i0 := by
    by_cases hxi : x = i0
    · simp [hxi]
    · rcases hA (Pi.single i0 1 + Pi.single x 1) with
        ⟨theta, htheta, hsum⟩
      rw [Matrix.mulVec_add, hcol i0, hcol x] at hsum
      have hs0 := congrFun hsum i0
      have hsx := congrFun hsum x
      simp [hxi, Ne.symm hxi] at hs0 hsx
      exact hsx.trans hs0.symm
  refine ⟨eta i0, heta i0, ?_⟩
  funext y x
  rw [hentry, heta_common x]
  by_cases hyx : y = x
  · subst y
    simp
  · simp [hyx]

namespace ComplexRawProjectiveActionEq

/--
On an inhabited finite space, a unitary's raw complex projective kernel is one
global unit phase.  Only `U` needs a unitary certificate.
-/
theorem globalPhaseEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ))
    (h : ComplexRawProjectiveActionEq U V) :
    ComplexGlobalPhaseEq U V := by
  let A : Matrix I I ℂ := V * star U
  have hfix : FixesEveryComplexRightRay A := by
    intro psi
    have hp := Complex.rightPhaseEquivalent_symm (h (star U *ᵥ psi))
    simpa only [A, Matrix.mulVec_mulVec,
      Unitary.mul_star_self_of_mem hU, Matrix.one_mulVec] using hp
  rcases fixesEveryComplexRightRay_globalPhase A hfix with
    ⟨eta, heta, hA⟩
  refine ⟨eta, heta, ?_⟩
  have hmul := congrArg (fun M : Matrix I I ℂ ↦ M * U) hA
  simpa only [A, Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] using hmul

end ComplexRawProjectiveActionEq

namespace RealProjectiveActionEq

/-- Normalized real projective action has exactly the global-sign kernel. -/
theorem globalSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℝ}
    (hU : U ∈ unitary (Matrix I I ℝ))
    (h : RealProjectiveActionEq U V) : RealGlobalSignEq U V :=
  h.rawProjectiveActionEq.globalSignEq_of_unitary hU

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

/-- Normalized complex projective action has exactly the global-phase kernel. -/
theorem globalPhaseEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ))
    (h : ComplexProjectiveActionEq U V) : ComplexGlobalPhaseEq U V :=
  h.rawProjectiveActionEq.globalPhaseEq_of_unitary hU

end ComplexProjectiveActionEq

/-! ## Global phase and physical channels -/

namespace RealGlobalSignEq

/-- A real global sign cancels from unitary conjugation. -/
theorem channelEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I}
    (h : RealGlobalSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ)) :
    ChannelEq U V := by
  intro rho
  apply DensityMatrix.ext_matrix
  rcases h with ⟨s, hs, hV⟩
  simp only [UnitaryOperator.evolve_coe, hV, Matrix.conjTranspose_smul,
    star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
    one_smul]

end RealGlobalSignEq

namespace ComplexGlobalPhaseEq

/-- A complex global unit phase cancels from unitary conjugation. -/
theorem channelEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I}
    (h : ComplexGlobalPhaseEq
      (U : Matrix I I ℂ) (V : Matrix I I ℂ)) :
    ChannelEq U V := by
  intro rho
  apply DensityMatrix.ext_matrix
  rcases h with ⟨eta, heta, hV⟩
  have heta' : star eta * eta = 1 := by
    change (starRingEnd ℂ) eta * eta = 1
    rw [mul_comm, Complex.mul_conj, heta]
    norm_num
  simp only [UnitaryOperator.evolve_coe, hV, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, heta', one_smul]

end ComplexGlobalPhaseEq

namespace ChannelEq

/-- Equal real unitary channels have equal projective action on normalized kets. -/
theorem realProjectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : ChannelEq U V) :
    RealProjectiveActionEq
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) := by
  intro psi
  have hpsi :
      star (psi : I → ℝ) ⬝ᵥ (psi : I → ℝ) = 1 := by
    simpa [State.realTotalWeight, State.totalWeight, State.basisWeight,
      State.realWeight, dotProduct] using psi.property
  have hUpsi :
      star ((U : Matrix I I ℝ) *ᵥ (psi : I → ℝ)) ⬝ᵥ
        ((U : Matrix I I ℝ) *ᵥ (psi : I → ℝ)) = 1 :=
    (State.star_dotProduct_mulVec_of_mem_unitary U.mem_unitary
      (psi : I → ℝ)).trans hpsi
  apply realSignEquivalent_of_normalized_pureMatrix_eq hUpsi
  have hevolve := h (RealDensityMatrix.ofState psi)
  have hmat := congrArg
    (fun rho : RealDensityMatrix I ↦ (rho : Matrix I I ℝ)) hevolve
  simpa only [UnitaryOperator.evolve, RealDensityMatrix.ofState,
    DensityMatrix.unitaryConjugate_pure_coe] using hmat

/-- Equal complex unitary channels have equal projective action on normalized kets. -/
theorem complexProjectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : ChannelEq U V) :
    ComplexProjectiveActionEq
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) := by
  intro psi
  have hpsi :
      star (psi : I → ℂ) ⬝ᵥ (psi : I → ℂ) = 1 := by
    have hp := congrArg (fun r : ℝ ↦ (r : ℂ)) psi.property
    simpa [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, dotProduct,
      ← Complex.normSq_eq_conj_mul_self] using hp
  have hUpsi :
      star ((U : Matrix I I ℂ) *ᵥ (psi : I → ℂ)) ⬝ᵥ
        ((U : Matrix I I ℂ) *ᵥ (psi : I → ℂ)) = 1 :=
    (State.star_dotProduct_mulVec_of_mem_unitary U.mem_unitary
      (psi : I → ℂ)).trans hpsi
  apply complexRightPhaseEquivalent_of_normalized_pureMatrix_eq hUpsi
  have hevolve := h (ComplexDensityMatrix.ofState psi)
  have hmat := congrArg
    (fun rho : ComplexDensityMatrix I ↦ (rho : Matrix I I ℂ)) hevolve
  simpa only [UnitaryOperator.evolve, ComplexDensityMatrix.ofState,
    DensityMatrix.unitaryConjugate_pure_coe] using hmat

/-- Equal real unitary channels agree projectively on every raw column. -/
theorem realRawProjectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : RealUnitaryOperator I} (h : ChannelEq U V) :
    RealRawProjectiveActionEq
      (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  h.realProjectiveActionEq.rawProjectiveActionEq

/-- Equal complex unitary channels agree projectively on every raw column. -/
theorem complexRawProjectiveActionEq
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : ComplexUnitaryOperator I} (h : ChannelEq U V) :
    ComplexRawProjectiveActionEq
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  h.complexProjectiveActionEq.rawProjectiveActionEq

end ChannelEq

/-! ## Exact inhabited-space characterizations -/

/-- On an inhabited finite space, real global-sign equality is exactly channel equality. -/
theorem realGlobalSignEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : RealUnitaryOperator I) :
    RealGlobalSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔
      ChannelEq U V :=
  ⟨RealGlobalSignEq.channelEq,
    fun h ↦ h.realProjectiveActionEq.globalSignEq_of_unitary
      U.mem_unitary⟩

/-- On an inhabited finite space, complex global-phase equality is exactly channel equality. -/
theorem complexGlobalPhaseEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : ComplexUnitaryOperator I) :
    ComplexGlobalPhaseEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔
      ChannelEq U V :=
  ⟨ComplexGlobalPhaseEq.channelEq,
    fun h ↦ h.complexProjectiveActionEq.globalPhaseEq_of_unitary
      U.mem_unitary⟩

/-- On an inhabited finite space, normalized real projective action is exactly channel equality. -/
theorem realProjectiveActionEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : RealUnitaryOperator I) :
    RealProjectiveActionEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔
      ChannelEq U V :=
  ⟨fun h ↦ (h.globalSignEq_of_unitary U.mem_unitary).channelEq,
    ChannelEq.realProjectiveActionEq⟩

/--
On an inhabited finite space, normalized complex projective action is exactly
channel equality.
-/
theorem complexProjectiveActionEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : ComplexUnitaryOperator I) :
    ComplexProjectiveActionEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔
      ChannelEq U V :=
  ⟨fun h ↦ (h.globalPhaseEq_of_unitary U.mem_unitary).channelEq,
    ChannelEq.complexProjectiveActionEq⟩

/-- On an inhabited finite space, raw real projective action is exactly channel equality. -/
theorem realRawProjectiveActionEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : RealUnitaryOperator I) :
    RealRawProjectiveActionEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔
      ChannelEq U V :=
  ⟨fun h ↦ (h.globalSignEq_of_unitary U.mem_unitary).channelEq,
    ChannelEq.realRawProjectiveActionEq⟩

/-- On an inhabited finite space, raw complex projective action is exactly channel equality. -/
theorem complexRawProjectiveActionEq_iff_channelEq
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : ComplexUnitaryOperator I) :
    ComplexRawProjectiveActionEq
      (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔ ChannelEq U V :=
  ⟨fun h ↦ (h.globalPhaseEq_of_unitary U.mem_unitary).channelEq,
    ChannelEq.complexRawProjectiveActionEq⟩

/-! ## Empty-index boundary -/

/-- Real square matrices on an empty type are exactly equal and hence globally sign equivalent. -/
theorem realGlobalSignEq_of_isEmpty
    {I : Type u} [Fintype I] [DecidableEq I] [IsEmpty I]
    (U V : RealUnitaryOperator I) :
    RealGlobalSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) :=
  RealGlobalSignEq.of_exact (Subsingleton.elim _ _)

/--
Complex square matrices on an empty type are exactly equal and hence globally
phase equivalent.
-/
theorem complexGlobalPhaseEq_of_isEmpty
    {I : Type u} [Fintype I] [DecidableEq I] [IsEmpty I]
    (U V : ComplexUnitaryOperator I) :
    ComplexGlobalPhaseEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) :=
  ComplexGlobalPhaseEq.of_exact (Subsingleton.elim _ _)

end QuaternionicComputing.Semantics
