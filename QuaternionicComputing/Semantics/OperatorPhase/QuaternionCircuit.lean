module

public import QuaternionicComputing.Semantics.OperatorPhase.Quaternion

/-!
# Quaternionic circuit phase semantics

This leaf owns the side-correct composition laws for quaternionic operator
phase and four evaluator-backed chronological-circuit relations.  Input
phases act on the right and are preserved by a common later evolution;
output phases act on the left and are preserved by a common earlier
evolution.  Raw projective action is stable under arbitrary compatible
evolution on either side.  Normalized projective action needs unitarity only
for a common earlier evolution, so that normalized inputs remain normalized.

The circuit predicates compare only `Circuit.OrderedCircuit.eval`.  There is
deliberately no raw-projective circuit wrapper, arbitrary quaternionic global
operator phase, gate-list equality, or resource comparison in this file.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u v w

/-! ## Side-correct matrix-composition laws -/

namespace QuaternionCentralSignEq

/-- Central real sign is compatible with multiplication of related operators. -/
theorem mul {O : Type u} {M : Type v} {I : Type w} [Fintype M]
    {A B : Matrix O M ℍ[ℝ]} {C D : Matrix M I ℍ[ℝ]}
    (hAB : QuaternionCentralSignEq A B)
    (hCD : QuaternionCentralSignEq C D) :
    QuaternionCentralSignEq (A * C) (B * D) := by
  rcases hAB with ⟨s, hs, hB⟩
  rcases hCD with ⟨t, ht, hD⟩
  refine ⟨s * t, ?_, ?_⟩
  · calc
      (s * t) * (s * t) = (s * s) * (t * t) := by ring
      _ = 1 := by rw [hs, ht, one_mul]
  · rw [hB, hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end QuaternionCentralSignEq

namespace QuaternionInputRightPhaseEq

/-- A common later quaternionic evolution preserves input-column right phases. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w} [Fintype O]
    (A : Matrix P O ℍ[ℝ]) {U V : Matrix O I ℍ[ℝ]}
    (h : QuaternionInputRightPhaseEq U V) :
    QuaternionInputRightPhaseEq (A * U) (A * V) := by
  rcases h with ⟨phi, hphi, hV⟩
  refine ⟨phi, hphi, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV z x, ← mul_assoc]

end QuaternionInputRightPhaseEq

namespace QuaternionOutputLeftPhaseEq

/-- A common earlier quaternionic evolution preserves output-row left phases. -/
theorem mul_right {O : Type u} {I : Type v} {K : Type w} [Fintype I]
    {U V : Matrix O I ℍ[ℝ]} (B : Matrix I K ℍ[ℝ])
    (h : QuaternionOutputLeftPhaseEq U V) :
    QuaternionOutputLeftPhaseEq (U * B) (V * B) := by
  rcases h with ⟨theta, htheta, hV⟩
  refine ⟨theta, htheta, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV y z, mul_assoc]

end QuaternionOutputLeftPhaseEq

namespace QuaternionRawProjectiveActionEq

/-- A common later quaternionic evolution preserves raw right-ray action. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w}
    [Fintype O] [Fintype I] (A : Matrix P O ℍ[ℝ])
    {U V : Matrix O I ℍ[ℝ]} (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionRawProjectiveActionEq (A * U) (A * V) := by
  intro psi
  simpa only [← Matrix.mulVec_mulVec] using
    State.rightPhaseEquivalent_mulVec A (h psi)

/-- A common earlier quaternionic evolution preserves raw right-ray action. -/
theorem mul_right {O : Type u} {I : Type v} {K : Type w}
    [Fintype I] [Fintype K] {U V : Matrix O I ℍ[ℝ]}
    (B : Matrix I K ℍ[ℝ]) (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionRawProjectiveActionEq (U * B) (V * B) := by
  intro psi
  have hp := h (B *ᵥ psi)
  simpa only [← Matrix.mulVec_mulVec] using hp

end QuaternionRawProjectiveActionEq

namespace QuaternionProjectiveActionEq

/-- A common later quaternionic evolution preserves normalized-input projective action. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w}
    [Fintype O] [Fintype I] (A : Matrix P O ℍ[ℝ])
    {U V : Matrix O I ℍ[ℝ]} (h : QuaternionProjectiveActionEq U V) :
    QuaternionProjectiveActionEq (A * U) (A * V) := by
  intro psi
  simpa only [← Matrix.mulVec_mulVec] using
    State.rightPhaseEquivalent_mulVec A (h psi)

/-
A common earlier evolution must be unitary: this is exactly what places its
output back in the normalized-input domain quantified by the relation.
-/
/-- A common unitary earlier evolution preserves normalized-input projective action. -/
theorem mul_right_unitary {O : Type u} {I : Type v}
    [Fintype I] [DecidableEq I] {U V : Matrix O I ℍ[ℝ]}
    (P : Matrix I I ℍ[ℝ]) (hP : P ∈ unitary (Matrix I I ℍ[ℝ]))
    (h : QuaternionProjectiveActionEq U V) :
    QuaternionProjectiveActionEq (U * P) (V * P) := by
  intro psi
  have hp := h (State.QuaternionState.evolveUnitary psi P hP)
  change Quaternion.RightPhaseEquivalent
    (U *ᵥ (P *ᵥ (psi : I → ℍ[ℝ])))
    (V *ᵥ (P *ᵥ (psi : I → ℍ[ℝ]))) at hp
  simpa only [← Matrix.mulVec_mulVec] using hp

end QuaternionProjectiveActionEq

/-! ## Evaluator-backed chronological-circuit relations -/

/-- Quaternionic chronological circuits differing by one central real sign. -/
def QuaternionCircuitCentralSignEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W) : Prop :=
  QuaternionCentralSignEq C.eval D.eval

/-- Quaternionic chronological circuits with one right phase per evaluated input column. -/
def QuaternionCircuitInputRightPhaseEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W) : Prop :=
  QuaternionInputRightPhaseEq C.eval D.eval

/-- Quaternionic chronological circuits with one left phase per evaluated output row. -/
def QuaternionCircuitOutputLeftPhaseEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W) : Prop :=
  QuaternionOutputLeftPhaseEq C.eval D.eval

/-- Quaternionic chronological circuits with equal right-ray action on every normalized input. -/
def QuaternionCircuitProjectiveActionEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W) : Prop :=
  QuaternionProjectiveActionEq C.eval D.eval

/-! ## Circuit equivalence laws and evaluator projections -/

namespace QuaternionCircuitCentralSignEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℍ[ℝ] W}

@[simp]
theorem iff_eval :
    QuaternionCircuitCentralSignEq C D ↔
      QuaternionCentralSignEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : QuaternionCircuitCentralSignEq C D) :
    QuaternionCentralSignEq C.eval D.eval :=
  h

@[refl]
theorem refl (C : Circuit.OrderedCircuit ℍ[ℝ] W) :
    QuaternionCircuitCentralSignEq C C :=
  QuaternionCentralSignEq.refl _

@[symm]
theorem symm (h : QuaternionCircuitCentralSignEq C D) :
    QuaternionCircuitCentralSignEq D C :=
  h.eval.symm

@[trans]
theorem trans (hCD : QuaternionCircuitCentralSignEq C D)
    (hDE : QuaternionCircuitCentralSignEq D E) :
    QuaternionCircuitCentralSignEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@QuaternionCircuitCentralSignEq W _) :=
  ⟨refl, symm, trans⟩

end QuaternionCircuitCentralSignEq

namespace QuaternionCircuitInputRightPhaseEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℍ[ℝ] W}

@[simp]
theorem iff_eval :
    QuaternionCircuitInputRightPhaseEq C D ↔
      QuaternionInputRightPhaseEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : QuaternionCircuitInputRightPhaseEq C D) :
    QuaternionInputRightPhaseEq C.eval D.eval :=
  h

@[refl]
theorem refl (C : Circuit.OrderedCircuit ℍ[ℝ] W) :
    QuaternionCircuitInputRightPhaseEq C C :=
  QuaternionInputRightPhaseEq.refl _

@[symm]
theorem symm (h : QuaternionCircuitInputRightPhaseEq C D) :
    QuaternionCircuitInputRightPhaseEq D C :=
  h.eval.symm

@[trans]
theorem trans (hCD : QuaternionCircuitInputRightPhaseEq C D)
    (hDE : QuaternionCircuitInputRightPhaseEq D E) :
    QuaternionCircuitInputRightPhaseEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence :
    Equivalence (@QuaternionCircuitInputRightPhaseEq W _) :=
  ⟨refl, symm, trans⟩

end QuaternionCircuitInputRightPhaseEq

namespace QuaternionCircuitOutputLeftPhaseEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℍ[ℝ] W}

@[simp]
theorem iff_eval :
    QuaternionCircuitOutputLeftPhaseEq C D ↔
      QuaternionOutputLeftPhaseEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : QuaternionCircuitOutputLeftPhaseEq C D) :
    QuaternionOutputLeftPhaseEq C.eval D.eval :=
  h

@[refl]
theorem refl (C : Circuit.OrderedCircuit ℍ[ℝ] W) :
    QuaternionCircuitOutputLeftPhaseEq C C :=
  QuaternionOutputLeftPhaseEq.refl _

@[symm]
theorem symm (h : QuaternionCircuitOutputLeftPhaseEq C D) :
    QuaternionCircuitOutputLeftPhaseEq D C :=
  h.eval.symm

@[trans]
theorem trans (hCD : QuaternionCircuitOutputLeftPhaseEq C D)
    (hDE : QuaternionCircuitOutputLeftPhaseEq D E) :
    QuaternionCircuitOutputLeftPhaseEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence :
    Equivalence (@QuaternionCircuitOutputLeftPhaseEq W _) :=
  ⟨refl, symm, trans⟩

end QuaternionCircuitOutputLeftPhaseEq

namespace QuaternionCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℍ[ℝ] W}

@[simp]
theorem iff_eval :
    QuaternionCircuitProjectiveActionEq C D ↔
      QuaternionProjectiveActionEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : QuaternionCircuitProjectiveActionEq C D) :
    QuaternionProjectiveActionEq C.eval D.eval :=
  h

@[refl]
theorem refl (C : Circuit.OrderedCircuit ℍ[ℝ] W) :
    QuaternionCircuitProjectiveActionEq C C :=
  QuaternionProjectiveActionEq.refl _

@[symm]
theorem symm (h : QuaternionCircuitProjectiveActionEq C D) :
    QuaternionCircuitProjectiveActionEq D C :=
  h.eval.symm

@[trans]
theorem trans (hCD : QuaternionCircuitProjectiveActionEq C D)
    (hDE : QuaternionCircuitProjectiveActionEq D E) :
    QuaternionCircuitProjectiveActionEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence :
    Equivalence (@QuaternionCircuitProjectiveActionEq W _) :=
  ⟨refl, symm, trans⟩

end QuaternionCircuitProjectiveActionEq

/-! ## Exact-circuit lift -/

namespace ExactCircuitEq

variable {W : Type u} [Fintype W]

/-- Exact quaternionic circuit equality implies central-sign equality. -/
theorem quaternionCentralSignEq {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : ExactCircuitEq C D) : QuaternionCircuitCentralSignEq C D :=
  QuaternionCentralSignEq.of_exact h

end ExactCircuitEq

/-! ## Chronological composition congruences -/

namespace QuaternionCircuitCentralSignEq

variable {W : Type u} [Fintype W]

/-- Appending related early/later quaternionic circuit pairs multiplies their central signs. -/
theorem append {C1 C2 D1 D2 : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h1 : QuaternionCircuitCentralSignEq C1 D1)
    (h2 : QuaternionCircuitCentralSignEq C2 D2) :
    QuaternionCircuitCentralSignEq (C1 ++ C2) (D1 ++ D2) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact QuaternionCentralSignEq.mul h2.eval h1.eval

/-- A common later quaternionic circuit preserves one central real sign. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℍ[ℝ] W)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitCentralSignEq C D) :
    QuaternionCircuitCentralSignEq (C ++ L) (D ++ L) :=
  append h (refl L)

/-- A common earlier quaternionic circuit preserves one central real sign. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℍ[ℝ] W)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitCentralSignEq C D) :
    QuaternionCircuitCentralSignEq (E ++ C) (E ++ D) :=
  append (refl E) h

end QuaternionCircuitCentralSignEq

namespace QuaternionCircuitInputRightPhaseEq

variable {W : Type u} [Fintype W]

/-- A common later quaternionic circuit preserves input-column right phases. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℍ[ℝ] W)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitInputRightPhaseEq C D) :
    QuaternionCircuitInputRightPhaseEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact QuaternionInputRightPhaseEq.mul_left L.eval h.eval

end QuaternionCircuitInputRightPhaseEq

namespace QuaternionCircuitOutputLeftPhaseEq

variable {W : Type u} [Fintype W]

/-- A common earlier quaternionic circuit preserves output-row left phases. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℍ[ℝ] W)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitOutputLeftPhaseEq C D) :
    QuaternionCircuitOutputLeftPhaseEq (E ++ C) (E ++ D) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact QuaternionOutputLeftPhaseEq.mul_right E.eval h.eval

end QuaternionCircuitOutputLeftPhaseEq

namespace QuaternionCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]

/-- A common later quaternionic circuit preserves normalized projective action. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℍ[ℝ] W)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitProjectiveActionEq C D) :
    QuaternionCircuitProjectiveActionEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact QuaternionProjectiveActionEq.mul_left L.eval h.eval

/-
Chronological prepend is right matrix multiplication.  Local unitarity of the
common earlier circuit supplies exactly the unitary premise needed by the
normalized operator relation.
-/
/-- A common locally unitary earlier circuit preserves normalized projective action. -/
theorem prepend_same_earlier_of_isLocallyUnitary
    (E : Circuit.OrderedCircuit ℍ[ℝ] W) (hE : E.IsLocallyUnitary)
    {C D : Circuit.OrderedCircuit ℍ[ℝ] W}
    (h : QuaternionCircuitProjectiveActionEq C D) :
    QuaternionCircuitProjectiveActionEq (E ++ C) (E ++ D) := by
  classical
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact QuaternionProjectiveActionEq.mul_right_unitary E.eval
    (E.eval_mem_unitary hE) h.eval

end QuaternionCircuitProjectiveActionEq

end QuaternionicComputing.Semantics
