module

public import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal

/-!
# Real and complex circuit phase semantics

This leaf owns composition laws and chronological-circuit wrappers for the
real and complex operator-phase relations. Input-basis phase is stable under a
common later evolution, while output-basis phase is stable under a common
earlier evolution. Projective action is stable under a common later evolution
without further assumptions; a common earlier evolution must be unitary so
that normalized inputs remain normalized.

All circuit relations compare `Circuit.OrderedCircuit.eval`. They say nothing
about gate-list equality, schedules, resources, scalar embeddings, or
quaternionic phase.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe u v w

/-! ## Sided matrix-composition laws -/

namespace RealGlobalSignEq

/-- Global real sign is compatible with multiplication of related operators. -/
theorem mul {O : Type u} {M : Type v} {I : Type w} [Fintype M]
    {A B : Matrix O M ℝ} {C D : Matrix M I ℝ}
    (hAB : RealGlobalSignEq A B) (hCD : RealGlobalSignEq C D) :
    RealGlobalSignEq (A * C) (B * D) := by
  rcases hAB with ⟨s, hs, hB⟩
  rcases hCD with ⟨t, ht, hD⟩
  refine ⟨s * t, ?_, ?_⟩
  · calc
      (s * t) * (s * t) = (s * s) * (t * t) := by ring
      _ = 1 := by rw [hs, ht, one_mul]
  · rw [hB, hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end RealGlobalSignEq

namespace ComplexGlobalPhaseEq

/-- One complex global phase is compatible with multiplication of related operators. -/
theorem mul {O : Type u} {M : Type v} {I : Type w} [Fintype M]
    {A B : Matrix O M ℂ} {C D : Matrix M I ℂ}
    (hAB : ComplexGlobalPhaseEq A B) (hCD : ComplexGlobalPhaseEq C D) :
    ComplexGlobalPhaseEq (A * C) (B * D) := by
  rcases hAB with ⟨eta, heta, hB⟩
  rcases hCD with ⟨theta, htheta, hD⟩
  refine ⟨eta * theta, ?_, ?_⟩
  · rw [Complex.normSq_mul, heta, htheta, one_mul]
  · rw [hB, hD, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end ComplexGlobalPhaseEq

namespace RealInputBasisSignEq

/-- A common later real evolution preserves input-column signs. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w} [Fintype O]
    (A : Matrix P O ℝ) {U V : Matrix O I ℝ}
    (h : RealInputBasisSignEq U V) :
    RealInputBasisSignEq (A * U) (A * V) := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨s, hs, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV z x, ← mul_assoc]

end RealInputBasisSignEq

namespace ComplexInputBasisPhaseEq

/-- A common later complex evolution preserves input-column phases. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w} [Fintype O]
    (A : Matrix P O ℂ) {U V : Matrix O I ℂ}
    (h : ComplexInputBasisPhaseEq U V) :
    ComplexInputBasisPhaseEq (A * U) (A * V) := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨eta, heta, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV z x, ← mul_assoc]

end ComplexInputBasisPhaseEq

namespace RealOutputBasisSignEq

/-- A common earlier real evolution preserves output-row signs. -/
theorem mul_right {O : Type u} {I : Type v} {K : Type w} [Fintype I]
    {U V : Matrix O I ℝ} (B : Matrix I K ℝ)
    (h : RealOutputBasisSignEq U V) :
    RealOutputBasisSignEq (U * B) (V * B) := by
  rcases h with ⟨s, hs, hV⟩
  refine ⟨s, hs, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV y z, mul_assoc]

end RealOutputBasisSignEq

namespace ComplexOutputBasisPhaseEq

/-- A common earlier complex evolution preserves output-row phases. -/
theorem mul_right {O : Type u} {I : Type v} {K : Type w} [Fintype I]
    {U V : Matrix O I ℂ} (B : Matrix I K ℂ)
    (h : ComplexOutputBasisPhaseEq U V) :
    ComplexOutputBasisPhaseEq (U * B) (V * B) := by
  rcases h with ⟨eta, heta, hV⟩
  refine ⟨eta, heta, ?_⟩
  intro y x
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [hV y z, mul_assoc]

end ComplexOutputBasisPhaseEq

namespace RealProjectiveActionEq

/-- A common later real-linear evolution preserves projective action equality. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w}
    [Fintype O] [Fintype I] (A : Matrix P O ℝ)
    {U V : Matrix O I ℝ} (h : RealProjectiveActionEq U V) :
    RealProjectiveActionEq (A * U) (A * V) := by
  intro psi
  simpa only [← Matrix.mulVec_mulVec] using
    State.signEquivalent_real_mulVec A (h psi)

/--
A common earlier real evolution preserves projective action equality when it
is unitary, so every normalized input remains in the quantified input domain.
-/
theorem mul_right_unitary {O : Type u} {I : Type v}
    [Fintype I] [DecidableEq I] {U V : Matrix O I ℝ}
    (P : Matrix I I ℝ) (hP : P ∈ unitary (Matrix I I ℝ))
    (h : RealProjectiveActionEq U V) :
    RealProjectiveActionEq (U * P) (V * P) := by
  intro psi
  have hp := h (State.RealState.evolveUnitary psi P hP)
  change Real.SignEquivalent
    (U *ᵥ (P *ᵥ (psi : I → ℝ)))
    (V *ᵥ (P *ᵥ (psi : I → ℝ))) at hp
  simpa only [← Matrix.mulVec_mulVec] using hp

end RealProjectiveActionEq

namespace ComplexProjectiveActionEq

/-- A common later complex-linear evolution preserves projective action equality. -/
theorem mul_left {P : Type u} {O : Type v} {I : Type w}
    [Fintype O] [Fintype I] (A : Matrix P O ℂ)
    {U V : Matrix O I ℂ} (h : ComplexProjectiveActionEq U V) :
    ComplexProjectiveActionEq (A * U) (A * V) := by
  intro psi
  simpa only [← Matrix.mulVec_mulVec] using
    State.rightPhaseEquivalent_complex_mulVec A (h psi)

/--
A common earlier complex evolution preserves projective action equality when
it is unitary, so every normalized input remains in the quantified input
domain.
-/
theorem mul_right_unitary {O : Type u} {I : Type v}
    [Fintype I] [DecidableEq I] {U V : Matrix O I ℂ}
    (P : Matrix I I ℂ) (hP : P ∈ unitary (Matrix I I ℂ))
    (h : ComplexProjectiveActionEq U V) :
    ComplexProjectiveActionEq (U * P) (V * P) := by
  intro psi
  have hp := h (State.ComplexState.evolveUnitary psi P hP)
  change Complex.RightPhaseEquivalent
    (U *ᵥ (P *ᵥ (psi : I → ℂ)))
    (V *ᵥ (P *ᵥ (psi : I → ℂ))) at hp
  simpa only [← Matrix.mulVec_mulVec] using hp

end ComplexProjectiveActionEq

/-! ## Chronological-circuit relation wrappers -/

/-- Real chronological circuits whose evaluated operators differ by one sign. -/
def RealCircuitGlobalSignEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℝ W) : Prop :=
  RealGlobalSignEq C.eval D.eval

/-- Complex chronological circuits whose evaluated operators differ by one phase. -/
def ComplexCircuitGlobalPhaseEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℂ W) : Prop :=
  ComplexGlobalPhaseEq C.eval D.eval

/-- Real chronological circuits with one sign per evaluated input column. -/
def RealCircuitInputBasisSignEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℝ W) : Prop :=
  RealInputBasisSignEq C.eval D.eval

/-- Complex chronological circuits with one phase per evaluated input column. -/
def ComplexCircuitInputBasisPhaseEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℂ W) : Prop :=
  ComplexInputBasisPhaseEq C.eval D.eval

/-- Real chronological circuits with one sign per evaluated output row. -/
def RealCircuitOutputBasisSignEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℝ W) : Prop :=
  RealOutputBasisSignEq C.eval D.eval

/-- Complex chronological circuits with one phase per evaluated output row. -/
def ComplexCircuitOutputBasisPhaseEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℂ W) : Prop :=
  ComplexOutputBasisPhaseEq C.eval D.eval

/-- Real chronological circuits with equal projective action on every pure input. -/
def RealCircuitProjectiveActionEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℝ W) : Prop :=
  RealProjectiveActionEq C.eval D.eval

/-- Complex chronological circuits with equal projective action on every pure input. -/
def ComplexCircuitProjectiveActionEq {W : Type u} [Fintype W]
    (C D : Circuit.OrderedCircuit ℂ W) : Prop :=
  ComplexProjectiveActionEq C.eval D.eval

/-! ## Circuit equivalence laws and evaluator projections -/

namespace RealCircuitGlobalSignEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℝ W}

@[simp]
theorem iff_eval : RealCircuitGlobalSignEq C D ↔ RealGlobalSignEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : RealCircuitGlobalSignEq C D) :
    RealGlobalSignEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℝ W) :
    RealCircuitGlobalSignEq C C :=
  RealGlobalSignEq.refl _

@[symm] theorem symm (h : RealCircuitGlobalSignEq C D) :
    RealCircuitGlobalSignEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : RealCircuitGlobalSignEq C D)
    (hDE : RealCircuitGlobalSignEq D E) : RealCircuitGlobalSignEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@RealCircuitGlobalSignEq W _) :=
  ⟨refl, symm, trans⟩

end RealCircuitGlobalSignEq

namespace ComplexCircuitGlobalPhaseEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℂ W}

@[simp]
theorem iff_eval :
    ComplexCircuitGlobalPhaseEq C D ↔ ComplexGlobalPhaseEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : ComplexCircuitGlobalPhaseEq C D) :
    ComplexGlobalPhaseEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℂ W) :
    ComplexCircuitGlobalPhaseEq C C :=
  ComplexGlobalPhaseEq.refl _

@[symm] theorem symm (h : ComplexCircuitGlobalPhaseEq C D) :
    ComplexCircuitGlobalPhaseEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : ComplexCircuitGlobalPhaseEq C D)
    (hDE : ComplexCircuitGlobalPhaseEq D E) : ComplexCircuitGlobalPhaseEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@ComplexCircuitGlobalPhaseEq W _) :=
  ⟨refl, symm, trans⟩

end ComplexCircuitGlobalPhaseEq

namespace RealCircuitInputBasisSignEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℝ W}

@[simp]
theorem iff_eval :
    RealCircuitInputBasisSignEq C D ↔ RealInputBasisSignEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : RealCircuitInputBasisSignEq C D) :
    RealInputBasisSignEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℝ W) :
    RealCircuitInputBasisSignEq C C :=
  RealInputBasisSignEq.refl _

@[symm] theorem symm (h : RealCircuitInputBasisSignEq C D) :
    RealCircuitInputBasisSignEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : RealCircuitInputBasisSignEq C D)
    (hDE : RealCircuitInputBasisSignEq D E) : RealCircuitInputBasisSignEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@RealCircuitInputBasisSignEq W _) :=
  ⟨refl, symm, trans⟩

end RealCircuitInputBasisSignEq

namespace ComplexCircuitInputBasisPhaseEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℂ W}

@[simp]
theorem iff_eval :
    ComplexCircuitInputBasisPhaseEq C D ↔
      ComplexInputBasisPhaseEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : ComplexCircuitInputBasisPhaseEq C D) :
    ComplexInputBasisPhaseEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℂ W) :
    ComplexCircuitInputBasisPhaseEq C C :=
  ComplexInputBasisPhaseEq.refl _

@[symm] theorem symm (h : ComplexCircuitInputBasisPhaseEq C D) :
    ComplexCircuitInputBasisPhaseEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : ComplexCircuitInputBasisPhaseEq C D)
    (hDE : ComplexCircuitInputBasisPhaseEq D E) :
    ComplexCircuitInputBasisPhaseEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@ComplexCircuitInputBasisPhaseEq W _) :=
  ⟨refl, symm, trans⟩

end ComplexCircuitInputBasisPhaseEq

namespace RealCircuitOutputBasisSignEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℝ W}

@[simp]
theorem iff_eval :
    RealCircuitOutputBasisSignEq C D ↔ RealOutputBasisSignEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : RealCircuitOutputBasisSignEq C D) :
    RealOutputBasisSignEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℝ W) :
    RealCircuitOutputBasisSignEq C C :=
  RealOutputBasisSignEq.refl _

@[symm] theorem symm (h : RealCircuitOutputBasisSignEq C D) :
    RealCircuitOutputBasisSignEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : RealCircuitOutputBasisSignEq C D)
    (hDE : RealCircuitOutputBasisSignEq D E) :
    RealCircuitOutputBasisSignEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@RealCircuitOutputBasisSignEq W _) :=
  ⟨refl, symm, trans⟩

end RealCircuitOutputBasisSignEq

namespace ComplexCircuitOutputBasisPhaseEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℂ W}

@[simp]
theorem iff_eval :
    ComplexCircuitOutputBasisPhaseEq C D ↔
      ComplexOutputBasisPhaseEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : ComplexCircuitOutputBasisPhaseEq C D) :
    ComplexOutputBasisPhaseEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℂ W) :
    ComplexCircuitOutputBasisPhaseEq C C :=
  ComplexOutputBasisPhaseEq.refl _

@[symm] theorem symm (h : ComplexCircuitOutputBasisPhaseEq C D) :
    ComplexCircuitOutputBasisPhaseEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : ComplexCircuitOutputBasisPhaseEq C D)
    (hDE : ComplexCircuitOutputBasisPhaseEq D E) :
    ComplexCircuitOutputBasisPhaseEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@ComplexCircuitOutputBasisPhaseEq W _) :=
  ⟨refl, symm, trans⟩

end ComplexCircuitOutputBasisPhaseEq

namespace RealCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℝ W}

@[simp]
theorem iff_eval :
    RealCircuitProjectiveActionEq C D ↔ RealProjectiveActionEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : RealCircuitProjectiveActionEq C D) :
    RealProjectiveActionEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℝ W) :
    RealCircuitProjectiveActionEq C C :=
  RealProjectiveActionEq.refl _

@[symm] theorem symm (h : RealCircuitProjectiveActionEq C D) :
    RealCircuitProjectiveActionEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : RealCircuitProjectiveActionEq C D)
    (hDE : RealCircuitProjectiveActionEq D E) :
    RealCircuitProjectiveActionEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@RealCircuitProjectiveActionEq W _) :=
  ⟨refl, symm, trans⟩

end RealCircuitProjectiveActionEq

namespace ComplexCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]
variable {C D E : Circuit.OrderedCircuit ℂ W}

@[simp]
theorem iff_eval :
    ComplexCircuitProjectiveActionEq C D ↔
      ComplexProjectiveActionEq C.eval D.eval :=
  Iff.rfl

theorem eval (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexProjectiveActionEq C.eval D.eval :=
  h

@[refl] theorem refl (C : Circuit.OrderedCircuit ℂ W) :
    ComplexCircuitProjectiveActionEq C C :=
  ComplexProjectiveActionEq.refl _

@[symm] theorem symm (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexCircuitProjectiveActionEq D C :=
  h.eval.symm

@[trans] theorem trans (hCD : ComplexCircuitProjectiveActionEq C D)
    (hDE : ComplexCircuitProjectiveActionEq D E) :
    ComplexCircuitProjectiveActionEq C E :=
  hCD.eval.trans hDE.eval

theorem equivalence : Equivalence (@ComplexCircuitProjectiveActionEq W _) :=
  ⟨refl, symm, trans⟩

end ComplexCircuitProjectiveActionEq

/-! ## Exact-circuit lifts -/

namespace ExactCircuitEq

variable {W : Type u} [Fintype W]

/-- Exact real circuit equality implies equality up to one global sign. -/
theorem realGlobalSignEq {C D : Circuit.OrderedCircuit ℝ W}
    (h : ExactCircuitEq C D) : RealCircuitGlobalSignEq C D :=
  RealGlobalSignEq.of_exact h

/-- Exact complex circuit equality implies equality up to one global phase. -/
theorem complexGlobalPhaseEq {C D : Circuit.OrderedCircuit ℂ W}
    (h : ExactCircuitEq C D) : ComplexCircuitGlobalPhaseEq C D :=
  ComplexGlobalPhaseEq.of_exact h

end ExactCircuitEq

/-! ## Chronological composition congruences -/

namespace RealCircuitGlobalSignEq

variable {W : Type u} [Fintype W]

/-- Appending two related early/later real circuit pairs multiplies their signs. -/
theorem append {C1 C2 D1 D2 : Circuit.OrderedCircuit ℝ W}
    (h1 : RealCircuitGlobalSignEq C1 D1)
    (h2 : RealCircuitGlobalSignEq C2 D2) :
    RealCircuitGlobalSignEq (C1 ++ C2) (D1 ++ D2) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact RealGlobalSignEq.mul h2.eval h1.eval

/-- A common later real circuit preserves one global sign. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℝ W)
    {C D : Circuit.OrderedCircuit ℝ W} (h : RealCircuitGlobalSignEq C D) :
    RealCircuitGlobalSignEq (C ++ L) (D ++ L) :=
  append h (refl L)

/-- A common earlier real circuit preserves one global sign. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℝ W)
    {C D : Circuit.OrderedCircuit ℝ W} (h : RealCircuitGlobalSignEq C D) :
    RealCircuitGlobalSignEq (E ++ C) (E ++ D) :=
  append (refl E) h

end RealCircuitGlobalSignEq

namespace ComplexCircuitGlobalPhaseEq

variable {W : Type u} [Fintype W]

/-- Appending two related early/later complex circuit pairs multiplies phases. -/
theorem append {C1 C2 D1 D2 : Circuit.OrderedCircuit ℂ W}
    (h1 : ComplexCircuitGlobalPhaseEq C1 D1)
    (h2 : ComplexCircuitGlobalPhaseEq C2 D2) :
    ComplexCircuitGlobalPhaseEq (C1 ++ C2) (D1 ++ D2) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact ComplexGlobalPhaseEq.mul h2.eval h1.eval

/-- A common later complex circuit preserves one global phase. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℂ W)
    {C D : Circuit.OrderedCircuit ℂ W} (h : ComplexCircuitGlobalPhaseEq C D) :
    ComplexCircuitGlobalPhaseEq (C ++ L) (D ++ L) :=
  append h (refl L)

/-- A common earlier complex circuit preserves one global phase. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℂ W)
    {C D : Circuit.OrderedCircuit ℂ W} (h : ComplexCircuitGlobalPhaseEq C D) :
    ComplexCircuitGlobalPhaseEq (E ++ C) (E ++ D) :=
  append (refl E) h

end ComplexCircuitGlobalPhaseEq

namespace RealCircuitInputBasisSignEq

variable {W : Type u} [Fintype W]

/-- A common later real circuit preserves input-column signs. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℝ W)
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitInputBasisSignEq C D) :
    RealCircuitInputBasisSignEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact RealInputBasisSignEq.mul_left L.eval h.eval

end RealCircuitInputBasisSignEq

namespace ComplexCircuitInputBasisPhaseEq

variable {W : Type u} [Fintype W]

/-- A common later complex circuit preserves input-column phases. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℂ W)
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitInputBasisPhaseEq C D) :
    ComplexCircuitInputBasisPhaseEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact ComplexInputBasisPhaseEq.mul_left L.eval h.eval

end ComplexCircuitInputBasisPhaseEq

namespace RealCircuitOutputBasisSignEq

variable {W : Type u} [Fintype W]

/-- A common earlier real circuit preserves output-row signs. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℝ W)
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitOutputBasisSignEq C D) :
    RealCircuitOutputBasisSignEq (E ++ C) (E ++ D) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact RealOutputBasisSignEq.mul_right E.eval h.eval

end RealCircuitOutputBasisSignEq

namespace ComplexCircuitOutputBasisPhaseEq

variable {W : Type u} [Fintype W]

/-- A common earlier complex circuit preserves output-row phases. -/
theorem prepend_same_earlier (E : Circuit.OrderedCircuit ℂ W)
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitOutputBasisPhaseEq C D) :
    ComplexCircuitOutputBasisPhaseEq (E ++ C) (E ++ D) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact ComplexOutputBasisPhaseEq.mul_right E.eval h.eval

end ComplexCircuitOutputBasisPhaseEq

namespace RealCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]

/-- A common later real circuit preserves projective action equality. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℝ W)
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitProjectiveActionEq C D) :
    RealCircuitProjectiveActionEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact RealProjectiveActionEq.mul_left L.eval h.eval

/--
A common earlier real circuit preserves projective action equality when every
gate in that earlier circuit is locally unitary.
-/
theorem prepend_same_earlier_of_isLocallyUnitary
    (E : Circuit.OrderedCircuit ℝ W) (hE : E.IsLocallyUnitary)
    {C D : Circuit.OrderedCircuit ℝ W}
    (h : RealCircuitProjectiveActionEq C D) :
    RealCircuitProjectiveActionEq (E ++ C) (E ++ D) := by
  classical
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact RealProjectiveActionEq.mul_right_unitary E.eval
    (E.eval_mem_unitary hE) h.eval

end RealCircuitProjectiveActionEq

namespace ComplexCircuitProjectiveActionEq

variable {W : Type u} [Fintype W]

/-- A common later complex circuit preserves projective action equality. -/
theorem append_same_later (L : Circuit.OrderedCircuit ℂ W)
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexCircuitProjectiveActionEq (C ++ L) (D ++ L) := by
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact ComplexProjectiveActionEq.mul_left L.eval h.eval

/--
A common earlier complex circuit preserves projective action equality when
every gate in that earlier circuit is locally unitary.
-/
theorem prepend_same_earlier_of_isLocallyUnitary
    (E : Circuit.OrderedCircuit ℂ W) (hE : E.IsLocallyUnitary)
    {C D : Circuit.OrderedCircuit ℂ W}
    (h : ComplexCircuitProjectiveActionEq C D) :
    ComplexCircuitProjectiveActionEq (E ++ C) (E ++ D) := by
  classical
  simp only [iff_eval, Circuit.OrderedCircuit.eval_append]
  exact ComplexProjectiveActionEq.mul_right_unitary E.eval
    (E.eval_mem_unitary hE) h.eval

end ComplexCircuitProjectiveActionEq

end QuaternionicComputing.Semantics
