module

public import QuaternionicComputing.Circuit.Basic

/-!
# Exact semantic equality

This leaf names literal matrix equality and equality of chronological circuit
evaluations. `ExactCircuitEq` deliberately goes through
`Circuit.OrderedCircuit.eval`; it neither compares gate lists nor records
resource equality. Cross-model embeddings and equality up to phase live in
separate semantic leaves.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Semantics

universe u v w x

/-- Exact equality of two matrices with the same input and output spaces. -/
def ExactOperatorEq {R : Type u} {O : Type v} {I : Type w}
    (U V : Matrix O I R) : Prop :=
  U = V

namespace ExactOperatorEq

variable {R : Type u} {O : Type v} {I : Type w}
variable {U V T : Matrix O I R}

@[refl]
theorem refl (U : Matrix O I R) : ExactOperatorEq U U :=
  rfl

@[symm]
theorem symm (h : ExactOperatorEq U V) : ExactOperatorEq V U :=
  Eq.symm h

@[trans]
theorem trans (hUV : ExactOperatorEq U V) (hVT : ExactOperatorEq V T) :
    ExactOperatorEq U T :=
  Eq.trans hUV hVT

/-- Exact matrix equality is an equivalence relation on each fixed matrix type. -/
theorem equivalence : Equivalence (@ExactOperatorEq R O I) :=
  ⟨refl, symm, trans⟩

@[simp]
theorem iff_eq : ExactOperatorEq U V ↔ U = V :=
  Iff.rfl

theorem of_eq (h : U = V) : ExactOperatorEq U V :=
  h

theorem eq (h : ExactOperatorEq U V) : U = V :=
  h

/-- Exact equality is respected by compatible matrix multiplication. -/
theorem mul {M : Type x} [Fintype M] [NonUnitalNonAssocSemiring R]
    {A B : Matrix O M R} {C D : Matrix M I R}
    (hAB : ExactOperatorEq A B) (hCD : ExactOperatorEq C D) :
    ExactOperatorEq (A * C) (B * D) := by
  subst B
  subst D
  rfl

end ExactOperatorEq

/--
Exact equality of ordered circuits means equality of their chronological
evaluations, not equality of their gate lists.
-/
def ExactCircuitEq {R : Type u} {W : Type v} [Semiring R] [Fintype W]
    (C D : Circuit.OrderedCircuit R W) : Prop :=
  ExactOperatorEq (Circuit.OrderedCircuit.eval C)
    (Circuit.OrderedCircuit.eval D)

namespace ExactCircuitEq

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]
variable {C D E : Circuit.OrderedCircuit R W}

@[refl]
theorem refl (C : Circuit.OrderedCircuit R W) : ExactCircuitEq C C :=
  rfl

@[symm]
theorem symm (h : ExactCircuitEq C D) : ExactCircuitEq D C :=
  Eq.symm h

@[trans]
theorem trans (hCD : ExactCircuitEq C D) (hDE : ExactCircuitEq D E) :
    ExactCircuitEq C E :=
  Eq.trans hCD hDE

/-- Exact evaluated-circuit equality is an equivalence relation. -/
theorem equivalence : Equivalence (@ExactCircuitEq R W _ _) :=
  ⟨refl, symm, trans⟩

@[simp]
theorem iff_eval_eq :
    ExactCircuitEq C D ↔
      Circuit.OrderedCircuit.eval C = Circuit.OrderedCircuit.eval D :=
  Iff.rfl

theorem of_eq (h : C = D) : ExactCircuitEq C D := by
  subst D
  rfl

theorem eval_eq (h : ExactCircuitEq C D) :
    Circuit.OrderedCircuit.eval C = Circuit.OrderedCircuit.eval D :=
  h

/-- Gatewise equality of denotations gives exact circuit equality. -/
theorem of_gatewise
    (h : List.Forall₂ (fun g k ↦ g.denote = k.denote) C D) :
    ExactCircuitEq C D :=
  Circuit.OrderedCircuit.eval_congr h

/-- Appending exactly equal early and late circuits preserves exact equality. -/
theorem append {C₁ C₂ D₁ D₂ : Circuit.OrderedCircuit R W}
    (h₁ : ExactCircuitEq C₁ D₁) (h₂ : ExactCircuitEq C₂ D₂) :
    ExactCircuitEq (C₁ ++ C₂) (D₁ ++ D₂) := by
  simp only [iff_eval_eq, Circuit.OrderedCircuit.eval_append]
  rw [h₁.eval_eq, h₂.eval_eq]

end ExactCircuitEq

end QuaternionicComputing.Semantics
