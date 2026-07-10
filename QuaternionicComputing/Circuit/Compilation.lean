module

public import QuaternionicComputing.Circuit.DescriptionCost

/-!
# Conditional exact compilation into primitive gates

The paper discusses decomposing abstract image gates into an elementary gate
library but supplies neither a library nor a synthesis theorem.  This module
therefore provides a conditional interface: an `ExactGateCompiler` contains
the replacement circuit, its primitive-gate certificate, and exact semantic
correctness for every source gate.

From that supplied data, whole-circuit evaluation is preserved, compiled gate
count is the exact sum of per-gate counts, and a uniform per-gate bound `K`
gives the finite bound `sourceGateCount * K`.  No instance asserting that such
a compiler exists for arbitrary unitaries is introduced here.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

universe u v

variable (R : Type u) (W : Type v) [Semiring R] [Fintype W]

/--
A certified exact replacement of each abstract placed gate by a chronological
circuit over a specified primitive-gate predicate.
-/
structure ExactGateCompiler where
  /-- The target elementary/primitive gate library, as a predicate. -/
  primitive : PlacedGate R W → Prop
  /-- Chronological primitive expansion of one abstract gate. -/
  compileGate : PlacedGate R W → OrderedCircuit R W
  /-- Every gate in an expansion belongs to the supplied primitive library. -/
  compileGate_primitive : ∀ g k, k ∈ compileGate g → primitive k
  /-- Each expansion has exactly the same global denotation as its source gate. -/
  eval_compileGate : ∀ g, OrderedCircuit.eval (compileGate g) = g.denote

namespace ExactGateCompiler

variable {R W}

/-- Compile an entire chronological circuit by concatenating gate expansions in place. -/
def compileCircuit (compiler : ExactGateCompiler R W)
    (c : OrderedCircuit R W) : OrderedCircuit R W :=
  c.flatMap compiler.compileGate

@[simp]
theorem compileCircuit_nil (compiler : ExactGateCompiler R W) :
    compiler.compileCircuit [] = [] :=
  rfl

@[simp]
theorem compileCircuit_cons (compiler : ExactGateCompiler R W)
    (g : PlacedGate R W) (c : OrderedCircuit R W) :
    compiler.compileCircuit (g :: c) =
      compiler.compileGate g ++ compiler.compileCircuit c :=
  rfl

/-- Every gate in the compiled circuit is certified primitive. -/
theorem primitive_of_mem_compileCircuit (compiler : ExactGateCompiler R W)
    {c : OrderedCircuit R W} {k : PlacedGate R W}
    (hk : k ∈ compiler.compileCircuit c) :
    compiler.primitive k := by
  rw [compileCircuit, List.mem_flatMap] at hk
  rcases hk with ⟨g, -, hkg⟩
  exact compiler.compileGate_primitive g k hkg

/-- Exact gatewise compilation preserves the public chronological evaluator. -/
@[simp]
theorem eval_compileCircuit (compiler : ExactGateCompiler R W)
    (c : OrderedCircuit R W) :
    OrderedCircuit.eval (compiler.compileCircuit c) =
      OrderedCircuit.eval c := by
  induction c with
  | nil => simp
  | cons g c ih =>
      simp [compiler.eval_compileGate, ih]

/-- Compiled gate count is the exact sum of the supplied per-gate expansion counts. -/
theorem gateCount_compileCircuit (compiler : ExactGateCompiler R W)
    (c : OrderedCircuit R W) :
    (compiler.compileCircuit c).gateCount =
      OrderedCircuit.translationWork
        (fun g => (compiler.compileGate g).gateCount) c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
      have iht :
          List.length (compiler.compileCircuit c) =
            OrderedCircuit.translationWork
              (fun g => (compiler.compileGate g).gateCount) c := by
        simpa only [OrderedCircuit.gateCount] using ih
      rw [compileCircuit_cons, OrderedCircuit.gateCount, List.length_append,
        iht]
      rfl

/--
If every source occurrence expands to at most `K` primitive gates, total
compiled count is at most source gate count times `K`.
-/
theorem gateCount_compileCircuit_le (compiler : ExactGateCompiler R W)
    (c : OrderedCircuit R W) (K : ℕ)
    (hcount : ∀ g ∈ c, (compiler.compileGate g).gateCount ≤ K) :
    (compiler.compileCircuit c).gateCount ≤ c.gateCount * K := by
  rw [compiler.gateCount_compileCircuit]
  exact OrderedCircuit.translationWork_le_gateCount_mul
    (fun g => (compiler.compileGate g).gateCount) c K hcount

end ExactGateCompiler

end QuaternionicComputing.Circuit
