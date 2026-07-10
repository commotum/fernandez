module

public import QuaternionicComputing.Circuit.Compilation
public import QuaternionicComputing.Simulation.Resources

/-!
# Conditional primitive compilation of exact image circuits

These theorems compose the exact realification and complexification maps with
an independently supplied `ExactGateCompiler` for the target scalar/wire
system.  They prove semantic preservation and finite multiplicative count
bounds from the compiler's explicit per-image-gate premise.

No elementary gate library or generic unitary synthesis algorithm is asserted
to exist.  In particular, these implications do not validate the numerical
decomposition bound claimed in the paper.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit

universe v

/-! ## Complex-to-real followed by a supplied real primitive compiler -/

/-- Exact primitive compilation retains the embedded complex circuit operator. -/
theorem eval_compile_realifyCircuit {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℝ (AddedWire W))
    (c : OrderedCircuit ℂ W) :
    OrderedCircuit.eval (compiler.compileCircuit (realifyCircuit c)) =
      wireRealify (OrderedCircuit.eval c) := by
  rw [compiler.eval_compileCircuit, eval_realifyCircuit]

/-- A supplied bound `K` per real image gate gives compiled count at most `s*K`. -/
theorem gateCount_compile_realifyCircuit_le {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℝ (AddedWire W))
    (c : OrderedCircuit ℂ W) (K : ℕ)
    (hcount : ∀ k ∈ realifyCircuit c,
      (compiler.compileGate k).gateCount ≤ K) :
    (compiler.compileCircuit (realifyCircuit c)).gateCount ≤
      c.gateCount * K := by
  calc
    (compiler.compileCircuit (realifyCircuit c)).gateCount ≤
        (realifyCircuit c).gateCount * K :=
      compiler.gateCount_compileCircuit_le (realifyCircuit c) K hcount
    _ = c.gateCount * K := by rw [gateCount_realifyCircuit]

/-- Canonical serial support layering of the conditionally compiled real image. -/
def compileRealifyCircuitSerialLayering {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℝ (AddedWire W))
    (c : OrderedCircuit ℂ W) :
    SupportLayering (compiler.compileCircuit (realifyCircuit c)) :=
  SupportLayering.serial _

/-- The supplied per-image-gate count bound also bounds canonical serial depth. -/
theorem depth_compileRealifyCircuitSerialLayering_le
    {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℝ (AddedWire W))
    (c : OrderedCircuit ℂ W) (K : ℕ)
    (hcount : ∀ k ∈ realifyCircuit c,
      (compiler.compileGate k).gateCount ≤ K) :
    (compileRealifyCircuitSerialLayering compiler c).depth ≤
      c.gateCount * K := by
  rw [compileRealifyCircuitSerialLayering, SupportLayering.depth_serial]
  exact gateCount_compile_realifyCircuit_le compiler c K hcount

/-! ## Quaternion-to-complex followed by a supplied complex primitive compiler -/

/-- Exact primitive compilation retains the embedded quaternionic circuit operator. -/
theorem eval_compile_complexifyCircuit {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℂ (AddedWire W))
    (c : OrderedCircuit ℍ[ℝ] W) :
    OrderedCircuit.eval (compiler.compileCircuit (complexifyCircuit c)) =
      wireComplexify (OrderedCircuit.eval c) := by
  rw [compiler.eval_compileCircuit, eval_complexifyCircuit]

/-- A supplied bound `K` per complex image gate gives compiled count at most `s*K`. -/
theorem gateCount_compile_complexifyCircuit_le {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℂ (AddedWire W))
    (c : OrderedCircuit ℍ[ℝ] W) (K : ℕ)
    (hcount : ∀ k ∈ complexifyCircuit c,
      (compiler.compileGate k).gateCount ≤ K) :
    (compiler.compileCircuit (complexifyCircuit c)).gateCount ≤
      c.gateCount * K := by
  calc
    (compiler.compileCircuit (complexifyCircuit c)).gateCount ≤
        (complexifyCircuit c).gateCount * K :=
      compiler.gateCount_compileCircuit_le (complexifyCircuit c) K hcount
    _ = c.gateCount * K := by rw [gateCount_complexifyCircuit]

/-- Canonical serial support layering of the conditionally compiled complex image. -/
def compileComplexifyCircuitSerialLayering {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℂ (AddedWire W))
    (c : OrderedCircuit ℍ[ℝ] W) :
    SupportLayering (compiler.compileCircuit (complexifyCircuit c)) :=
  SupportLayering.serial _

/-- The supplied per-image-gate count bound also bounds canonical serial depth. -/
theorem depth_compileComplexifyCircuitSerialLayering_le
    {W : Type v} [Fintype W]
    (compiler : ExactGateCompiler ℂ (AddedWire W))
    (c : OrderedCircuit ℍ[ℝ] W) (K : ℕ)
    (hcount : ∀ k ∈ complexifyCircuit c,
      (compiler.compileGate k).gateCount ≤ K) :
    (compileComplexifyCircuitSerialLayering compiler c).depth ≤
      c.gateCount * K := by
  rw [compileComplexifyCircuitSerialLayering,
    SupportLayering.depth_serial]
  exact gateCount_compile_complexifyCircuit_le compiler c K hcount

end QuaternionicComputing.Simulation
