module

public import QuaternionicComputing.Circuit.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Preparation of known computational-basis inputs

A classically known assignment `b : BitBasis W` can be prepared from the
all-zero assignment by flipping exactly the wires on which `b` is true.  This
file realizes those flips as the permutation `x ↦ x XOR b`, proves that its
permutation matrix is unitary over any compatible star semiring, and packages
it as a full-support `PlacedGate`.

The final theorem respects the chronological convention of `OrderedCircuit`:
prepending the preparation gate makes a circuit acting on the all-zero basis
column agree with the original circuit acting on the known basis column.

This construction is deliberately limited to a *classically known
computational-basis assignment*.  It does not prepare an unknown quantum
state, provide a uniform runtime compiler, or establish a general
"without loss of generality" principle for arbitrary inputs.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Circuit

universe u v

/-- The computational-basis assignment in which every wire is zero. -/
def groundBasis (W : Type*) : BitBasis W :=
  fun _ ↦ false

@[simp]
theorem groundBasis_apply (W : Type*) (w : W) :
    groundBasis W w = false :=
  rfl

section Xor

variable {W : Type v}

/--
XOR with a fixed basis assignment, viewed as a permutation of all basis
assignments.  Its inverse is the same XOR operation.
-/
def xorBasisEquiv (b : BitBasis W) : BitBasis W ≃ BitBasis W where
  toFun x w := xor (x w) (b w)
  invFun x w := xor (x w) (b w)
  left_inv x := by
    funext w
    simp
  right_inv x := by
    funext w
    simp

@[simp]
theorem xorBasisEquiv_apply (b x : BitBasis W) (w : W) :
    xorBasisEquiv b x w = xor (x w) (b w) :=
  rfl

@[simp]
theorem xorBasisEquiv_symm (b : BitBasis W) :
    (xorBasisEquiv b).symm = xorBasisEquiv b := by
  apply Equiv.ext
  intro x
  rfl

@[simp]
theorem xorBasisEquiv_ground (b : BitBasis W) :
    xorBasisEquiv b (groundBasis W) = b := by
  funext w
  simp

@[simp]
theorem xorBasisEquiv_self (b : BitBasis W) :
    xorBasisEquiv b b = groundBasis W := by
  funext w
  simp

/-- XOR by `b` produces the all-zero assignment exactly at `b`. -/
theorem xorBasisEquiv_eq_ground_iff (b x : BitBasis W) :
    xorBasisEquiv b x = groundBasis W ↔ x = b := by
  constructor
  · intro h
    funext w
    have hw := congrFun h w
    change xor (x w) (b w) = false at hw
    cases hx : x w <;> cases hb : b w <;> simp_all
  · intro h
    subst x
    exact xorBasisEquiv_self b

end Xor

section Matrix

variable {R : Type u} [Semiring R]
variable {W : Type v} [Fintype W]

/-- The one-hot column belonging to a computational-basis assignment. -/
def basisColumn (x : BitBasis W) : BitBasis W → R :=
  Pi.single x 1

/--
The scalar-generic permutation matrix which prepares the known assignment
`b` from the all-zero assignment.
-/
def basisPreparationMatrix (b : BitBasis W) :
    Matrix (BitBasis W) (BitBasis W) R :=
  Equiv.Perm.permMatrix R (xorBasisEquiv b)

/-- A basis-preparation permutation matrix is unitary over any star semiring. -/
theorem basisPreparationMatrix_mem_unitary [StarRing R] (b : BitBasis W) :
    basisPreparationMatrix (R := R) b ∈
      unitary (Matrix (BitBasis W) (BitBasis W) R) := by
  constructor
  · rw [Matrix.star_eq_conjTranspose, basisPreparationMatrix,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  · rw [Matrix.star_eq_conjTranspose, basisPreparationMatrix,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp

/-- The preparation matrix maps the all-zero basis column to the column at `b`. -/
theorem basisPreparationMatrix_mulVec_ground (b : BitBasis W) :
    basisPreparationMatrix (R := R) b *ᵥ basisColumn (R := R) (groundBasis W) =
      basisColumn (R := R) b := by
  classical
  rw [basisPreparationMatrix, PEquiv.toMatrix_toPEquiv_mulVec]
  ext x
  simp [basisColumn, Pi.single_apply, xorBasisEquiv_eq_ground_iff]

end Matrix

section Gate

variable {R : Type u} [Semiring R]
variable {W : Type v} [Fintype W]

/--
The known-basis preparation matrix packaged as a gate whose local wires are
all global wires and whose complement is empty.
-/
def basisPreparationGate (b : BitBasis W) : PlacedGate R W :=
  PlacedGate.ofSplit (Equiv.sumEmpty W (ULift.{v} Empty))
    (basisPreparationMatrix (R := R) b)

/-- The known-basis preparation gate has the whole global wire set as support. -/
@[simp]
theorem basisPreparationGate_support (b : BitBasis W) :
    (basisPreparationGate (R := R) b).support = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro w
  rw [PlacedGate.mem_support_iff]
  exact ⟨w, rfl⟩

private theorem place_sumEmpty (U : Matrix (BitBasis W) (BitBasis W) R) :
    place (Equiv.sumEmpty W (ULift.{v} Empty)) U = U := by
  ext x y
  rw [place_apply, if_pos (Subsingleton.elim _ _)]
  congr 1

/-- The global denotation of the full-support preparation gate is its matrix. -/
@[simp]
theorem basisPreparationGate_denote (b : BitBasis W) :
    (basisPreparationGate (R := R) b).denote =
      basisPreparationMatrix (R := R) b := by
  rw [basisPreparationGate, PlacedGate.denote_ofSplit, place_sumEmpty]

/-- The full-support preparation gate is certified locally unitary. -/
theorem basisPreparationGate_isLocallyUnitary [StarRing R] (b : BitBasis W) :
    (basisPreparationGate (R := R) b).IsLocallyUnitary := by
  rw [basisPreparationGate, PlacedGate.isLocallyUnitary_ofSplit]
  exact basisPreparationMatrix_mem_unitary b

/-- The global denotation of the preparation gate is unitary. -/
theorem basisPreparationGate_denote_mem_unitary [StarRing R] (b : BitBasis W) :
    (basisPreparationGate (R := R) b).denote ∈
      unitary (Matrix (BitBasis W) (BitBasis W) R) :=
  (basisPreparationGate (R := R) b).denote_mem_unitary
    (basisPreparationGate_isLocallyUnitary b)

/-- The preparation gate sends the all-zero basis column to the column at `b`. -/
theorem basisPreparationGate_mulVec_ground (b : BitBasis W) :
    (basisPreparationGate (R := R) b).denote *ᵥ
        basisColumn (R := R) (groundBasis W) =
      basisColumn (R := R) b := by
  rw [basisPreparationGate_denote, basisPreparationMatrix_mulVec_ground]

/--
Prepending the known-basis preparation gate absorbs a known basis input into
the chronological circuit while retaining an all-zero external input.
-/
theorem eval_prepend_basisPreparation_mulVec_ground
    (c : OrderedCircuit R W) (b : BitBasis W) :
    OrderedCircuit.eval (basisPreparationGate (R := R) b :: c) *ᵥ
        basisColumn (R := R) (groundBasis W) =
      OrderedCircuit.eval c *ᵥ basisColumn (R := R) b := by
  rw [OrderedCircuit.eval_cons, ← Matrix.mulVec_mulVec,
    basisPreparationGate_mulVec_ground]

end Gate

end QuaternionicComputing.Circuit
