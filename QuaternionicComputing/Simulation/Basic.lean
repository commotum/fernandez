module

public import QuaternionicComputing.Circuit.AddedWire
public import QuaternionicComputing.State.Basic

/-!
# Scalar-generic added-wire column transport

This module bridges the sum index used by the algebraic matrix embeddings and
the computational basis of the explicit distinguished top wire used by
circuits.  It contains no concrete scalar embedding and no circuit
translation.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit

universe u v

variable {R : Type u} {W : Type v}

/--
Transport a column on two copies of the original computational basis to the
basis of an explicit added top wire.
-/
def transportAddedColumn
    (v : BitBasis W ⊕ BitBasis W → R) : BitBasis (AddedWire W) → R :=
  v ∘ (addedBasisEquiv W).symm

/-- The left sum sector is the actual assignment with top bit `false`. -/
@[simp]
theorem transportAddedColumn_false
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis W) :
    transportAddedColumn v (addedBasisEquiv W (Sum.inl x)) = v (Sum.inl x) := by
  simp [transportAddedColumn]

/-- The right sum sector is the actual assignment with top bit `true`. -/
@[simp]
theorem transportAddedColumn_true
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis W) :
    transportAddedColumn v (addedBasisEquiv W (Sum.inr x)) = v (Sum.inr x) := by
  simp [transportAddedColumn]

/-- Evaluation at any added-wire assignment whose top bit is `false`. -/
theorem transportAddedColumn_apply_of_top_false
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis (AddedWire W))
    (hx : x (Sum.inl ()) = false) :
    transportAddedColumn v x = v (Sum.inl (tailBits x)) := by
  simp [transportAddedColumn, addedBasisEquiv_symm_false x hx]

/-- Evaluation at any added-wire assignment whose top bit is `true`. -/
theorem transportAddedColumn_apply_of_top_true
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis (AddedWire W))
    (hx : x (Sum.inl ()) = true) :
    transportAddedColumn v x = v (Sum.inr (tailBits x)) := by
  simp [transportAddedColumn, addedBasisEquiv_symm_true x hx]

/-- Added-wire transport loses no column coordinates. -/
theorem transportAddedColumn_injective :
    Function.Injective
      (transportAddedColumn : (BitBasis W ⊕ BitBasis W → R) →
        BitBasis (AddedWire W) → R) := by
  intro v w h
  funext i
  have hi := congrFun h (addedBasisEquiv W i)
  simpa [transportAddedColumn] using hi

/--
Reindexing a square matrix to the explicit added-wire basis commutes with
matrix action on transported columns.
-/
theorem reindex_mulVec_transportAddedColumn [Finite W]
    [NonUnitalNonAssocSemiring R]
    (A : Matrix (BitBasis W ⊕ BitBasis W) (BitBasis W ⊕ BitBasis W) R)
    (v : BitBasis W ⊕ BitBasis W → R) :
    Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W) A *ᵥ
        transportAddedColumn v =
      transportAddedColumn (A *ᵥ v) := by
  simpa [Matrix.reindex_apply, transportAddedColumn, Function.comp_def] using
    (Matrix.submatrix_mulVec_equiv A (transportAddedColumn v)
      (addedBasisEquiv W).symm (addedBasisEquiv W).symm)

/--
The total weight above a bottom assignment, summing the actual `false` and
`true` assignments of the distinguished top wire.
-/
def addedWireBottomWeight (weight : R → ℝ)
    (v : BitBasis (AddedWire W) → R) (x : BitBasis W) : ℝ :=
  QuaternionicComputing.State.basisWeight weight v
      (addedBasisEquiv W (Sum.inl x)) +
    QuaternionicComputing.State.basisWeight weight v
      (addedBasisEquiv W (Sum.inr x))

@[simp]
theorem addedWireBottomWeight_apply (weight : R → ℝ)
    (v : BitBasis (AddedWire W) → R) (x : BitBasis W) :
    addedWireBottomWeight weight v x =
      weight (v (addedBasisEquiv W (Sum.inl x))) +
        weight (v (addedBasisEquiv W (Sum.inr x))) :=
  rfl

/-- Bottom weight of a transported column is the sum of its two source-sector weights. -/
@[simp]
theorem addedWireBottomWeight_transportAddedColumn (weight : R → ℝ)
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis W) :
    addedWireBottomWeight weight (transportAddedColumn v) x =
      QuaternionicComputing.State.basisWeight weight v (Sum.inl x) +
        QuaternionicComputing.State.basisWeight weight v (Sum.inr x) := by
  simp [addedWireBottomWeight, QuaternionicComputing.State.basisWeight]

end QuaternionicComputing.Simulation
