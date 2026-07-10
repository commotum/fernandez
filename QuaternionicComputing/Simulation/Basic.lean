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

/-- Added-wire transport preserves the total weight of every finite column. -/
@[simp]
theorem totalWeight_transportAddedColumn [Finite W] (weight : R → ℝ)
    (v : BitBasis W ⊕ BitBasis W → R) :
    QuaternionicComputing.State.totalWeight weight (transportAddedColumn v) =
      QuaternionicComputing.State.totalWeight weight v := by
  simpa [QuaternionicComputing.State.totalWeight,
    QuaternionicComputing.State.basisWeight, transportAddedColumn,
    Function.comp_def] using
    ((addedBasisEquiv W).symm.sum_comp (fun i => weight (v i)))

/-- Transport a normalized sum-index state to the explicit added-wire basis. -/
def transportAddedState [Finite W] {weight : R → ℝ}
    (v : QuaternionicComputing.State.NormalizedState
      (BitBasis W ⊕ BitBasis W) R weight) :
    QuaternionicComputing.State.NormalizedState
      (BitBasis (AddedWire W)) R weight :=
  ⟨transportAddedColumn v, by
    rw [totalWeight_transportAddedColumn]
    exact v.property⟩

@[simp]
theorem transportAddedState_apply [Finite W] {weight : R → ℝ}
    (v : QuaternionicComputing.State.NormalizedState
      (BitBasis W ⊕ BitBasis W) R weight)
    (x : BitBasis (AddedWire W)) :
    transportAddedState v x = transportAddedColumn v x :=
  rfl

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

/-- Pointwise nonnegative scalar weights give nonnegative bottom weights. -/
theorem addedWireBottomWeight_nonneg (weight : R → ℝ)
    (hweight : ∀ r, 0 ≤ weight r)
    (v : BitBasis (AddedWire W) → R) (x : BitBasis W) :
    0 ≤ addedWireBottomWeight weight v x := by
  exact add_nonneg
    (hweight (v (addedBasisEquiv W (Sum.inl x))))
    (hweight (v (addedBasisEquiv W (Sum.inr x))))

/-- Summing bottom weights recovers the full added-wire total weight. -/
theorem sum_addedWireBottomWeight [Finite W] (weight : R → ℝ)
    (v : BitBasis (AddedWire W) → R) :
    (∑ x : BitBasis W, addedWireBottomWeight weight v x) =
      QuaternionicComputing.State.totalWeight weight v := by
  calc
    (∑ x : BitBasis W, addedWireBottomWeight weight v x) =
        ∑ s : BitBasis W ⊕ BitBasis W,
          QuaternionicComputing.State.basisWeight weight v
            (addedBasisEquiv W s) := by
      simp [addedWireBottomWeight, Fintype.sum_sum_type,
        Finset.sum_add_distrib]
    _ = ∑ y : BitBasis (AddedWire W),
          QuaternionicComputing.State.basisWeight weight v y :=
      (addedBasisEquiv W).sum_comp _
    _ = QuaternionicComputing.State.totalWeight weight v :=
      rfl

/-- Bottom weights of a normalized added-wire state have total mass one. -/
@[simp]
theorem sum_addedWireBottomWeight_normalized [Finite W]
    {weight : R → ℝ}
    (v : QuaternionicComputing.State.NormalizedState
      (BitBasis (AddedWire W)) R weight) :
    (∑ x : BitBasis W, addedWireBottomWeight weight v x) = 1 := by
  rw [sum_addedWireBottomWeight]
  exact v.property

/-- Nonnegative scalar weights make every normalized bottom weight nonnegative. -/
theorem addedWireBottomWeight_normalized_nonneg [Finite W]
    {weight : R → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    (v : QuaternionicComputing.State.NormalizedState
      (BitBasis (AddedWire W)) R weight) (x : BitBasis W) :
    0 ≤ addedWireBottomWeight weight v x :=
  addedWireBottomWeight_nonneg weight hweight v x

/-- Bottom weight of a transported column is the sum of its two source-sector weights. -/
@[simp]
theorem addedWireBottomWeight_transportAddedColumn (weight : R → ℝ)
    (v : BitBasis W ⊕ BitBasis W → R) (x : BitBasis W) :
    addedWireBottomWeight weight (transportAddedColumn v) x =
      QuaternionicComputing.State.basisWeight weight v (Sum.inl x) +
        QuaternionicComputing.State.basisWeight weight v (Sum.inr x) := by
  simp [addedWireBottomWeight, QuaternionicComputing.State.basisWeight]

end QuaternionicComputing.Simulation
