module

public import QuaternionicComputing.Circuit.Basic
public import QuaternionicComputing.Circuit.AddedWire
public import QuaternionicComputing.Matrix.Realification

/-!
# Complex gate realification on one added wire

This module moves the sum-index realification of a complex matrix to the
computational basis of one explicit distinguished top wire.  It then
translates a placed complex gate: the top wire joins the gate's local support,
while its complementary wire type is unchanged.

Only the semantics of one placed gate are treated here.  Translation and
evaluation of ordered circuits belong to the simulation layer.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Circuit

universe v

/--
Realification of a complex matrix, reindexed so its two real block sectors
are the two assignments of one explicit distinguished top wire.
-/
def wireRealify {W : Type*}
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) :
    Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℝ :=
  Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
    (QuaternionicComputing.Matrix.realify A)

/-- The wire-facing realification loses no matrix entries. -/
theorem wireRealify_injective {W : Type*} :
    Function.Injective (@wireRealify W) := by
  intro A B h
  apply QuaternionicComputing.Matrix.realify_injective
  exact (Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)).injective h

@[simp]
theorem wireRealify_eq_iff {W : Type*}
    {A B : Matrix (BitBasis W) (BitBasis W) ℂ} :
    wireRealify A = wireRealify B ↔ A = B :=
  wireRealify_injective.eq_iff

/-- Wire-facing realification sends identity to identity. -/
@[simp]
theorem wireRealify_one {W : Type*} [Fintype W] :
    wireRealify (1 : Matrix (BitBasis W) (BitBasis W) ℂ) = 1 := by
  classical
  rw [wireRealify, QuaternionicComputing.Matrix.realify_one]
  exact map_one (Matrix.reindexRingEquiv ℝ (addedBasisEquiv W))

/-- Wire-facing realification preserves multiplication. -/
@[simp]
theorem wireRealify_mul {W : Type*} [Finite W]
    (A B : Matrix (BitBasis W) (BitBasis W) ℂ) :
    wireRealify (A * B) = wireRealify A * wireRealify B := by
  classical
  rw [wireRealify, QuaternionicComputing.Matrix.realify_mul]
  exact map_mul (Matrix.reindexRingEquiv ℝ (addedBasisEquiv W)) _ _

/-- Wire-facing realification commutes with the matrix adjoint. -/
@[simp]
theorem wireRealify_conjTranspose {W : Type*}
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) :
    wireRealify Aᴴ = (wireRealify A)ᴴ := by
  rw [wireRealify, QuaternionicComputing.Matrix.realify_conjTranspose]
  change Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
      (QuaternionicComputing.Matrix.realify A)ᵀ =
    (Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
      (QuaternionicComputing.Matrix.realify A))ᴴ
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.transpose_reindex _ _ _).symm

/--
Wire-facing realification as the star-monoid homomorphism consumed by ordered
circuit evaluation in the simulation layer.
-/
def wireRealifyStarMonoidHom (W : Type*) [Fintype W] :
    Matrix (BitBasis W) (BitBasis W) ℂ →⋆*
      Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℝ where
  toFun := wireRealify
  map_one' := wireRealify_one
  map_mul' := wireRealify_mul
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose] using wireRealify_conjTranspose A

@[simp]
theorem wireRealifyStarMonoidHom_apply (W : Type*) [Fintype W]
    (A : Matrix (BitBasis W) (BitBasis W) ℂ) :
    wireRealifyStarMonoidHom W A = wireRealify A :=
  rfl

/-- A complex unitary remains unitary after wire-facing realification. -/
theorem wireRealify_mem_unitary {W : Type*} [Fintype W]
    {U : Matrix (BitBasis W) (BitBasis W) ℂ}
    (hU : U ∈ unitary (Matrix (BitBasis W) (BitBasis W) ℂ)) :
    wireRealify U ∈
      unitary (Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℝ) :=
  Unitary.map_mem (wireRealifyStarMonoidHom W) hU

/--
Realification commutes with contextual placement.  The target placement uses
the same complementary wire type and adds the distinguished top wire to the
local side.
-/
theorem wireRealify_place {L K W : Type*} [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) ℂ) :
    wireRealify (place split U) =
      place (addTopSplit split) (wireRealify U) := by
  ext x y
  cases hx : x (Sum.inl ()) <;> cases hy : y (Sum.inl ())
  all_goals
    simp [wireRealify, Matrix.reindex_apply, place_apply, hx, hy,
      addedBasisEquiv_symm_false, addedBasisEquiv_symm_true]
  all_goals
    by_cases h : complementBits split (tailBits x) =
        complementBits split (tailBits y) <;> simp [h]

/-- Translate one placed complex gate by adjoining the shared top wire. -/
def realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) : PlacedGate ℝ (AddedWire W) := by
  letI := g.localFintype
  letI := g.complementFintype
  exact PlacedGate.ofSplit (addTopSplit g.split) (wireRealify g.localMatrix)

/-- The added local top wire is the shared global top wire. -/
@[simp]
theorem localSupport_realifyPlacedGate_top {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) (u : Unit) :
    (realifyPlacedGate g).localSupport (Sum.inl u) = Sum.inl u := by
  letI := g.localFintype
  letI := g.complementFintype
  change addTopSplit g.split (Sum.inl (Sum.inl u)) = Sum.inl u
  rfl

/-- Every original local wire remains the corresponding bottom global wire. -/
@[simp]
theorem localSupport_realifyPlacedGate_bottom {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) (l : g.Local) :
    (realifyPlacedGate g).localSupport (Sum.inr l) =
      Sum.inr (g.localSupport l) := by
  letI := g.localFintype
  letI := g.complementFintype
  change addTopSplit g.split (Sum.inl (Sum.inr l)) =
    Sum.inr (g.split (Sum.inl l))
  rfl

/-- Every complementary wire remains the corresponding bottom global wire. -/
@[simp]
theorem complementSupport_realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) (k : g.Complement) :
    (realifyPlacedGate g).complementSupport k =
      Sum.inr (g.complementSupport k) := by
  letI := g.localFintype
  letI := g.complementFintype
  change addTopSplit g.split (Sum.inr k) =
    Sum.inr (g.split (Sum.inr k))
  rfl

/-- The translated gate denotes the wire-facing realification of the source gate. -/
@[simp]
theorem realifyPlacedGate_denote {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) :
    (realifyPlacedGate g).denote = wireRealify g.denote := by
  letI := g.localFintype
  letI := g.complementFintype
  change place (addTopSplit g.split) (wireRealify g.localMatrix) =
    wireRealify (place g.split g.localMatrix)
  exact (wireRealify_place g.split g.localMatrix).symm

/-- Translating a local gate increases its local wire arity by exactly one. -/
@[simp]
theorem localArity_realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) :
    (realifyPlacedGate g).localArity = g.localArity + 1 := by
  letI := g.localFintype
  letI := g.complementFintype
  change Fintype.card (AddedWire g.Local) = Fintype.card g.Local + 1
  simp [AddedWire, Nat.add_comm]

/-- Translating a local gate leaves the complementary wire arity unchanged. -/
@[simp]
theorem complementArity_realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) :
    (realifyPlacedGate g).complementArity = g.complementArity := by
  letI := g.localFintype
  letI := g.complementFintype
  rfl

/-- Local unitarity is preserved by placed-gate realification. -/
theorem isLocallyUnitary_realifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℂ W) (hg : g.IsLocallyUnitary) :
    (realifyPlacedGate g).IsLocallyUnitary := by
  letI := g.localFintype
  letI := g.complementFintype
  exact wireRealify_mem_unitary hg

end QuaternionicComputing.Circuit
