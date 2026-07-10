module

public import QuaternionicComputing.Circuit.Basic
public import QuaternionicComputing.Circuit.AddedWire
public import QuaternionicComputing.Matrix.Complexification

/-!
# Quaternionic gate complexification on one added wire

This module moves the sum-index block embedding of a quaternionic matrix to
the computational basis of an explicit distinguished top wire.  It then
translates one placed quaternionic gate: the new top wire joins the gate's
local support, while the original complementary wires are unchanged.

Only gatewise semantics are treated here.  Mapping and evaluating ordered
circuits belongs to the simulation layer.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Circuit

universe v

/--
Complexification of a quaternionic matrix, reindexed so its two block sectors
are the two assignments of one explicit distinguished top wire.
-/
def wireComplexify {W : Type*}
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) :
    Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℂ :=
  Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
    (QuaternionicComputing.Quaternion.complexify A)

/-- The wire-facing complexification loses no matrix entries. -/
theorem wireComplexify_injective {W : Type*} :
    Function.Injective (@wireComplexify W) := by
  intro A B h
  apply QuaternionicComputing.Quaternion.complexify_injective
  exact (Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)).injective h

@[simp]
theorem wireComplexify_eq_iff {W : Type*}
    {A B : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]} :
    wireComplexify A = wireComplexify B ↔ A = B :=
  wireComplexify_injective.eq_iff

/-- Wire-facing complexification sends identity to identity. -/
@[simp]
theorem wireComplexify_one {W : Type*} [Fintype W] :
    wireComplexify (1 : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) = 1 := by
  classical
  rw [wireComplexify, QuaternionicComputing.Quaternion.complexify_one]
  exact map_one (Matrix.reindexRingEquiv ℂ (addedBasisEquiv W))

set_option linter.unusedFintypeInType false in
/-- Wire-facing complexification preserves multiplication. -/
@[simp]
theorem wireComplexify_mul {W : Type*} [Fintype W]
    (A B : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) :
    wireComplexify (A * B) = wireComplexify A * wireComplexify B := by
  classical
  rw [wireComplexify, QuaternionicComputing.Quaternion.complexify_mul]
  exact map_mul (Matrix.reindexRingEquiv ℂ (addedBasisEquiv W)) _ _

/-- Wire-facing complexification commutes with the matrix adjoint. -/
@[simp]
theorem wireComplexify_conjTranspose {W : Type*}
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) :
    wireComplexify Aᴴ = (wireComplexify A)ᴴ := by
  rw [wireComplexify, QuaternionicComputing.Quaternion.complexify_conjTranspose]
  change Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
      (QuaternionicComputing.Quaternion.complexify A)ᴴ =
    (Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
      (QuaternionicComputing.Quaternion.complexify A))ᴴ
  exact (Matrix.conjTranspose_reindex _ _ _).symm

/--
Wire-facing complexification as the star-monoid homomorphism consumed by
ordered-circuit evaluation in the simulation layer.
-/
def wireComplexifyStarMonoidHom (W : Type*) [Fintype W] :
    Matrix (BitBasis W) (BitBasis W) ℍ[ℝ] →⋆*
      Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℂ where
  toFun := wireComplexify
  map_one' := wireComplexify_one
  map_mul' := wireComplexify_mul
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose] using wireComplexify_conjTranspose A

@[simp]
theorem wireComplexifyStarMonoidHom_apply (W : Type*) [Fintype W]
    (A : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]) :
    wireComplexifyStarMonoidHom W A = wireComplexify A :=
  rfl

/-- A quaternionic unitary remains unitary after wire-facing complexification. -/
theorem wireComplexify_mem_unitary {W : Type*} [Fintype W]
    {U : Matrix (BitBasis W) (BitBasis W) ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix (BitBasis W) (BitBasis W) ℍ[ℝ])) :
    wireComplexify U ∈
      unitary (Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) ℂ) :=
  Unitary.map_mem (wireComplexifyStarMonoidHom W) hU

/--
Complexification commutes with contextual placement.  The target placement
uses the same complementary wire type and adds the distinguished top wire to
the local side.
-/
theorem wireComplexify_place {L K W : Type*} [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) ℍ[ℝ]) :
    wireComplexify (place split U) =
      place (addTopSplit split) (wireComplexify U) := by
  ext x y
  by_cases hc : complementBits split (tailBits x) =
      complementBits split (tailBits y) <;>
    cases hx : x (Sum.inl ()) <;> cases hy : y (Sum.inl ()) <;>
    simp [wireComplexify, Matrix.reindex_apply, place_apply, hx, hy, hc,
      addedBasisEquiv_symm_false, addedBasisEquiv_symm_true]

/-- Translate one placed quaternionic gate by adjoining the shared top wire. -/
def complexifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) : PlacedGate ℂ (AddedWire W) := by
  letI := g.localFintype
  letI := g.complementFintype
  exact PlacedGate.ofSplit (addTopSplit g.split) (wireComplexify g.localMatrix)

/-- The translated gate denotes the wire-facing complexification of the source gate. -/
@[simp]
theorem complexifyPlacedGate_denote {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) :
    (complexifyPlacedGate g).denote = wireComplexify g.denote := by
  letI := g.localFintype
  letI := g.complementFintype
  change place (addTopSplit g.split) (wireComplexify g.localMatrix) =
    wireComplexify (place g.split g.localMatrix)
  exact (wireComplexify_place g.split g.localMatrix).symm

/-- Translating a local gate increases its local wire arity by exactly one. -/
@[simp]
theorem localArity_complexifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) :
    (complexifyPlacedGate g).localArity = g.localArity + 1 := by
  letI := g.localFintype
  letI := g.complementFintype
  change Fintype.card (AddedWire g.Local) = Fintype.card g.Local + 1
  simp [AddedWire, Nat.add_comm]

/-- Translating a local gate leaves the complementary wire arity unchanged. -/
@[simp]
theorem complementArity_complexifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) :
    (complexifyPlacedGate g).complementArity = g.complementArity := by
  letI := g.localFintype
  letI := g.complementFintype
  rfl

/-- Local unitarity is preserved by placed-gate complexification. -/
theorem isLocallyUnitary_complexifyPlacedGate {W : Type v} [Fintype W]
    (g : PlacedGate ℍ[ℝ] W) (hg : g.IsLocallyUnitary) :
    (complexifyPlacedGate g).IsLocallyUnitary := by
  letI := g.localFintype
  letI := g.complementFintype
  exact wireComplexify_mem_unitary hg

end QuaternionicComputing.Circuit
