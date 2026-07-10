module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Sum

/-!
# Contextual placement of finite-wire gates

A computational-basis label on a wire type `W` is a function `W → Bool`.
An explicit equivalence `L ⊕ K ≃ W` therefore splits every global basis
label into its local and complementary parts.  The contextual matrix of a
local gate `U` is obtained by reindexing `U ⊗ₖ 1` along this split.

The multiplication proof identifies tensoring on the right by the identity
with a block diagonal matrix.  Its multiplication law is valid over
noncommutative semirings, unlike the generic same-ring Kronecker product
multiplication theorem.  Consequently the API applies in particular to
quaternionic matrices.
-/

@[expose] public noncomputable section

open scoped Matrix Kronecker

namespace QuaternionicComputing.Circuit

/-- A computational-basis assignment on the finite wire type `W`. -/
abbrev BitBasis (W : Type*) := W → Bool

/-- A finite wire type has a finite computational basis. -/
noncomputable instance bitBasisFintype (W : Type*) [Finite W] :
    Fintype (BitBasis W) :=
  Fintype.ofFinite _

/--
Split global basis assignments into their local and complementary assignments
using an explicit decomposition of the wire type.
-/
def basisSplit {L K W : Type*} (split : L ⊕ K ≃ W) :
    BitBasis W ≃ BitBasis L × BitBasis K :=
  (Equiv.piCongrLeft (fun _ : W => Bool) split).symm.trans
    (Equiv.sumArrowEquivProdArrow L K Bool)

@[simp]
theorem basisSplit_apply_fst {L K W : Type*} (split : L ⊕ K ≃ W)
    (x : BitBasis W) (l : L) :
    (basisSplit split x).1 l = x (split (Sum.inl l)) := by
  simp [basisSplit]

@[simp]
theorem basisSplit_apply_snd {L K W : Type*} (split : L ⊕ K ≃ W)
    (x : BitBasis W) (k : K) :
    (basisSplit split x).2 k = x (split (Sum.inr k)) := by
  simp [basisSplit]

/-- Restrict a global basis assignment to the selected local wires. -/
def localBits {L K W : Type*} (split : L ⊕ K ≃ W) (x : BitBasis W) :
    BitBasis L :=
  (basisSplit split x).1

/-- Restrict a global basis assignment to the complementary wires. -/
def complementBits {L K W : Type*} (split : L ⊕ K ≃ W)
    (x : BitBasis W) : BitBasis K :=
  (basisSplit split x).2

@[simp]
theorem localBits_apply {L K W : Type*} (split : L ⊕ K ≃ W)
    (x : BitBasis W) (l : L) :
    localBits split x l = x (split (Sum.inl l)) :=
  basisSplit_apply_fst split x l

@[simp]
theorem complementBits_apply {L K W : Type*} (split : L ⊕ K ≃ W)
    (x : BitBasis W) (k : K) :
    complementBits split x k = x (split (Sum.inr k)) :=
  basisSplit_apply_snd split x k

/--
Place a local matrix on the wires selected by `split`, acting as the identity
on all complementary wires.
-/
def place {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    Matrix (BitBasis W) (BitBasis W) R :=
  Matrix.reindexRingEquiv R (basisSplit split).symm
    (U ⊗ₖ (1 : Matrix (BitBasis K) (BitBasis K) R))

/--
Exact entrywise semantics of contextual placement: the local entry is used
precisely when the two complementary assignments agree.
-/
@[simp]
theorem place_apply {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) (x y : BitBasis W) :
    place split U x y =
      if complementBits split x = complementBits split y then
        U (localBits split x) (localBits split y)
      else 0 := by
  simp [place, localBits, complementBits, Matrix.reindex_apply,
    Matrix.one_apply]

@[simp]
theorem place_zero {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W) :
    place split (0 : Matrix (BitBasis L) (BitBasis L) R) = 0 := by
  ext x y
  simp

@[simp]
theorem place_add {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U V : Matrix (BitBasis L) (BitBasis L) R) :
    place split (U + V) = place split U + place split V := by
  ext x y
  by_cases h : complementBits split x = complementBits split y <;> simp [h]

@[simp]
theorem place_one {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W) :
    place split (1 : Matrix (BitBasis L) (BitBasis L) R) = 1 := by
  simp [place]

/--
Tensoring on the right by an identity matrix preserves multiplication over a
possibly noncommutative semiring.
-/
theorem kronecker_one_mul {R I K : Type*} [Semiring R] [Fintype I]
    [Fintype K] [DecidableEq K] (U V : Matrix I I R) :
    (U * V) ⊗ₖ (1 : Matrix K K R) =
      (U ⊗ₖ (1 : Matrix K K R)) * (V ⊗ₖ (1 : Matrix K K R)) := by
  rw [Matrix.kronecker_one, Matrix.kronecker_one, Matrix.kronecker_one,
    Matrix.blockDiagonal_mul]

@[simp]
theorem place_mul {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W)
    (U V : Matrix (BitBasis L) (BitBasis L) R) :
    place split (U * V) = place split U * place split V := by
  simp only [place, kronecker_one_mul]
  exact map_mul (Matrix.reindexRingEquiv R (basisSplit split).symm) _ _

/-- Placement is an injective ring homomorphism. -/
def placeRingHom {R L K W : Type*} [Semiring R] [Fintype L] [Fintype K]
    [Fintype W] (split : L ⊕ K ≃ W) :
    Matrix (BitBasis L) (BitBasis L) R →+*
      Matrix (BitBasis W) (BitBasis W) R where
  toFun := place split
  map_zero' := place_zero split
  map_one' := place_one split
  map_add' := place_add split
  map_mul' := place_mul split

@[simp]
theorem placeRingHom_apply {R L K W : Type*} [Semiring R] [Fintype L]
    [Fintype K] [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    placeRingHom split U = place split U :=
  rfl

/--
Placement loses no local matrix entries.  No inhabitance hypothesis on the
complement is needed: its bit-assignment type always contains the all-false
assignment, even when `K` itself is empty.
-/
theorem place_injective {R L K W : Type*} [Semiring R] [Fintype L]
    [Fintype K] [Fintype W] (split : L ⊕ K ≃ W) :
    Function.Injective
      (place split : Matrix (BitBasis L) (BitBasis L) R →
        Matrix (BitBasis W) (BitBasis W) R) := by
  intro U V h
  ext x y
  let z : BitBasis K := fun _ => false
  let x' : BitBasis W := (basisSplit split).symm (x, z)
  let y' : BitBasis W := (basisSplit split).symm (y, z)
  have hxy := congrFun (congrFun h x') y'
  simpa [x', y', localBits, complementBits] using hxy

@[simp]
theorem place_conjTranspose {R L K W : Type*} [Semiring R] [StarAddMonoid R]
    [Fintype L] [Fintype K] [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    place split Uᴴ = (place split U)ᴴ := by
  ext x y
  by_cases h : complementBits split x = complementBits split y <;>
    simp [Matrix.conjTranspose_apply, h, eq_comm]

@[simp]
theorem place_star {R L K W : Type*} [Semiring R] [StarRing R]
    [Fintype L] [Fintype K] [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    place split (star U) = star (place split U) := by
  simpa only [Matrix.star_eq_conjTranspose] using place_conjTranspose split U

/-- Placement as a star-preserving monoid homomorphism. -/
def placeStarMonoidHom {R L K W : Type*} [Semiring R] [StarRing R]
    [Fintype L] [Fintype K] [Fintype W] (split : L ⊕ K ≃ W) :
    Matrix (BitBasis L) (BitBasis L) R →⋆*
      Matrix (BitBasis W) (BitBasis W) R where
  toFun := place split
  map_one' := place_one split
  map_mul' := place_mul split
  map_star' := place_star split

@[simp]
theorem placeStarMonoidHom_apply {R L K W : Type*} [Semiring R] [StarRing R]
    [Fintype L] [Fintype K] [Fintype W] (split : L ⊕ K ≃ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    placeStarMonoidHom split U = place split U :=
  rfl

/-- A local unitary matrix remains unitary after contextual placement. -/
theorem place_mem_unitary {R L K W : Type*} [Semiring R] [StarRing R]
    [Fintype L] [Fintype K] [Fintype W] (split : L ⊕ K ≃ W)
    {U : Matrix (BitBasis L) (BitBasis L) R}
    (hU : U ∈ unitary (Matrix (BitBasis L) (BitBasis L) R)) :
    place split U ∈ unitary (Matrix (BitBasis W) (BitBasis W) R) :=
  Unitary.map_mem (placeStarMonoidHom split) hU

/-! ## Constructing a split from an injective support -/

/-- The global wires outside the range of an injective local support. -/
abbrev SupportComplement {L W : Type*} (support : L ↪ W) :=
  {w : W // w ∉ Set.range support}

/--
An injective enumeration of selected wires canonically gives a local/complement
wire split.  The selected wires may be noncontiguous and arbitrarily ordered.
-/
def supportSplit {L W : Type*} (support : L ↪ W) :
    L ⊕ SupportComplement support ≃ W := by
  classical
  exact
    (Equiv.sumCongr (Equiv.ofInjective support support.injective) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun w ↦ w ∈ Set.range support))

@[simp]
theorem supportSplit_apply_inl {L W : Type*} (support : L ↪ W) (l : L) :
    supportSplit support (Sum.inl l) = support l :=
  by
    classical
    simp [supportSplit]

@[simp]
theorem supportSplit_apply_inr {L W : Type*} (support : L ↪ W)
    (k : SupportComplement support) :
    supportSplit support (Sum.inr k) = k :=
  by
    classical
    simp [supportSplit]

/-- Place a local gate on the range of an injective finite-wire support. -/
def placeOnSupport {R L W : Type*} [Semiring R] [Fintype L] [Fintype W]
    (support : L ↪ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) :
    Matrix (BitBasis W) (BitBasis W) R :=
  letI : Fintype (SupportComplement support) := Fintype.ofFinite _
  place (supportSplit support) U

end QuaternionicComputing.Circuit
