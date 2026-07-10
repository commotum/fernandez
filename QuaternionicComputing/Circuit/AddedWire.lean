module

public import QuaternionicComputing.Circuit.Placement

/-!
# A distinguished added circuit wire

This module contains the embedding-independent bookkeeping for extending a
finite wire type `W` by one distinguished top wire, represented as
`Unit ⊕ W`.

The computational basis on `Unit ⊕ W` is canonically equivalent to two
copies of the basis on `W`: the left copy contains assignments whose top bit
is `false`, and the right copy those whose top bit is `true`.  A local wire
split `L ⊕ K ≃ W` extends to `(Unit ⊕ L) ⊕ K ≃ Unit ⊕ W`, so the
new top wire joins the local support while the complementary wires are
unchanged.

No scalar or matrix embedding is defined here.  Realification and
complexification use this shared wire algebra from separate proof leaves.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

/-- A wire type extended by one distinguished top wire. -/
abbrev AddedWire (W : Type*) := Unit ⊕ W

/--
The two-block basis equivalence for one added top wire.

The left summand encodes top bit `false`; the right summand encodes top bit
`true`.  Both retain the supplied assignment on the original tail wires.
-/
def addedBasisEquiv (W : Type*) :
    BitBasis W ⊕ BitBasis W ≃ BitBasis (AddedWire W) where
  toFun
    | Sum.inl x => Sum.elim (fun _ ↦ false) x
    | Sum.inr x => Sum.elim (fun _ ↦ true) x
  invFun x :=
    if x (Sum.inl ()) then Sum.inr (fun w ↦ x (Sum.inr w))
    else Sum.inl (fun w ↦ x (Sum.inr w))
  left_inv x := by
    rcases x with x | x <;> simp
  right_inv x := by
    ext w
    rcases w with (_ | w)
    · cases h : x (Sum.inl ()) <;> simp [h]
    · cases h : x (Sum.inl ()) <;> simp [h]

@[simp]
theorem addedBasisEquiv_inl_top (W : Type*) (x : BitBasis W) :
    addedBasisEquiv W (Sum.inl x) (Sum.inl ()) = false :=
  rfl

@[simp]
theorem addedBasisEquiv_inr_top (W : Type*) (x : BitBasis W) :
    addedBasisEquiv W (Sum.inr x) (Sum.inl ()) = true :=
  rfl

@[simp]
theorem addedBasisEquiv_inl_bottom (W : Type*) (x : BitBasis W) (w : W) :
    addedBasisEquiv W (Sum.inl x) (Sum.inr w) = x w :=
  rfl

@[simp]
theorem addedBasisEquiv_inr_bottom (W : Type*) (x : BitBasis W) (w : W) :
    addedBasisEquiv W (Sum.inr x) (Sum.inr w) = x w :=
  rfl

/--
Reindex square matrices from the two-block sum basis to the computational
basis of `AddedWire W`.

This is a generic star-monoid homomorphism over possibly noncommutative
coefficients.  Embedding-specific circuit leaves can compose their algebraic
matrix embedding with this common wire-facing reindexing.
-/
def addedBasisReindexStarMonoidHom (R W : Type*) [Semiring R] [StarRing R]
    [Fintype W] :
    Matrix (BitBasis W ⊕ BitBasis W) (BitBasis W ⊕ BitBasis W) R →⋆*
      Matrix (BitBasis (AddedWire W)) (BitBasis (AddedWire W)) R where
  toFun := Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W)
  map_one' := by
    exact map_one (Matrix.reindexRingEquiv R (addedBasisEquiv W))
  map_mul' A B := by
    exact map_mul (Matrix.reindexRingEquiv R (addedBasisEquiv W)) A B
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.conjTranspose_reindex
        (addedBasisEquiv W) (addedBasisEquiv W) A).symm

@[simp]
theorem addedBasisReindexStarMonoidHom_apply
    (R W : Type*) [Semiring R] [StarRing R] [Fintype W]
    (A : Matrix (BitBasis W ⊕ BitBasis W) (BitBasis W ⊕ BitBasis W) R) :
    addedBasisReindexStarMonoidHom R W A =
      Matrix.reindex (addedBasisEquiv W) (addedBasisEquiv W) A :=
  rfl

/--
Extend a local/complement split by adjoining one distinguished top wire to
the local side.  The complement type `K` is unchanged.
-/
def addTopSplit {L K W : Type*} (split : L ⊕ K ≃ W) :
    AddedWire L ⊕ K ≃ AddedWire W where
  toFun
    | Sum.inl (Sum.inl u) => Sum.inl u
    | Sum.inl (Sum.inr l) => Sum.inr (split (Sum.inl l))
    | Sum.inr k => Sum.inr (split (Sum.inr k))
  invFun
    | Sum.inl u => Sum.inl (Sum.inl u)
    | Sum.inr w =>
        match split.symm w with
        | Sum.inl l => Sum.inl (Sum.inr l)
        | Sum.inr k => Sum.inr k
  left_inv x := by
    rcases x with (u | l) | k
    · rfl
    · simp
    · simp
  right_inv x := by
    rcases x with u | w
    · rfl
    · generalize hs : split.symm w = s
      rcases s with l | k
      · simp only [hs]
        rw [← split.apply_symm_apply w, hs]
      · simp only [hs]
        rw [← split.apply_symm_apply w, hs]

@[simp]
theorem addTopSplit_top {L K W : Type*} (split : L ⊕ K ≃ W) (u : Unit) :
    addTopSplit split (Sum.inl (Sum.inl u)) = Sum.inl u :=
  rfl

@[simp]
theorem addTopSplit_local {L K W : Type*} (split : L ⊕ K ≃ W) (l : L) :
    addTopSplit split (Sum.inl (Sum.inr l)) =
      Sum.inr (split (Sum.inl l)) :=
  rfl

@[simp]
theorem addTopSplit_rest {L K W : Type*} (split : L ⊕ K ≃ W) (k : K) :
    addTopSplit split (Sum.inr k) = Sum.inr (split (Sum.inr k)) :=
  rfl

/-- Forget the distinguished top bit and retain the original tail assignment. -/
def tailBits {W : Type*} (x : BitBasis (AddedWire W)) : BitBasis W :=
  fun w ↦ x (Sum.inr w)

@[simp]
theorem tailBits_apply {W : Type*} (x : BitBasis (AddedWire W)) (w : W) :
    tailBits x w = x (Sum.inr w) :=
  rfl

/-- Adding the top local wire does not change the complementary assignment. -/
@[simp]
theorem complementBits_addTopSplit {L K W : Type*}
    (split : L ⊕ K ≃ W) (x : BitBasis (AddedWire W)) :
    complementBits (addTopSplit split) x =
      complementBits split (tailBits x) := by
  funext k
  simp [tailBits]

/-- The new local assignment's top bit is the global top bit. -/
@[simp]
theorem localBits_addTopSplit_top {L K W : Type*}
    (split : L ⊕ K ≃ W) (x : BitBasis (AddedWire W)) (u : Unit) :
    localBits (addTopSplit split) x (Sum.inl u) = x (Sum.inl u) := by
  simp

/-- The old local bits are the local restriction of the global tail. -/
@[simp]
theorem localBits_addTopSplit_bottom {L K W : Type*}
    (split : L ⊕ K ≃ W) (x : BitBasis (AddedWire W)) (l : L) :
    localBits (addTopSplit split) x (Sum.inr l) =
      localBits split (tailBits x) l := by
  simp [tailBits]

/-- Decode an added-wire assignment whose distinguished top bit is `false`. -/
@[simp]
theorem addedBasisEquiv_symm_false {W : Type*}
    (x : BitBasis (AddedWire W)) (h : x (Sum.inl ()) = false) :
    (addedBasisEquiv W).symm x = Sum.inl (tailBits x) := by
  simp [addedBasisEquiv, h]
  rfl

/-- Decode an added-wire assignment whose distinguished top bit is `true`. -/
@[simp]
theorem addedBasisEquiv_symm_true {W : Type*}
    (x : BitBasis (AddedWire W)) (h : x (Sum.inl ()) = true) :
    (addedBasisEquiv W).symm x = Sum.inr (tailBits x) := by
  simp [addedBasisEquiv, h]
  rfl

/--
Dropping the new top bit after taking the extended local restriction recovers
the original local restriction of the global tail.
-/
@[simp]
theorem tailBits_localBits_addTopSplit {L K W : Type*}
    (split : L ⊕ K ≃ W) (x : BitBasis (AddedWire W)) :
    tailBits (localBits (addTopSplit split) x) =
      localBits split (tailBits x) := by
  funext l
  simp [tailBits]

end QuaternionicComputing.Circuit
