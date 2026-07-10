module

public import QuaternionicComputing.Simulation.ComplexToReal

/-!
# A pure non-product realification witness

This file defines pure top/bottom product factorization directly on columns
indexed by the computational basis of `AddedWire W`.  The factorization uses
the actual assignments of the distinguished top wire and the original bottom
wires; the top scalar is multiplied on the left.

The concrete example realifies the normalized one-wire complex state with
amplitudes `3/5` at bottom `0` and `(4/5)i` at bottom `1`.  Its canonical first
real column has coordinates `(3/5, 0, 0, -4/5)` in
`(top,bottom) = (0,0), (0,1), (1,0), (1,1)` order and is not a pure product
column.

This is one pure non-product witness.  It is not a mixed-state, signaling,
entanglement-generation, or cryptographic-security theorem.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe u v

/--
The actual added-wire basis assignment with distinguished top value `top` and
bottom assignment `bottom`.
-/
def topBottomAssignment {W : Type u} (top : Bool) (bottom : BitBasis W) :
    BitBasis (AddedWire W) :=
  match top with
  | false => addedBasisEquiv W (Sum.inl bottom)
  | true => addedBasisEquiv W (Sum.inr bottom)

@[simp]
theorem topBottomAssignment_false {W : Type u} (bottom : BitBasis W) :
    topBottomAssignment false bottom = addedBasisEquiv W (Sum.inl bottom) :=
  rfl

@[simp]
theorem topBottomAssignment_true {W : Type u} (bottom : BitBasis W) :
    topBottomAssignment true bottom = addedBasisEquiv W (Sum.inr bottom) :=
  rfl

@[simp]
theorem topBottomAssignment_top {W : Type u} (top : Bool)
    (bottom : BitBasis W) :
    topBottomAssignment top bottom (Sum.inl ()) = top := by
  cases top <;> rfl

@[simp]
theorem topBottomAssignment_bottom {W : Type u} (top : Bool)
    (bottom : BitBasis W) (w : W) :
    topBottomAssignment top bottom (Sum.inr w) = bottom w := by
  cases top <;> rfl

/--
A column on one added wire and a bottom system factors as a pure top column
times a pure bottom column.  The multiplication order is explicitly
`topFactor top * bottomFactor bottom`.  The two factors are not required to be
normalized, so failure of this predicate is stronger than failure among
normalized product factors.
-/
def IsPureTopBottomProduct {R : Type v} {W : Type u} [Mul R]
    (column : BitBasis (AddedWire W) → R) : Prop :=
  ∃ topFactor : Bool → R, ∃ bottomFactor : BitBasis W → R,
    ∀ top bottom,
      column (topBottomAssignment top bottom) =
        topFactor top * bottomFactor bottom

namespace NonProductWitness

/-! ## One bottom wire and the normalized complex source state -/

/-- The one-wire bottom assignment with the supplied Boolean value. -/
def oneWireBasis (bit : Bool) : BitBasis Unit :=
  fun _ ↦ bit

@[simp]
theorem oneWireBasis_apply (bit : Bool) (u : Unit) :
    oneWireBasis bit u = bit :=
  rfl

/-- Identify a Boolean value with the corresponding one-wire assignment. -/
def boolEquivOneWireBasis : Bool ≃ BitBasis Unit where
  toFun := oneWireBasis
  invFun x := x ()
  left_inv _ := rfl
  right_inv x := by
    funext u
    cases u
    rfl

/-- The source amplitude column: `3/5` at `0` and `(4/5)i` at `1`. -/
def sourceColumn (x : BitBasis Unit) : ℂ :=
  if x () then ⟨0, 4 / 5⟩ else ⟨3 / 5, 0⟩

@[simp]
theorem sourceColumn_zero :
    sourceColumn (oneWireBasis false) = (⟨3 / 5, 0⟩ : ℂ) := by
  simp [sourceColumn]

@[simp]
theorem sourceColumn_one :
    sourceColumn (oneWireBasis true) = (⟨0, 4 / 5⟩ : ℂ) := by
  simp [sourceColumn]

/-- The non-real amplitude is literally `(4/5)i`. -/
theorem sourceColumn_one_eq_mul_I :
    sourceColumn (oneWireBasis true) = (4 / 5 : ℂ) * Complex.I := by
  apply Complex.ext <;> norm_num [sourceColumn]

/-- The source column has exact total complex weight one. -/
theorem sourceColumn_normalization :
    complexTotalWeight sourceColumn = 1 := by
  change (∑ x : BitBasis Unit, Complex.normSq (sourceColumn x)) = 1
  rw [← boolEquivOneWireBasis.sum_comp]
  simp [sourceColumn, boolEquivOneWireBasis, oneWireBasis,
    Fintype.univ_bool, Complex.normSq_apply]
  norm_num

/-- The explicitly normalized one-bottom-wire source state. -/
def sourceState : ComplexState (BitBasis Unit) :=
  ⟨sourceColumn, sourceColumn_normalization⟩

/-! ## Canonical wire-facing realification -/

/-- The canonical first real column on the actual added-wire basis. -/
def encodedColumn : BitBasis (AddedWire Unit) → ℝ :=
  wireRealColumn0 sourceColumn

/-- The same canonical encoding, bundled with its proved normalization. -/
def encodedState : RealState (BitBasis (AddedWire Unit)) :=
  wireRealColumn0State sourceState

@[simp]
theorem encodedState_apply (x : BitBasis (AddedWire Unit)) :
    encodedState x = encodedColumn x :=
  rfl

@[simp]
theorem encodedColumn_false_zero :
    encodedColumn (topBottomAssignment false (oneWireBasis false)) = 3 / 5 := by
  norm_num [encodedColumn, wireRealColumn0, transportAddedColumn,
    sourceColumn, topBottomAssignment, oneWireBasis, realColumn0]

@[simp]
theorem encodedColumn_false_one :
    encodedColumn (topBottomAssignment false (oneWireBasis true)) = 0 := by
  norm_num [encodedColumn, wireRealColumn0, transportAddedColumn,
    sourceColumn, topBottomAssignment, oneWireBasis, realColumn0]

@[simp]
theorem encodedColumn_true_zero :
    encodedColumn (topBottomAssignment true (oneWireBasis false)) = 0 := by
  norm_num [encodedColumn, wireRealColumn0, transportAddedColumn,
    sourceColumn, topBottomAssignment, oneWireBasis, realColumn0]

@[simp]
theorem encodedColumn_true_one :
    encodedColumn (topBottomAssignment true (oneWireBasis true)) = -4 / 5 := by
  norm_num [encodedColumn, wireRealColumn0, transportAddedColumn,
    sourceColumn, topBottomAssignment, oneWireBasis, realColumn0]

/-- The four exact coordinates, in `(top,bottom) = 00, 01, 10, 11` order. -/
theorem encodedColumn_coordinates :
    encodedColumn (topBottomAssignment false (oneWireBasis false)) = 3 / 5 ∧
    encodedColumn (topBottomAssignment false (oneWireBasis true)) = 0 ∧
    encodedColumn (topBottomAssignment true (oneWireBasis false)) = 0 ∧
    encodedColumn (topBottomAssignment true (oneWireBasis true)) = -4 / 5 := by
  exact ⟨encodedColumn_false_zero, encodedColumn_false_one,
    encodedColumn_true_zero, encodedColumn_true_one⟩

/-- The normalized canonical encoding has the same four exact coordinates. -/
theorem encodedState_coordinates :
    encodedState (topBottomAssignment false (oneWireBasis false)) = 3 / 5 ∧
    encodedState (topBottomAssignment false (oneWireBasis true)) = 0 ∧
    encodedState (topBottomAssignment true (oneWireBasis false)) = 0 ∧
    encodedState (topBottomAssignment true (oneWireBasis true)) = -4 / 5 := by
  simpa only [encodedState_apply] using encodedColumn_coordinates

/-! ## Pure non-product witness -/

/-- The canonical realification column cannot factor into pure top and bottom columns. -/
theorem encodedColumn_not_pureTopBottomProduct :
    ¬ IsPureTopBottomProduct encodedColumn := by
  rintro ⟨topFactor, bottomFactor, hfactor⟩
  have h00 : (3 / 5 : ℝ) =
      topFactor false * bottomFactor (oneWireBasis false) := by
    have h := hfactor false (oneWireBasis false)
    rw [encodedColumn_false_zero] at h
    exact h
  have h01 : (0 : ℝ) =
      topFactor false * bottomFactor (oneWireBasis true) := by
    have h := hfactor false (oneWireBasis true)
    rw [encodedColumn_false_one] at h
    exact h
  have h11 : (-4 / 5 : ℝ) =
      topFactor true * bottomFactor (oneWireBasis true) := by
    have h := hfactor true (oneWireBasis true)
    rw [encodedColumn_true_one] at h
    exact h
  have htop : topFactor false ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at h00
    norm_num at h00
  have hbottom : bottomFactor (oneWireBasis true) = 0 :=
    (mul_eq_zero.mp h01.symm).resolve_left htop
  rw [hbottom, mul_zero] at h11
  norm_num at h11

/-- The normalized canonical real state is likewise not a pure top/bottom product. -/
theorem encodedState_not_pureTopBottomProduct :
    ¬ IsPureTopBottomProduct (fun x ↦ encodedState x) := by
  simpa only [encodedState_apply] using encodedColumn_not_pureTopBottomProduct

end NonProductWitness

end QuaternionicComputing.Simulation
