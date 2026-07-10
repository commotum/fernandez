module

public import QuaternionicComputing.Circuit.Ordering
public import QuaternionicComputing.State.Unitary

/-!
# Observable order dependence on disjoint quaternionic gates

This file gives a fully unitary, measurement-level witness for quaternionic
circuit order dependence.  The global wire type is `Bool`: `false` and `true`
are two distinct wires.  An `i`-valued rational mixer acts only on the first
wire and a `j`-valued mixer acts only on the second, so their certified supports
are disjoint.

Both chronological orders are legal schedules for the empty precedence
relation.  Nevertheless, the public ordered evaluator produces different
operators.  On the normalized input with amplitudes `3/5` at `00` and
`(4/5)k` at `11`, the output weight at `00` is respectively
`8281/15625` and `1369/15625`.

The construction is an explicit counterexample only.  It does not assert that
all disjoint quaternionic gates are order-sensitive.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion

namespace QuaternionicComputing.Circuit.OrderingWitness

open QuaternionicComputing.State
open QuaternionicComputing.Quaternion

/-! ## Rational one-wire mixers -/

/-- The real diagonal coefficient `3/5`, represented without square roots. -/
def mixerDiagonal : ℍ[ℝ] := ⟨3 / 5, 0, 0, 0⟩

/-- The real off-diagonal magnitude `4/5`. -/
def mixerOffDiagonal : ℍ[ℝ] := ⟨4 / 5, 0, 0, 0⟩

/--
The Boolean `2 × 2` mixer with diagonal `3/5` and both off-diagonal
entries `(4/5)u`.
-/
def boolMixer (u : ℍ[ℝ]) : Matrix Bool Bool ℍ[ℝ] :=
  fun x y ↦ if x = y then mixerDiagonal else mixerOffDiagonal * u

/-- The rational mixer whose off-diagonal quaternionic direction is `i`. -/
def iMixer : Matrix Bool Bool ℍ[ℝ] := boolMixer i

/-- The rational mixer whose off-diagonal quaternionic direction is `j`. -/
def jMixer : Matrix Bool Bool ℍ[ℝ] := boolMixer j

/-- The Boolean `i` mixer is exactly unitary. -/
theorem iMixer_unitary : iMixer ∈ unitary (Matrix Bool Bool ℍ[ℝ]) := by
  constructor <;> ext x y <;> cases x <;> cases y <;>
    simp [iMixer, boolMixer, mixerDiagonal, mixerOffDiagonal,
      Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] <;> norm_num

/-- The Boolean `j` mixer is exactly unitary. -/
theorem jMixer_unitary : jMixer ∈ unitary (Matrix Bool Bool ℍ[ℝ]) := by
  constructor <;> ext x y <;> cases x <;> cases y <;>
    simp [jMixer, boolMixer, mixerDiagonal, mixerOffDiagonal,
      Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] <;> norm_num

/-! A one-wire local basis is `Unit → Bool`; reindex the checked Boolean mixers to it. -/

/-- Identify a Boolean value with the unique bit assignment on one `Unit` wire. -/
def boolToUnitBasis : Bool ≃ BitBasis Unit where
  toFun q := fun _ ↦ q
  invFun x := x ()
  left_inv _ := rfl
  right_inv x := by
    funext u
    cases u
    rfl

/-- Reindex Boolean matrices to one-wire computational-basis matrices. -/
def unitReindexStarMonoidHom :
    Matrix Bool Bool ℍ[ℝ] →⋆* Matrix (BitBasis Unit) (BitBasis Unit) ℍ[ℝ] where
  toFun := Matrix.reindex boolToUnitBasis boolToUnitBasis
  map_one' := map_one (Matrix.reindexRingEquiv ℍ[ℝ] boolToUnitBasis)
  map_mul' A B :=
    map_mul (Matrix.reindexRingEquiv ℍ[ℝ] boolToUnitBasis) A B
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.conjTranspose_reindex boolToUnitBasis boolToUnitBasis A).symm

/-- The genuine one-wire local `i` mixer. -/
def localIMixer : Matrix (BitBasis Unit) (BitBasis Unit) ℍ[ℝ] :=
  unitReindexStarMonoidHom iMixer

/-- The genuine one-wire local `j` mixer. -/
def localJMixer : Matrix (BitBasis Unit) (BitBasis Unit) ℍ[ℝ] :=
  unitReindexStarMonoidHom jMixer

/-- Reindexing preserves unitarity of the local `i` mixer. -/
theorem localIMixer_unitary :
    localIMixer ∈ unitary (Matrix (BitBasis Unit) (BitBasis Unit) ℍ[ℝ]) :=
  Unitary.map_mem unitReindexStarMonoidHom iMixer_unitary

/-- Reindexing preserves unitarity of the local `j` mixer. -/
theorem localJMixer_unitary :
    localJMixer ∈ unitary (Matrix (BitBasis Unit) (BitBasis Unit) ℍ[ℝ]) :=
  Unitary.map_mem unitReindexStarMonoidHom jMixer_unitary

/-! ## Disjoint placement on two global wires -/

/-- Select global wire `false` locally and leave wire `true` complementary. -/
def firstSplit : Unit ⊕ Unit ≃ Bool where
  toFun
    | Sum.inl _ => false
    | Sum.inr _ => true
  invFun
    | false => Sum.inl ()
    | true => Sum.inr ()
  left_inv x := by rcases x with (_ | _) <;> rfl
  right_inv x := by cases x <;> rfl

/-- Select global wire `true` locally and leave wire `false` complementary. -/
def secondSplit : Unit ⊕ Unit ≃ Bool where
  toFun
    | Sum.inl _ => true
    | Sum.inr _ => false
  invFun
    | false => Sum.inr ()
    | true => Sum.inl ()
  left_inv x := by rcases x with (_ | _) <;> rfl
  right_inv x := by cases x <;> rfl

/-- The `i` mixer placed only on global wire `false`. -/
def iGate : PlacedGate ℍ[ℝ] Bool :=
  PlacedGate.ofSplit firstSplit localIMixer

/-- The `j` mixer placed only on global wire `true`. -/
def jGate : PlacedGate ℍ[ℝ] Bool :=
  PlacedGate.ofSplit secondSplit localJMixer

/-- The first placed gate is locally unitary. -/
theorem iGate_locallyUnitary : iGate.IsLocallyUnitary :=
  localIMixer_unitary

/-- The second placed gate is locally unitary. -/
theorem jGate_locallyUnitary : jGate.IsLocallyUnitary :=
  localJMixer_unitary

/-- The first placed gate has exactly one local wire. -/
@[simp]
theorem iGate_localArity : iGate.localArity = 1 := by
  change Fintype.card Unit = 1
  simp

/-- The second placed gate has exactly one local wire. -/
@[simp]
theorem jGate_localArity : jGate.localArity = 1 := by
  change Fintype.card Unit = 1
  simp

/-- The two locality certificates select disjoint global supports. -/
theorem gate_supports_disjoint : Disjoint iGate.support jGate.support := by
  rw [Finset.disjoint_left]
  intro w hi hj
  rw [PlacedGate.mem_support_iff] at hi hj
  rcases hi with ⟨u, hu⟩
  rcases hj with ⟨v, hv⟩
  change firstSplit (Sum.inl u) = w at hu
  change secondSplit (Sum.inl v) = w at hv
  have hwFalse : w = false := by
    simpa [firstSplit] using hu.symm
  have hwTrue : w = true := by
    simpa [secondSplit] using hv.symm
  simp [hwFalse] at hwTrue

@[simp]
theorem complementBits_firstSplit_eq (x y : BitBasis Bool) :
    complementBits firstSplit x = complementBits firstSplit y ↔
      x true = y true := by
  constructor
  · intro h
    exact congrFun h ()
  · intro h
    funext u
    cases u
    simpa [complementBits_apply, firstSplit] using h

@[simp]
theorem complementBits_secondSplit_eq (x y : BitBasis Bool) :
    complementBits secondSplit x = complementBits secondSplit y ↔
      x false = y false := by
  constructor
  · intro h
    exact congrFun h ()
  · intro h
    funext u
    cases u
    simpa [complementBits_apply, secondSplit] using h

/-- Exact global entries of the first placed gate. -/
@[simp]
theorem iGate_denote_apply (x y : BitBasis Bool) :
    iGate.denote x y =
      if x true = y true then iMixer (x false) (y false) else 0 := by
  change place firstSplit localIMixer x y = _
  rw [place_apply]
  by_cases h : x true = y true
  · have hc : complementBits firstSplit x = complementBits firstSplit y :=
      (complementBits_firstSplit_eq x y).2 h
    rw [if_pos hc, if_pos h]
    simp [localIMixer, unitReindexStarMonoidHom, Matrix.reindex_apply,
      boolToUnitBasis, localBits_apply, firstSplit]
  · have hc : complementBits firstSplit x ≠ complementBits firstSplit y := by
      simpa using h
    rw [if_neg hc, if_neg h]

/-- Exact global entries of the second placed gate. -/
@[simp]
theorem jGate_denote_apply (x y : BitBasis Bool) :
    jGate.denote x y =
      if x false = y false then jMixer (x true) (y true) else 0 := by
  change place secondSplit localJMixer x y = _
  rw [place_apply]
  by_cases h : x false = y false
  · have hc : complementBits secondSplit x = complementBits secondSplit y :=
      (complementBits_secondSplit_eq x y).2 h
    rw [if_pos hc, if_pos h]
    simp [localJMixer, unitReindexStarMonoidHom, Matrix.reindex_apply,
      boolToUnitBasis, localBits_apply, secondSplit]
  · have hc : complementBits secondSplit x ≠ complementBits secondSplit y := by
      simpa using h
    rw [if_neg hc, if_neg h]

/-! ## The normalized interference input -/

/-- A two-wire basis assignment with values `x0` on `false` and `x1` on `true`. -/
def basis (x0 x1 : Bool) : BitBasis Bool :=
  fun w ↦ if w then x1 else x0

@[simp] theorem basis_false (x0 x1 : Bool) : basis x0 x1 false = x0 := rfl
@[simp] theorem basis_true (x0 x1 : Bool) : basis x0 x1 true = x1 := rfl

@[simp]
theorem basis_eq_iff (x0 x1 y0 y1 : Bool) :
    basis x0 x1 = basis y0 y1 ↔ x0 = y0 ∧ x1 = y1 := by
  constructor
  · intro h
    exact ⟨congrFun h false, congrFun h true⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The `00` global basis assignment. -/
def basis00 : BitBasis Bool := basis false false

/-- The `01` global basis assignment. -/
def basis01 : BitBasis Bool := basis false true

/-- The `10` global basis assignment. -/
def basis10 : BitBasis Bool := basis true false

/-- The `11` global basis assignment. -/
def basis11 : BitBasis Bool := basis true true

/-- Enumerate the four global basis assignments by their two Boolean values. -/
def pairToBasis : Bool × Bool ≃ BitBasis Bool where
  toFun p := basis p.1 p.2
  invFun x := (x false, x true)
  left_inv p := by rcases p with ⟨x, y⟩; cases x <;> cases y <;> rfl
  right_inv x := by
    funext w
    cases w <;> rfl

/-- Rewrite a finite sum over the four two-wire computational-basis assignments. -/
theorem sum_bitBasisBool {M : Type*} [AddCommMonoid M]
    (f : BitBasis Bool → M) :
    (∑ x, f x) =
      (f basis00 + f basis01) + (f basis10 + f basis11) := by
  rw [← pairToBasis.sum_comp f]
  simp [Fintype.sum_prod_type, pairToBasis, basis00, basis01, basis10,
    basis11]
  ac_rfl

/--
The raw input column: amplitude `3/5` at `00`, amplitude `(4/5)k` at `11`,
and zero elsewhere.
-/
def inputColumn (x : BitBasis Bool) : ℍ[ℝ] :=
  if x = basis00 then mixerDiagonal
  else if x = basis11 then mixerOffDiagonal * k
  else 0

/-- The witness input column has exact total quaternionic weight one. -/
theorem inputColumn_normalization : quaternionTotalWeight inputColumn = 1 := by
  change (∑ x, _root_.Quaternion.normSq (inputColumn x)) = 1
  rw [sum_bitBasisBool]
  simp [inputColumn, basis00, basis01, basis10, basis11, mixerDiagonal,
    mixerOffDiagonal, _root_.Quaternion.normSq_def']
  norm_num

/-- The explicitly normalized global two-wire witness state. -/
def inputState : QuaternionState (BitBasis Bool) :=
  ⟨inputColumn, inputColumn_normalization⟩

/-! ## Two legal chronological orders -/

/-- Chronological execution with the `i` gate first and the `j` gate second. -/
def iThenJ : OrderedCircuit ℍ[ℝ] Bool := [iGate, jGate]

/-- Chronological execution with the `j` gate first and the `i` gate second. -/
def jThenI : OrderedCircuit ℍ[ℝ] Bool := [jGate, iGate]

/-- The two gate occurrences have no precedence constraint. -/
def noPrecedence (_ _ : Bool) : Prop := False

/-- The two gate occurrences are incomparable under `noPrecedence`. -/
theorem occurrences_incomparable :
    ¬ noPrecedence false true ∧ ¬ noPrecedence true false := by
  simp [noPrecedence]

/-- Assign occurrence `false` to the `i` gate and occurrence `true` to the `j` gate. -/
def gateFamily : Bool → PlacedGate ℍ[ℝ] Bool
  | false => iGate
  | true => jGate

/-- The `i`-then-`j` order is a legal schedule. -/
def iThenJSchedule : LegalSchedule Bool noPrecedence where
  order := [false, true]
  nodup := by decide
  complete q := by cases q <;> simp
  respects h := h.elim

/-- The `j`-then-`i` order is also a legal schedule. -/
def jThenISchedule : LegalSchedule Bool noPrecedence where
  order := [true, false]
  nodup := by decide
  complete q := by cases q <;> simp
  respects h := h.elim

/-- Instantiating the first legal schedule gives the advertised chronological circuit. -/
@[simp]
theorem scheduledCircuit_iThenJ :
    iThenJSchedule.scheduledCircuit gateFamily = iThenJ := rfl

/-- Instantiating the second legal schedule gives the reverse chronological circuit. -/
@[simp]
theorem scheduledCircuit_jThenI :
    jThenISchedule.scheduledCircuit gateFamily = jThenI := rfl

/-- The first chronological circuit is locally unitary. -/
theorem iThenJ_locallyUnitary : iThenJ.IsLocallyUnitary := by
  simp [iThenJ, OrderedCircuit.IsLocallyUnitary, iGate_locallyUnitary,
    jGate_locallyUnitary]

/-- The reverse chronological circuit is locally unitary. -/
theorem jThenI_locallyUnitary : jThenI.IsLocallyUnitary := by
  simp [jThenI, OrderedCircuit.IsLocallyUnitary, iGate_locallyUnitary,
    jGate_locallyUnitary]

/-! ## Exact operator and observable separation -/

private theorem iThenJ_scalar_calculation :
    mixerDiagonal * (mixerDiagonal * mixerDiagonal) +
        mixerOffDiagonal * j *
          (mixerOffDiagonal * i * (mixerOffDiagonal * k)) =
      (⟨91 / 125, 0, 0, 0⟩ : ℍ[ℝ]) := by
  ext <;> norm_num [mixerDiagonal, mixerOffDiagonal]

private theorem jThenI_scalar_calculation :
    mixerDiagonal * (mixerDiagonal * mixerDiagonal) +
        mixerOffDiagonal * i *
          (mixerOffDiagonal * j * (mixerOffDiagonal * k)) =
      (⟨-37 / 125, 0, 0, 0⟩ : ℍ[ℝ]) := by
  ext <;> norm_num [mixerDiagonal, mixerOffDiagonal]

/-- The `00` output amplitude for chronological `i` then `j` is `91/125`. -/
theorem iThenJ_output_basis00 :
    (OrderedCircuit.eval iThenJ *ᵥ inputColumn) basis00 =
      (⟨91 / 125, 0, 0, 0⟩ : ℍ[ℝ]) := by
  rw [show OrderedCircuit.eval iThenJ = jGate.denote * iGate.denote by
    simp [iThenJ]]
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [sum_bitBasisBool]
  simpa [iGate_denote_apply, jGate_denote_apply, inputColumn, iMixer, jMixer,
    boolMixer, basis00, basis01, basis10, basis11] using
    iThenJ_scalar_calculation

/-- The `00` output amplitude for chronological `j` then `i` is `-37/125`. -/
theorem jThenI_output_basis00 :
    (OrderedCircuit.eval jThenI *ᵥ inputColumn) basis00 =
      (⟨-37 / 125, 0, 0, 0⟩ : ℍ[ℝ]) := by
  rw [show OrderedCircuit.eval jThenI = iGate.denote * jGate.denote by
    simp [jThenI]]
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [sum_bitBasisBool]
  simpa [iGate_denote_apply, jGate_denote_apply, inputColumn, iMixer, jMixer,
    boolMixer, basis00, basis01, basis10, basis11] using
    jThenI_scalar_calculation

/-- The two public ordered-circuit operators are different. -/
theorem circuit_operators_ne :
    OrderedCircuit.eval iThenJ ≠ OrderedCircuit.eval jThenI := by
  intro h
  have hv := congrArg
    (fun M : Matrix (BitBasis Bool) (BitBasis Bool) ℍ[ℝ] ↦
      (M *ᵥ inputColumn) basis00) h
  rw [iThenJ_output_basis00, jThenI_output_basis00] at hv
  have hre := congrArg QuaternionAlgebra.re hv
  norm_num at hre

/-- The two legal schedules therefore have different public scheduled evaluations. -/
theorem scheduled_operators_ne :
    iThenJSchedule.scheduledEval gateFamily ≠
      jThenISchedule.scheduledEval gateFamily := by
  simpa [LegalSchedule.scheduledEval] using circuit_operators_ne

/-- The normalized output of the `i`-then-`j` circuit. -/
def iThenJOutput : QuaternionState (BitBasis Bool) :=
  QuaternionState.evolveUnitary inputState (OrderedCircuit.eval iThenJ)
    (OrderedCircuit.eval_mem_unitary iThenJ_locallyUnitary)

/-- The normalized output of the `j`-then-`i` circuit. -/
def jThenIOutput : QuaternionState (BitBasis Bool) :=
  QuaternionState.evolveUnitary inputState (OrderedCircuit.eval jThenI)
    (OrderedCircuit.eval_mem_unitary jThenI_locallyUnitary)

@[simp]
theorem iThenJOutput_basis00 :
    iThenJOutput basis00 = (⟨91 / 125, 0, 0, 0⟩ : ℍ[ℝ]) :=
  iThenJ_output_basis00

@[simp]
theorem jThenIOutput_basis00 :
    jThenIOutput basis00 = (⟨-37 / 125, 0, 0, 0⟩ : ℍ[ℝ]) :=
  jThenI_output_basis00

/-- The first legal order gives exact `00` weight `8281/15625`. -/
theorem iThenJOutput_basis00_weight :
    quaternionBasisWeight iThenJOutput basis00 = 8281 / 15625 := by
  simp [quaternionBasisWeight, basisWeight, quaternionWeight,
    _root_.Quaternion.normSq_def']
  norm_num

/-- The reverse legal order gives exact `00` weight `1369/15625`. -/
theorem jThenIOutput_basis00_weight :
    quaternionBasisWeight jThenIOutput basis00 = 1369 / 15625 := by
  simp [quaternionBasisWeight, basisWeight, quaternionWeight,
    _root_.Quaternion.normSq_def']
  norm_num

/-- The two legal orders have observably different computational-basis outcomes. -/
theorem output_basis00_weight_ne :
    quaternionBasisWeight iThenJOutput basis00 ≠
      quaternionBasisWeight jThenIOutput basis00 := by
  rw [iThenJOutput_basis00_weight, jThenIOutput_basis00_weight]
  norm_num

end QuaternionicComputing.Circuit.OrderingWitness
