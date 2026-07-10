module

public import QuaternionicComputing.Circuit.Basic
public import QuaternionicComputing.Scalar.Quaternion

/-!
# Order-sensitivity sanity check

This narrow audit leaf gives a concrete noncommutative witness for the public
ordered-circuit evaluator.  Keeping the witness here leaves `Circuit.Basic`
scalar-generic while still making accidental reversal of chronological
multiplication mechanically detectable.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Circuit.OrderSanity

open QuaternionicComputing.Quaternion

/-- The unique split of a zero-wire local system and zero-wire complement. -/
def emptySplit : Empty ⊕ Empty ≃ Empty :=
  Equiv.sumEmpty Empty Empty

/-- A zero-wire local matrix whose unique entry is the quaternionic unit `i`. -/
def iLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℍ[ℝ] :=
  fun _ _ ↦ i

/-- A zero-wire local matrix whose unique entry is the quaternionic unit `j`. -/
def jLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℍ[ℝ] :=
  fun _ _ ↦ j

/-- The placed `i` gate used by the order sanity check. -/
def iGate : PlacedGate ℍ[ℝ] Empty :=
  PlacedGate.ofSplit emptySplit iLocal

/-- The placed `j` gate used by the order sanity check. -/
def jGate : PlacedGate ℍ[ℝ] Empty :=
  PlacedGate.ofSplit emptySplit jLocal

/-- The two stored local matrices genuinely fail to commute. -/
theorem jLocal_mul_iLocal_ne_iLocal_mul_jLocal :
    jLocal * iLocal ≠ iLocal * jLocal := by
  intro h
  let z : BitBasis Empty := fun x ↦ nomatch x
  have hz := congrFun (congrFun h z) z
  have hk : (-k : ℍ[ℝ]) = k := by
    simpa [iLocal, jLocal, Matrix.mul_apply] using hz
  have hkCoord := congrArg QuaternionAlgebra.imK hk
  norm_num at hkCoord

/-- The corresponding placed global matrices genuinely fail to commute. -/
theorem jGate_denote_mul_iGate_denote_ne_iGate_denote_mul_jGate_denote :
    jGate.denote * iGate.denote ≠ iGate.denote * jGate.denote := by
  change
    place emptySplit jLocal * place emptySplit iLocal ≠
      place emptySplit iLocal * place emptySplit jLocal
  rw [← place_mul, ← place_mul]
  exact (place_injective emptySplit).ne jLocal_mul_iLocal_ne_iLocal_mul_jLocal

/--
The actual public evaluator distinguishes chronological `[i, j]` from
chronological `[j, i]`: the former denotes `j * i`, the latter `i * j`.
This theorem fails if circuit multiplication order is accidentally reversed.
-/
theorem eval_i_then_j_ne_eval_j_then_i :
    OrderedCircuit.eval [iGate, jGate] ≠ OrderedCircuit.eval [jGate, iGate] :=
  OrderedCircuit.eval_pair_ne_swap_of_not_commute iGate jGate
    jGate_denote_mul_iGate_denote_ne_iGate_denote_mul_jGate_denote

end QuaternionicComputing.Circuit.OrderSanity
