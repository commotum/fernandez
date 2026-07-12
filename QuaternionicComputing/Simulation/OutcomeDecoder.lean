module

public import QuaternionicComputing.State.Distribution
public import QuaternionicComputing.Circuit.AddedWire

/-!
# Explicit finite-outcome decoders for added simulation wires

This scalar-independent leaf decodes the computational-basis outcome of one
or two distinguished added wires by summing the corresponding target weights.
The one-wire distribution decoder is proved to be exactly deterministic
pushforward through `Circuit.tailBits`; its direct two-sector definition keeps
the false/true marginal policy visible at the point-weight level.

The two-wire decoder removes the outer added wire first and the inner added
wire second, matching quaternion-to-complex followed by complex-to-real
simulation. Weight decoders accept arbitrary real-valued functions and make no
normalization claim. Distribution decoders consume genuine normalized finite
distributions and preserve that normalization. None of these definitions is a
quantum partial trace or a claim about product states, mixed states, channels,
physical effects, randomized postprocessing, or runtime.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.Simulation

open QuaternionicComputing.Circuit
open QuaternionicComputing.State

universe u

/-! ## Generic and one-added-wire decoders -/

/-- Sum the two target-sector weights lying above one source outcome. -/
def sumSectorWeightDecoder {I : Type u}
    (targetWeight : I ⊕ I → ℝ) (outcome : I) : ℝ :=
  targetWeight (Sum.inl outcome) + targetWeight (Sum.inr outcome)

/--
Forget one distinguished added wire at the weight-function level by summing
its explicit false and true assignments above each tail assignment.
-/
def addedWireWeightDecoder {W : Type u}
    (targetWeight : BitBasis (AddedWire W) → ℝ)
    (outcome : BitBasis W) : ℝ :=
  targetWeight (addedBasisEquiv W (Sum.inl outcome)) +
    targetWeight (addedBasisEquiv W (Sum.inr outcome))

/--
Decode a normalized full added-wire distribution to its normalized tail
distribution by summing the two explicit top-bit sectors.
-/
def addedWireDistributionDecoder {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire W))) :
    FiniteDistribution (BitBasis W) where
  weight := addedWireWeightDecoder target.weight
  nonnegative outcome := add_nonneg
    (target.nonnegative (addedBasisEquiv W (Sum.inl outcome)))
    (target.nonnegative (addedBasisEquiv W (Sum.inr outcome)))
  normalized := by
    calc
      (∑ outcome : BitBasis W,
          addedWireWeightDecoder target.weight outcome) =
          ∑ sector : BitBasis W ⊕ BitBasis W,
            target.weight (addedBasisEquiv W sector) := by
        simp [addedWireWeightDecoder, Fintype.sum_sum_type,
          Finset.sum_add_distrib]
      _ = ∑ targetOutcome : BitBasis (AddedWire W),
          target.weight targetOutcome :=
        (addedBasisEquiv W).sum_comp target.weight
      _ = 1 := target.normalized

/-- The one-wire distribution decoder computes by its point-weight decoder. -/
@[simp]
theorem addedWireDistributionDecoder_weight {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire W)))
    (outcome : BitBasis W) :
    (addedWireDistributionDecoder target).weight outcome =
      addedWireWeightDecoder target.weight outcome :=
  rfl

/-- Compatibility required by `DecodedDistributionAgreement` point weights. -/
theorem addedWireDistributionDecoder_compat {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire W))) :
    (addedWireDistributionDecoder target).weight =
      addedWireWeightDecoder target.weight :=
  rfl

@[simp]
private theorem tailBits_addedBasisEquiv_inl {W : Type u}
    (outcome : BitBasis W) :
    tailBits (addedBasisEquiv W (Sum.inl outcome)) = outcome := by
  funext wire
  simp [tailBits]

@[simp]
private theorem tailBits_addedBasisEquiv_inr {W : Type u}
    (outcome : BitBasis W) :
    tailBits (addedBasisEquiv W (Sum.inr outcome)) = outcome := by
  funext wire
  simp [tailBits]

/--
The explicit false/true decoder is exactly deterministic marginalization by
forgetting the distinguished top bit.
-/
theorem addedWireDistributionDecoder_eq_pushforward
    {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire W))) :
    addedWireDistributionDecoder target = target.pushforward tailBits := by
  classical
  apply FiniteDistribution.ext
  intro outcome
  rw [FiniteDistribution.pushforward_weight]
  change
    target.weight (addedBasisEquiv W (Sum.inl outcome)) +
        target.weight (addedBasisEquiv W (Sum.inr outcome)) =
      ∑ targetOutcome with tailBits targetOutcome = outcome,
        target.weight targetOutcome
  rw [Finset.sum_filter]
  rw [← (addedBasisEquiv W).sum_comp
    (fun targetOutcome ↦
      if tailBits targetOutcome = outcome then target.weight targetOutcome
      else 0)]
  simp [Fintype.sum_sum_type]

/-! ## Two-added-wire decoders -/

/--
Decode two added-wire weight layers in construction order: first the outer
wire, then the inner wire.
-/
def twoAddedWireWeightDecoder {W : Type u}
    (targetWeight : BitBasis (AddedWire (AddedWire W)) → ℝ)
    (outcome : BitBasis W) : ℝ :=
  addedWireWeightDecoder (W := W)
    (addedWireWeightDecoder (W := AddedWire W) targetWeight) outcome

/--
Decode a normalized two-added-wire distribution by composing the outer and
inner one-wire distribution decoders in that order.
-/
def twoAddedWireDistributionDecoder {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire (AddedWire W)))) :
    FiniteDistribution (BitBasis W) :=
  addedWireDistributionDecoder (W := W)
    (addedWireDistributionDecoder (W := AddedWire W) target)

/-- The two-wire distribution decoder computes by the nested weight decoder. -/
@[simp]
theorem twoAddedWireDistributionDecoder_weight {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire (AddedWire W))))
    (outcome : BitBasis W) :
    (twoAddedWireDistributionDecoder target).weight outcome =
      twoAddedWireWeightDecoder target.weight outcome :=
  rfl

/-- Compatibility required by composed decoded-distribution agreements. -/
theorem twoAddedWireDistributionDecoder_compat {W : Type u} [Finite W]
    (target : FiniteDistribution (BitBasis (AddedWire (AddedWire W)))) :
    (twoAddedWireDistributionDecoder target).weight =
      twoAddedWireWeightDecoder target.weight :=
  rfl

end QuaternionicComputing.Simulation
