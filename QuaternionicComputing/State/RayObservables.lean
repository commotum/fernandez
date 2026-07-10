module

public import QuaternionicComputing.State.Ray
public import QuaternionicComputing.State.DistributionLaws

/-!
# Computational-basis observables of normalized rays

Computational-basis weights, their normalized finite distributions, finite
events, and deterministic classical postprocessing depend only on a normalized
state's physical ray.  This file descends those operations to real sign rays,
complex unit right-phase rays, and quaternionic unit right-phase rays.

These observables deliberately forget phase.  Equality of the descended
distributions is not used to define ray equality, and no claim here concerns
channels, arbitrary effects, or invariance under quantum evolution.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.State

universe u v

/-! ## Real rays -/

namespace RealRay

variable {I : Type u} [Fintype I]

/-- The normalized computational-basis distribution of a real sign ray. -/
def distribution (r : RealRay I) : FiniteDistribution I :=
  lift
    (FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg)
    (fun _ _ h ↦ FiniteDistribution.ext fun i ↦
      signEquivalent_realBasisWeight h i) r

/-- The distribution of a constructed real ray is the distribution of its representative. -/
@[simp]
theorem distribution_mk (a : RealState I) :
    distribution (mk a) =
      FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg a :=
  rfl

/-- The computational-basis weight of one outcome of a real sign ray. -/
def basisWeight (r : RealRay I) (i : I) : ℝ :=
  (distribution r).weight i

/-- A real ray's basis weight computes on any normalized representative. -/
@[simp]
theorem basisWeight_mk (a : RealState I) (i : I) :
    basisWeight (mk a) i = realBasisWeight a i :=
  rfl

/-- The weight field of the descended distribution is the descended basis weight. -/
@[simp]
theorem distribution_weight (r : RealRay I) (i : I) :
    (distribution r).weight i = basisWeight r i :=
  rfl

/-- The probability weight of a finite computational-basis event on a real ray. -/
def eventWeight (r : RealRay I) (event : Finset I) : ℝ :=
  (distribution r).eventWeight event

/-- Real-ray event weight computes on any normalized representative. -/
@[simp]
theorem eventWeight_mk (a : RealState I) (event : Finset I) :
    eventWeight (mk a) event =
      (FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg a).eventWeight event :=
  rfl

/-- Deterministically postprocess the basis distribution of a real ray. -/
def pushforward {J : Type v} [Fintype J]
    (r : RealRay I) (f : I → J) : FiniteDistribution J :=
  (distribution r).pushforward f

/-- Real-ray deterministic postprocessing computes on any representative. -/
@[simp]
theorem pushforward_mk {J : Type v} [Fintype J]
    (a : RealState I) (f : I → J) :
    pushforward (mk a) f =
      (FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg a).pushforward f :=
  rfl

/-- Identity postprocessing leaves a real ray's basis distribution unchanged. -/
@[simp]
theorem pushforward_id (r : RealRay I) :
    pushforward r id = distribution r :=
  FiniteDistribution.pushforward_id _

/-- Successive deterministic postprocessings of a real ray compose. -/
theorem pushforward_comp {J : Type v} {K : Type*}
    [Fintype J] [Fintype K] (r : RealRay I) (f : I → J) (g : J → K) :
    pushforward r (g ∘ f) = (pushforward r f).pushforward g :=
  FiniteDistribution.pushforward_comp _ f g

end RealRay

/-! ## Complex rays -/

namespace ComplexRay

variable {I : Type u} [Fintype I]

/-- The normalized computational-basis distribution of a complex phase ray. -/
def distribution (r : ComplexRay I) : FiniteDistribution I :=
  lift
    (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg)
    (fun _ _ h ↦ FiniteDistribution.ext fun i ↦
      rightPhaseEquivalent_complexBasisWeight h i) r

/-- The distribution of a constructed complex ray is that of its representative. -/
@[simp]
theorem distribution_mk (a : ComplexState I) :
    distribution (mk a) =
      FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a :=
  rfl

/-- The computational-basis weight of one outcome of a complex phase ray. -/
def basisWeight (r : ComplexRay I) (i : I) : ℝ :=
  (distribution r).weight i

/-- A complex ray's basis weight computes on any normalized representative. -/
@[simp]
theorem basisWeight_mk (a : ComplexState I) (i : I) :
    basisWeight (mk a) i = complexBasisWeight a i :=
  rfl

/-- The distribution weight field is the descended complex-ray basis weight. -/
@[simp]
theorem distribution_weight (r : ComplexRay I) (i : I) :
    (distribution r).weight i = basisWeight r i :=
  rfl

/-- The probability weight of a finite computational-basis event on a complex ray. -/
def eventWeight (r : ComplexRay I) (event : Finset I) : ℝ :=
  (distribution r).eventWeight event

/-- Complex-ray event weight computes on any normalized representative. -/
@[simp]
theorem eventWeight_mk (a : ComplexState I) (event : Finset I) :
    eventWeight (mk a) event =
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).eventWeight event :=
  rfl

/-- Deterministically postprocess the basis distribution of a complex ray. -/
def pushforward {J : Type v} [Fintype J]
    (r : ComplexRay I) (f : I → J) : FiniteDistribution J :=
  (distribution r).pushforward f

/-- Complex-ray deterministic postprocessing computes on any representative. -/
@[simp]
theorem pushforward_mk {J : Type v} [Fintype J]
    (a : ComplexState I) (f : I → J) :
    pushforward (mk a) f =
      (FiniteDistribution.ofNormalizedState complexWeight complexWeight_nonneg a).pushforward f :=
  rfl

/-- Identity postprocessing leaves a complex ray's basis distribution unchanged. -/
@[simp]
theorem pushforward_id (r : ComplexRay I) :
    pushforward r id = distribution r :=
  FiniteDistribution.pushforward_id _

/-- Successive deterministic postprocessings of a complex ray compose. -/
theorem pushforward_comp {J : Type v} {K : Type*}
    [Fintype J] [Fintype K] (r : ComplexRay I) (f : I → J) (g : J → K) :
    pushforward r (g ∘ f) = (pushforward r f).pushforward g :=
  FiniteDistribution.pushforward_comp _ f g

end ComplexRay

/-! ## Quaternionic right-phase rays -/

namespace QuaternionRay

variable {I : Type u} [Fintype I]

/-- The normalized computational-basis distribution of a quaternionic right-phase ray. -/
def distribution (r : QuaternionRay I) : FiniteDistribution I :=
  lift
    (FiniteDistribution.ofNormalizedState quaternionWeight quaternionWeight_nonneg)
    (fun _ _ h ↦ FiniteDistribution.ext fun i ↦
      rightPhaseEquivalent_quaternionBasisWeight h i) r

/-- The distribution of a constructed quaternionic ray is that of its representative. -/
@[simp]
theorem distribution_mk (a : QuaternionState I) :
    distribution (mk a) =
      FiniteDistribution.ofNormalizedState quaternionWeight quaternionWeight_nonneg a :=
  rfl

/-- The computational-basis weight of one outcome of a quaternionic ray. -/
def basisWeight (r : QuaternionRay I) (i : I) : ℝ :=
  (distribution r).weight i

/-- A quaternionic ray's basis weight computes on any normalized representative. -/
@[simp]
theorem basisWeight_mk (a : QuaternionState I) (i : I) :
    basisWeight (mk a) i = quaternionBasisWeight a i :=
  rfl

/-- The distribution weight field is the descended quaternionic-ray basis weight. -/
@[simp]
theorem distribution_weight (r : QuaternionRay I) (i : I) :
    (distribution r).weight i = basisWeight r i :=
  rfl

/-- The probability weight of a finite basis event on a quaternionic ray. -/
def eventWeight (r : QuaternionRay I) (event : Finset I) : ℝ :=
  (distribution r).eventWeight event

/-- Quaternionic-ray event weight computes on any normalized representative. -/
@[simp]
theorem eventWeight_mk (a : QuaternionState I) (event : Finset I) :
    eventWeight (mk a) event =
      (FiniteDistribution.ofNormalizedState quaternionWeight quaternionWeight_nonneg a).eventWeight event :=
  rfl

/-- Deterministically postprocess the basis distribution of a quaternionic ray. -/
def pushforward {J : Type v} [Fintype J]
    (r : QuaternionRay I) (f : I → J) : FiniteDistribution J :=
  (distribution r).pushforward f

/-- Quaternionic-ray postprocessing computes on any normalized representative. -/
@[simp]
theorem pushforward_mk {J : Type v} [Fintype J]
    (a : QuaternionState I) (f : I → J) :
    pushforward (mk a) f =
      (FiniteDistribution.ofNormalizedState quaternionWeight quaternionWeight_nonneg a).pushforward f :=
  rfl

/-- Identity postprocessing leaves a quaternionic ray's distribution unchanged. -/
@[simp]
theorem pushforward_id (r : QuaternionRay I) :
    pushforward r id = distribution r :=
  FiniteDistribution.pushforward_id _

/-- Successive deterministic postprocessings of a quaternionic ray compose. -/
theorem pushforward_comp {J : Type v} {K : Type*}
    [Fintype J] [Fintype K] (r : QuaternionRay I) (f : I → J) (g : J → K) :
    pushforward r (g ∘ f) = (pushforward r f).pushforward g :=
  FiniteDistribution.pushforward_comp _ f g

end QuaternionRay

end QuaternionicComputing.State
