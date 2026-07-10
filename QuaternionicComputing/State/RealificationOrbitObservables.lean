module

public import QuaternionicComputing.State.RealificationOrbit
public import QuaternionicComputing.State.RayObservables

/-!
# Bottom observables of realification sector orbits

A unit complex phase rotates the two realification sectors and can change the
individual doubled-real basis weights.  The sum of the two sector weights over
each source index is invariant.  This file packages exactly that bottom
marginal as a finite distribution and descends it to `RealSectorOrbit`.

No full doubled-target basis distribution is attached to the orbit: that
distribution is not invariant under sector rotation.  Finite events and
deterministic postprocessing are already supplied by the generic
`FiniteDistribution` API and need no orbit-specific wrappers.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.State

universe u

variable {I : Type u}

/-! ## Representative bottom distributions -/

/--
Sector action scales each bottom marginal weight by the complex scalar's norm
square.
-/
theorem realSectorAction_bottomRealWeight (eta : ℂ)
    (w : I ⊕ I → ℝ) (i : I) :
    bottomRealWeight (realSectorAction eta w) i =
      Complex.normSq eta * bottomRealWeight w i := by
  simp [bottomRealWeight, realBasisWeight, basisWeight, realWeight,
    realSectorAction, Complex.normSq_apply]
  ring

/-- A unit complex sector action preserves every bottom marginal weight. -/
theorem realSectorAction_bottomRealWeight_of_normSq_eq_one
    (eta : ℂ) (heta : Complex.normSq eta = 1)
    (w : I ⊕ I → ℝ) (i : I) :
    bottomRealWeight (realSectorAction eta w) i = bottomRealWeight w i := by
  rw [realSectorAction_bottomRealWeight, heta, one_mul]

/--
The normalized bottom marginal distribution of a doubled real state, obtained
by summing its two sector weights over each source index.
-/
def realBottomDistribution [Fintype I]
    (w : RealState (I ⊕ I)) : FiniteDistribution I where
  weight i := bottomRealWeight w i
  nonnegative i := add_nonneg
    (RealState.basisWeight_nonneg w (Sum.inl i))
    (RealState.basisWeight_nonneg w (Sum.inr i))
  normalized := by
    change (∑ i, bottomRealWeight (w : I ⊕ I → ℝ) i) = 1
    calc
      (∑ i, bottomRealWeight (w : I ⊕ I → ℝ) i) =
          realTotalWeight (w : I ⊕ I → ℝ) := by
        simp [realTotalWeight, totalWeight, bottomRealWeight,
          realBasisWeight, basisWeight, realWeight,
          Fintype.sum_sum_type, Finset.sum_add_distrib]
      _ = 1 := w.property

/-- A representative bottom distribution computes by `bottomRealWeight`. -/
@[simp]
theorem realBottomDistribution_weight [Fintype I]
    (w : RealState (I ⊕ I)) (i : I) :
    (realBottomDistribution w).weight i = bottomRealWeight w i :=
  rfl

/-- Sector-phase-equivalent normalized representatives have equal bottom distributions. -/
theorem realBottomDistribution_eq_of_phase [Fintype I]
    {x y : RealState (I ⊕ I)}
    (hxy : RealSectorPhaseEquivalent (x : I ⊕ I → ℝ) y) :
    realBottomDistribution x = realBottomDistribution y := by
  rcases hxy with ⟨eta, heta, hxy⟩
  apply FiniteDistribution.ext
  intro i
  change bottomRealWeight x i = bottomRealWeight y i
  rw [hxy, realSectorAction_bottomRealWeight, heta, one_mul]

/-! ## Descent to real sector orbits -/

namespace RealSectorOrbit

variable [Fintype I]

/-- The normalized bottom marginal distribution of a real sector orbit. -/
def bottomDistribution (r : RealSectorOrbit I) : FiniteDistribution I :=
  lift realBottomDistribution
    (fun _ _ hxy ↦ realBottomDistribution_eq_of_phase hxy) r

/-- Orbit bottom distribution computes on every normalized representative. -/
@[simp]
theorem bottomDistribution_mk (w : RealState (I ⊕ I)) :
    bottomDistribution (mk w) = realBottomDistribution w :=
  rfl

end RealSectorOrbit

/-! ## Canonical-column and source-ray bridges -/

/-- The first canonical realification column has the source complex distribution. -/
@[simp]
theorem realBottomDistribution_realColumn0State [Fintype I]
    (w : ComplexState I) :
    realBottomDistribution (realColumn0State w) =
      FiniteDistribution.ofNormalizedState
        complexWeight complexWeight_nonneg w := by
  apply FiniteDistribution.ext
  intro i
  exact realColumn0_bottomWeight w i

/-- The second canonical realification column has the source complex distribution. -/
@[simp]
theorem realBottomDistribution_realColumn1State [Fintype I]
    (w : ComplexState I) :
    realBottomDistribution (realColumn1State w) =
      FiniteDistribution.ofNormalizedState
        complexWeight complexWeight_nonneg w := by
  apply FiniteDistribution.ext
  intro i
  exact realColumn1_bottomWeight w i

namespace ComplexRay

variable [Fintype I]

/--
Realification into a sector orbit preserves the complete source
computational-basis distribution after the two real sectors are marginalized.
-/
theorem realificationOrbit_distribution (r : ComplexRay I) :
    RealSectorOrbit.bottomDistribution (realificationOrbit r) =
      distribution r := by
  refine inductionOn r ?_
  intro w
  rw [realificationOrbit_mk, RealSectorOrbit.bottomDistribution_mk,
    realBottomDistribution_realColumn0State, distribution_mk]

end ComplexRay

end QuaternionicComputing.State
