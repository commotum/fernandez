module

public import QuaternionicComputing.State.RealificationOrbit
public import QuaternionicComputing.State.RealificationOrbitObservables
public import QuaternionicComputing.State.RealificationOrbitBoundary

/-!
# Realification-sector-orbit audit

This non-root diagnostic leaf gives named downstream consumers for every
stable declaration introduced by Goal 2 Stage 4C.  The aggregate consumers
cover the sector action, orbit relation, normalized quotient/equivalence,
bottom-marginal observables, and the exact ordinary-real-ray no-descent
boundary.

Concrete `Unit` examples separate the relevant notions: amplitudes `1` and
`I` are the same complex ray and the same real sector orbit, but their first
realification columns are different ordinary real rays with different full
doubled-real basis distributions.  Marginalizing the two real sectors restores
the same bottom distribution.  The public root deliberately does not import
this audit leaf.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.State.RealificationOrbitAudit

/-! ## Complete sector-action consumer -/

/-- Complete named consumer for all 28 sector-action and normalized-top declarations. -/
theorem sectorAction_api
    (w : Unit ⊕ Unit → ℝ) (x : RealState (Unit ⊕ Unit))
    (v : ComplexState Unit) (eta theta : ℂ)
    (heta : Complex.normSq eta = 1)
    (htheta : Complex.normSq theta = 1) :
    realSectorAction eta w = realSectorAction eta w ∧
      realSectorAction eta w (Sum.inl ()) =
        eta.re * w (Sum.inl ()) + eta.im * w (Sum.inr ()) ∧
      realSectorAction eta w (Sum.inr ()) =
        -eta.im * w (Sum.inl ()) + eta.re * w (Sum.inr ()) ∧
      realSectorAction 1 w = w ∧
      realSectorAction eta (realSectorAction theta w) =
        realSectorAction (eta * theta) w ∧
      realSectorAction eta (realSectorAction theta w) =
        realSectorAction (theta * eta) w ∧
      realSectorAction Complex.I w =
        Sum.elim (fun i ↦ w (Sum.inr i)) (fun i ↦ -w (Sum.inl i)) ∧
      realSectorAction eta (realColumn0 v) =
        realColumn0 (fun i ↦ v i * eta) ∧
      realSectorAction eta (realColumn1 v) =
        realColumn1 (fun i ↦ v i * eta) ∧
      realColumn0 (fun i ↦ v i * eta) =
        realTopCombination eta.re (-eta.im) v ∧
      realColumn1 (fun i ↦ v i * eta) =
        realTopCombination eta.im eta.re v ∧
      realTotalWeight (realSectorAction eta w) =
        Complex.normSq eta * realTotalWeight w ∧
      realTotalWeight (realSectorAction eta w) = realTotalWeight w ∧
      RealState.sectorRotation x eta heta =
        RealState.sectorRotation x eta heta ∧
      RealState.sectorRotation x eta heta (Sum.inl ()) =
        realSectorAction eta x (Sum.inl ()) ∧
      RealState.sectorRotation x 1 (by simp) = x ∧
      RealState.sectorRotation
          (RealState.sectorRotation x theta htheta) eta heta =
        RealState.sectorRotation x (eta * theta) (by
          rw [Complex.normSq_mul, heta, htheta, one_mul]) ∧
      RealState.sectorRotation
          (RealState.sectorRotation x theta htheta) eta heta =
        RealState.sectorRotation x (theta * eta) (by
          rw [Complex.normSq_mul, htheta, heta, one_mul]) ∧
      realPhaseTop0 eta heta = realPhaseTop0 eta heta ∧
      realPhaseTop0 eta heta false = eta.re ∧
      realPhaseTop0 eta heta true = -eta.im ∧
      realPhaseTop1 eta heta = realPhaseTop1 eta heta ∧
      realPhaseTop1 eta heta false = eta.im ∧
      realPhaseTop1 eta heta true = eta.re ∧
      realColumn0State (ComplexState.rightPhase v eta heta) =
        RealState.sectorRotation (realColumn0State v) eta heta ∧
      realColumn1State (ComplexState.rightPhase v eta heta) =
        RealState.sectorRotation (realColumn1State v) eta heta ∧
      realColumn0State (ComplexState.rightPhase v eta heta) =
        realTopState (realPhaseTop0 eta heta) v ∧
      realColumn1State (ComplexState.rightPhase v eta heta) =
        realTopState (realPhaseTop1 eta heta) v := by
  exact ⟨rfl,
    realSectorAction_inl eta w (),
    realSectorAction_inr eta w (),
    realSectorAction_one w,
    realSectorAction_mul eta theta w,
    realSectorAction_comp_right theta eta w,
    realSectorAction_I w,
    realSectorAction_realColumn0 eta v,
    realSectorAction_realColumn1 eta v,
    realColumn0_right_mul eta v,
    realColumn1_right_mul eta v,
    realSectorAction_realTotalWeight eta w,
    realSectorAction_realTotalWeight_of_normSq_eq_one eta heta w,
    rfl,
    RealState.sectorRotation_apply x eta heta (Sum.inl ()),
    RealState.sectorRotation_one x,
    RealState.sectorRotation_mul x eta theta heta htheta,
    RealState.sectorRotation_comp_right x theta eta htheta heta,
    rfl,
    realPhaseTop0_false eta heta,
    realPhaseTop0_true eta heta,
    rfl,
    realPhaseTop1_false eta heta,
    realPhaseTop1_true eta heta,
    realColumn0State_rightPhase v eta heta,
    realColumn1State_rightPhase v eta heta,
    realColumn0State_rightPhase_eq_realTopState v eta heta,
    realColumn1State_rightPhase_eq_realTopState v eta heta⟩

/-! ## Complete relation consumer -/

/-- Complete named consumer for all 13 raw relation and decoder declarations. -/
theorem sectorRelation_api
    (x y z : Unit ⊕ Unit → ℝ)
    (hxy : RealSectorPhaseEquivalent x y)
    (hyz : RealSectorPhaseEquivalent y z)
    (v q : Unit → ℂ) (a b : ComplexState Unit)
    (hsign : QuaternionicComputing.Real.SignEquivalent x y) :
    (RealSectorPhaseEquivalent x y ↔
      ∃ eta : ℂ, Complex.normSq eta = 1 ∧
        x = realSectorAction eta y) ∧
      RealSectorPhaseEquivalent x x ∧
      RealSectorPhaseEquivalent y x ∧
      RealSectorPhaseEquivalent x z ∧
      RealSectorPhaseEquivalent x x ∧
      realColumn0 (complexOfRealColumn0 x) = x ∧
      complexOfRealColumn0 (realSectorAction Complex.I x) =
        (fun i ↦ complexOfRealColumn0 x i * Complex.I) ∧
      (RealSectorPhaseEquivalent x y ↔
        QuaternionicComputing.Complex.RightPhaseEquivalent
          (complexOfRealColumn0 x) (complexOfRealColumn0 y)) ∧
      (RealSectorPhaseEquivalent (realColumn0 v) (realColumn0 q) ↔
        QuaternionicComputing.Complex.RightPhaseEquivalent v q) ∧
      (RealSectorPhaseEquivalent (realColumn1 v) (realColumn1 q) ↔
        QuaternionicComputing.Complex.RightPhaseEquivalent v q) ∧
      (RealSectorPhaseEquivalent
          (realColumn0State a : Unit ⊕ Unit → ℝ) (realColumn0State b) ↔
        QuaternionicComputing.Complex.RightPhaseEquivalent
          (a : Unit → ℂ) b) ∧
      (RealSectorPhaseEquivalent
          (realColumn1State a : Unit ⊕ Unit → ℝ) (realColumn1State b) ↔
        QuaternionicComputing.Complex.RightPhaseEquivalent
          (a : Unit → ℂ) b) ∧
      RealSectorPhaseEquivalent x y := by
  exact ⟨Iff.rfl,
    realSectorPhaseEquivalent_refl x,
    realSectorPhaseEquivalent_symm hxy,
    realSectorPhaseEquivalent_trans hxy hyz,
    realSectorPhaseEquivalent_equivalence.1 x,
    realColumn0_complexOfRealColumn0 x,
    complexOfRealColumn0_realSectorAction Complex.I x,
    realSectorPhaseEquivalent_iff_decode_rightPhaseEquivalent,
    realColumn0_phaseEquivalent_iff_rightPhaseEquivalent,
    realColumn1_phaseEquivalent_iff_rightPhaseEquivalent,
    realColumn0State_phaseEquivalent_iff_rightPhaseEquivalent,
    realColumn1State_phaseEquivalent_iff_rightPhaseEquivalent,
    signEquivalent_realSectorPhaseEquivalent hsign⟩

/-! ## Complete quotient and equivalence consumer -/

/-- Complete named consumer for all 25 normalized orbit declarations. -/
theorem sectorOrbit_api
    (r : RealSectorOrbit Unit) (w x : RealState (Unit ⊕ Unit))
    (c : ComplexState Unit) (q : ComplexRay Unit) (top : Rebit)
    (f g : RealSectorOrbit Unit → ℝ)
    (hfg : ∀ y : RealState (Unit ⊕ Unit),
      f (RealSectorOrbit.mk y) = g (RealSectorOrbit.mk y)) :
    ((realSectorOrbitSetoid Unit) w x ↔
        RealSectorPhaseEquivalent (w : Unit ⊕ Unit → ℝ) x) ∧
      RealSectorOrbit Unit = Quotient (realSectorOrbitSetoid Unit) ∧
      RealSectorOrbit.mk w = Quotient.mk (realSectorOrbitSetoid Unit) w ∧
      (RealSectorOrbit.mk w = RealSectorOrbit.mk x ↔
        RealSectorPhaseEquivalent (w : Unit ⊕ Unit → ℝ) x) ∧
      (∃ y : RealState (Unit ⊕ Unit), RealSectorOrbit.mk y = r) ∧
      r = r ∧
      RealSectorOrbit.lift
          (fun _ : RealState (Unit ⊕ Unit) ↦ (0 : ℝ))
          (fun _ _ _ ↦ rfl) r = 0 ∧
      RealSectorOrbit.lift
          (fun _ : RealState (Unit ⊕ Unit) ↦ (0 : ℝ))
          (fun _ _ _ ↦ rfl) (RealSectorOrbit.mk w) = 0 ∧
      f = g ∧
      complexStateOfRealColumn0 w () = complexOfRealColumn0 w () ∧
      complexStateOfRealColumn0 (realColumn0State c) = c ∧
      realColumn0State (complexStateOfRealColumn0 w) = w ∧
      (realColumn0StateEquiv (I := Unit)) c = realColumn0State c ∧
      ComplexRay.realificationOrbit q = ComplexRay.realificationOrbit q ∧
      ComplexRay.realificationOrbit (ComplexRay.mk c) =
        RealSectorOrbit.mk (realColumn0State c) ∧
      RealSectorOrbit.toComplexRay r = RealSectorOrbit.toComplexRay r ∧
      RealSectorOrbit.toComplexRay (RealSectorOrbit.mk w) =
        ComplexRay.mk (complexStateOfRealColumn0 w) ∧
      RealSectorOrbit.toComplexRay (ComplexRay.realificationOrbit q) = q ∧
      ComplexRay.realificationOrbit (RealSectorOrbit.toComplexRay r) = r ∧
      (complexRayEquivRealSectorOrbit (I := Unit)) (ComplexRay.mk c) =
        ComplexRay.realificationOrbit (ComplexRay.mk c) ∧
      Function.Injective
        (ComplexRay.realificationOrbit :
          ComplexRay Unit → RealSectorOrbit Unit) ∧
      Function.Bijective
        (ComplexRay.realificationOrbit :
          ComplexRay Unit → RealSectorOrbit Unit) ∧
      ComplexRay.realificationOrbit (ComplexRay.mk c) =
        RealSectorOrbit.mk (realColumn1State c) ∧
      RealSectorPhaseEquivalent
        (realTopState top c : Unit ⊕ Unit → ℝ)
        (realColumn0State c : Unit ⊕ Unit → ℝ) ∧
      ComplexRay.realificationOrbit (ComplexRay.mk c) =
        RealSectorOrbit.mk (realTopState top c) := by
  exact ⟨Iff.rfl,
    rfl,
    rfl,
    RealSectorOrbit.mk_eq_mk_iff,
    RealSectorOrbit.exists_rep r,
    RealSectorOrbit.inductionOn r (fun _ ↦ rfl),
    RealSectorOrbit.inductionOn r (fun _ ↦ rfl),
    RealSectorOrbit.lift_mk
      (fun _ : RealState (Unit ⊕ Unit) ↦ (0 : ℝ))
      (fun _ _ _ ↦ rfl) w,
    RealSectorOrbit.function_ext hfg,
    rfl,
    complexStateOfRealColumn0_realColumn0State c,
    realColumn0State_complexStateOfRealColumn0 w,
    rfl,
    rfl,
    ComplexRay.realificationOrbit_mk c,
    rfl,
    RealSectorOrbit.toComplexRay_mk w,
    RealSectorOrbit.toComplexRay_realificationOrbit q,
    ComplexRay.realificationOrbit_toComplexRay r,
    rfl,
    ComplexRay.realificationOrbit_injective,
    ComplexRay.realificationOrbit_bijective,
    ComplexRay.realificationOrbit_mk_eq_realColumn1State c,
    realTopState_phaseEquivalent_realColumn0State top c,
    ComplexRay.realificationOrbit_mk_eq_realTopState top c⟩

/-! ## Complete observable consumer -/

/-- Complete named consumer for all 10 bottom-marginal declarations. -/
theorem sectorObservables_api
    (eta : ℂ) (heta : Complex.normSq eta = 1)
    (raw : Unit ⊕ Unit → ℝ)
    (x y : RealState (Unit ⊕ Unit))
    (hxy : RealSectorPhaseEquivalent (x : Unit ⊕ Unit → ℝ) y)
    (r : RealSectorOrbit Unit) (c : ComplexState Unit)
    (q : ComplexRay Unit) :
    bottomRealWeight (realSectorAction eta raw) () =
        Complex.normSq eta * bottomRealWeight raw () ∧
      bottomRealWeight (realSectorAction eta raw) () =
        bottomRealWeight raw () ∧
      realBottomDistribution x = realBottomDistribution x ∧
      (realBottomDistribution x).weight () = bottomRealWeight x () ∧
      realBottomDistribution x = realBottomDistribution y ∧
      RealSectorOrbit.bottomDistribution r =
        RealSectorOrbit.bottomDistribution r ∧
      RealSectorOrbit.bottomDistribution (RealSectorOrbit.mk x) =
        realBottomDistribution x ∧
      realBottomDistribution (realColumn0State c) =
        FiniteDistribution.ofNormalizedState
          complexWeight complexWeight_nonneg c ∧
      realBottomDistribution (realColumn1State c) =
        FiniteDistribution.ofNormalizedState
          complexWeight complexWeight_nonneg c ∧
      RealSectorOrbit.bottomDistribution
          (ComplexRay.realificationOrbit q) =
        ComplexRay.distribution q := by
  exact ⟨realSectorAction_bottomRealWeight eta raw (),
    realSectorAction_bottomRealWeight_of_normSq_eq_one eta heta raw (),
    rfl,
    realBottomDistribution_weight x (),
    realBottomDistribution_eq_of_phase hxy,
    rfl,
    RealSectorOrbit.bottomDistribution_mk x,
    realBottomDistribution_realColumn0State c,
    realBottomDistribution_realColumn1State c,
    ComplexRay.realificationOrbit_distribution q⟩

/-! ## Complete ordinary-real-ray boundary consumer -/

/-- Complete named consumer for all eight exact no-descent declarations. -/
theorem sectorBoundary_api
    (psi : ComplexState Unit) (eta : ℂ)
    (heta : Complex.normSq eta = 1) :
    (RealRay.mk
          (realColumn0State (ComplexState.rightPhase psi eta heta)) =
        RealRay.mk (realColumn0State psi) ↔
      eta = 1 ∨ eta = -1) ∧
      (RealRay.mk
          (realColumn1State (ComplexState.rightPhase psi eta heta)) =
        RealRay.mk (realColumn1State psi) ↔
      eta = 1 ∨ eta = -1) ∧
      RealRay.mk
          (realColumn0State
            (ComplexState.rightPhase psi Complex.I Complex.normSq_I)) ≠
        RealRay.mk (realColumn0State psi) ∧
      RealRay.mk
          (realColumn1State
            (ComplexState.rightPhase psi Complex.I Complex.normSq_I)) ≠
        RealRay.mk (realColumn1State psi) ∧
      ¬ (∃ F : ComplexRay Unit → RealRay (Unit ⊕ Unit),
        ∀ z : ComplexState Unit,
          F (ComplexRay.mk z) = RealRay.mk (realColumn0State z)) ∧
      ¬ (∃ F : ComplexRay Unit → RealRay (Unit ⊕ Unit),
        ∀ z : ComplexState Unit,
          F (ComplexRay.mk z) = RealRay.mk (realColumn1State z)) ∧
      ((∃ F : ComplexRay Unit → RealRay (Unit ⊕ Unit),
          ∀ z : ComplexState Unit,
            F (ComplexRay.mk z) = RealRay.mk (realColumn0State z)) ↔
        IsEmpty Unit) ∧
      ((∃ F : ComplexRay Unit → RealRay (Unit ⊕ Unit),
          ∀ z : ComplexState Unit,
            F (ComplexRay.mk z) = RealRay.mk (realColumn1State z)) ↔
        IsEmpty Unit) := by
  exact ⟨realColumn0State_rightPhase_realRay_eq_iff psi eta heta,
    realColumn1State_rightPhase_realRay_eq_iff psi eta heta,
    realColumn0State_rightPhase_I_realRay_ne psi,
    realColumn1State_rightPhase_I_realRay_ne psi,
    no_complexRay_realColumn0_lift,
    no_complexRay_realColumn1_lift,
    complexRay_realColumn0_lift_exists_iff_isEmpty,
    complexRay_realColumn1_lift_exists_iff_isEmpty⟩

/-! ## Concrete `Unit`-indexed distinction witnesses -/

/-- The normalized one-coordinate complex representative with amplitude `1`. -/
def unitOneState : ComplexState Unit :=
  ⟨fun _ ↦ 1, by
    simp [totalWeight, basisWeight, complexWeight]⟩

/-- The same complex ray represented after multiplication by phase `I`. -/
def unitIState : ComplexState Unit :=
  ComplexState.rightPhase unitOneState Complex.I Complex.normSq_I

/-- A non-basis normalized top rebit with amplitudes `3/5` and `4/5`. -/
def threeFourTop : Rebit :=
  ⟨fun b ↦ if b then (4 / 5 : ℝ) else (3 / 5 : ℝ), by
    norm_num [realTotalWeight, totalWeight, basisWeight, realWeight,
      Fintype.univ_bool]⟩

/-- The representatives `1` and `I` define the same complex ray. -/
theorem unitI_eq_unitOne_complexRay :
    ComplexRay.mk unitIState = ComplexRay.mk unitOneState :=
  ComplexRay.mk_eq_mk_iff.mpr
    (ComplexState.rightPhaseEquivalent_rightPhase
      unitOneState Complex.I Complex.normSq_I)

/-- Their first-column realifications define the same real sector orbit. -/
theorem unitI_eq_unitOne_realSectorOrbit :
    RealSectorOrbit.mk (realColumn0State unitIState) =
      RealSectorOrbit.mk (realColumn0State unitOneState) := by
  simpa only [ComplexRay.realificationOrbit_mk] using
    congrArg ComplexRay.realificationOrbit unitI_eq_unitOne_complexRay

/-- Their first-column realifications are distinct ordinary real rays. -/
theorem unitI_ne_unitOne_realRay :
    RealRay.mk (realColumn0State unitIState) ≠
      RealRay.mk (realColumn0State unitOneState) :=
  realColumn0State_rightPhase_I_realRay_ne unitOneState

/-- Their full doubled-real computational-basis distributions are different. -/
theorem unitI_fullDistribution_ne_unitOne :
    RealRay.distribution (RealRay.mk (realColumn0State unitIState)) ≠
      RealRay.distribution (RealRay.mk (realColumn0State unitOneState)) := by
  intro h
  have hweight := congrArg
    (fun mu : FiniteDistribution (Unit ⊕ Unit) ↦ mu.weight (Sum.inl ())) h
  simp [unitIState, unitOneState, realColumn0State, realColumn0,
    ComplexState.rightPhase, basisWeight, realWeight] at hweight

/-- Marginalizing the two real sectors restores the same bottom distribution. -/
theorem unitI_bottomDistribution_eq_unitOne :
    realBottomDistribution (realColumn0State unitIState) =
      realBottomDistribution (realColumn0State unitOneState) := by
  rw [← RealSectorOrbit.bottomDistribution_mk,
    unitI_eq_unitOne_realSectorOrbit,
    RealSectorOrbit.bottomDistribution_mk]

/-- Every normalized top rebit, including a non-basis one, lies in the source orbit. -/
theorem arbitraryTop_realSectorOrbit (top : Rebit) :
    ComplexRay.realificationOrbit (ComplexRay.mk unitOneState) =
      RealSectorOrbit.mk (realTopState top unitOneState) :=
  ComplexRay.realificationOrbit_mk_eq_realTopState top unitOneState

/-- The explicit `3/5,4/5` top rebit exercises the arbitrary-top consumer. -/
theorem threeFourTop_realSectorOrbit :
    ComplexRay.realificationOrbit (ComplexRay.mk unitOneState) =
      RealSectorOrbit.mk (realTopState threeFourTop unitOneState) :=
  arbitraryTop_realSectorOrbit threeFourTop

/-- On the empty index type both canonical constructor-compatible lifts exist vacuously. -/
theorem emptyCanonicalLifts_exist :
    (∃ F : ComplexRay Empty → RealRay (Empty ⊕ Empty),
      ∀ z : ComplexState Empty,
        F (ComplexRay.mk z) = RealRay.mk (realColumn0State z)) ∧
      (∃ F : ComplexRay Empty → RealRay (Empty ⊕ Empty),
        ∀ z : ComplexState Empty,
          F (ComplexRay.mk z) = RealRay.mk (realColumn1State z)) := by
  exact ⟨complexRay_realColumn0_lift_exists_iff_isEmpty.mpr inferInstance,
    complexRay_realColumn1_lift_exists_iff_isEmpty.mpr inferInstance⟩

/-! ## Local axiom audit -/

#print axioms sectorAction_api
#print axioms sectorRelation_api
#print axioms sectorOrbit_api
#print axioms sectorObservables_api
#print axioms sectorBoundary_api
#print axioms unitI_eq_unitOne_complexRay
#print axioms unitI_eq_unitOne_realSectorOrbit
#print axioms unitI_ne_unitOne_realRay
#print axioms unitI_fullDistribution_ne_unitOne
#print axioms unitI_bottomDistribution_eq_unitOne
#print axioms arbitraryTop_realSectorOrbit
#print axioms emptyCanonicalLifts_exist

end QuaternionicComputing.State.RealificationOrbitAudit
