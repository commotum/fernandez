module

public import QuaternionicComputing.State.RayObservables
public import QuaternionicComputing.State.RayEvolution
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Circuit.OrderingWitness

/-!
# Normalized ray descent audit

This non-root diagnostic leaf gives named consumers for every stable
declaration introduced by Goal 2 Stage 4B.  It covers finite deterministic
pushforward laws, locally-unitary append, all real/complex/quaternionic ray
observables and evolutions, and the semantic bridges from representative phase
equality to quotient equality.

Concrete examples exercise rebits, qubits, and quaterbits.  The quaternionic
ordering witness additionally checks that chronological append uses the
noncommutative-safe order `D.eval * C.eval`.  Zero-wire circuits remain
nonvacuous because `BitBasis Empty` has one assignment, while proof arguments
to the descended evolution are irrelevant.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion

namespace QuaternionicComputing.State.RayDescentAudit

open QuaternionicComputing.Circuit

/-! ## Shared finite-distribution and circuit closure consumers -/

/--
Complete named consumer for deterministic pushforward functoriality and
locally-unitary chronological append.
-/
theorem sharedDescent_api
    (mu : FiniteDistribution Bool) (f g : Bool → Bool)
    (C D : OrderedCircuit ℍ[ℝ] Bool)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    mu.pushforward id = mu ∧
      mu.pushforward (g ∘ f) = (mu.pushforward f).pushforward g ∧
      (C ++ D).IsLocallyUnitary := by
  exact ⟨FiniteDistribution.pushforward_id mu,
    FiniteDistribution.pushforward_comp mu f g,
    hC.append hD⟩

/-! ## Complete real-ray consumer -/

/-- Complete named consumer for every real-ray observable, evolution, and semantic bridge. -/
theorem realRayDescent_api
    (r : RealRay Bool) (a b : RealState Bool)
    (f g : Bool → Bool)
    (U V : Matrix Bool Bool ℝ)
    (hU : U ∈ unitary (Matrix Bool Bool ℝ))
    (hV : V ∈ unitary (Matrix Bool Bool ℝ))
    (q : RealRay (BitBasis Unit))
    (x : RealState (BitBasis Unit))
    (C D : OrderedCircuit ℝ Unit)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    RealRay.distribution r = RealRay.distribution r ∧
      RealRay.distribution (RealRay.mk a) =
        FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg a ∧
      RealRay.basisWeight r false = (RealRay.distribution r).weight false ∧
      RealRay.basisWeight (RealRay.mk a) false = realBasisWeight a false ∧
      (RealRay.distribution r).weight false = RealRay.basisWeight r false ∧
      RealRay.eventWeight r {false} =
        (RealRay.distribution r).eventWeight {false} ∧
      RealRay.eventWeight (RealRay.mk a) {false} =
        (FiniteDistribution.ofNormalizedState
          realWeight realWeight_nonneg a).eventWeight {false} ∧
      RealRay.pushforward r f = (RealRay.distribution r).pushforward f ∧
      RealRay.pushforward (RealRay.mk a) f =
        (FiniteDistribution.ofNormalizedState
          realWeight realWeight_nonneg a).pushforward f ∧
      RealRay.pushforward r id = RealRay.distribution r ∧
      RealRay.pushforward r (g ∘ f) =
        (RealRay.pushforward r f).pushforward g ∧
      RealRay.evolveUnitary r U hU = RealRay.evolveUnitary r U hU ∧
      RealRay.evolveUnitary (RealRay.mk a) U hU =
        RealRay.mk (RealState.evolveUnitary a U hU) ∧
      RealRay.evolveUnitary r 1
          (unitary (Matrix Bool Bool ℝ)).one_mem = r ∧
      RealRay.evolveUnitary (RealRay.evolveUnitary r U hU) V hV =
        RealRay.evolveUnitary r (V * U)
          ((unitary (Matrix Bool Bool ℝ)).mul_mem hV hU) ∧
      RealRay.evolveCircuit q C hC = RealRay.evolveCircuit q C hC ∧
      RealRay.evolveCircuit (RealRay.mk x) C hC =
        RealRay.mk
          (RealState.evolveUnitary x C.eval (C.eval_mem_unitary hC)) ∧
      RealRay.evolveCircuit q []
          OrderedCircuit.isLocallyUnitary_nil = q ∧
      RealRay.evolveCircuit q (C ++ D) (hC.append hD) =
        RealRay.evolveCircuit (RealRay.evolveCircuit q C hC) D hD ∧
      (Semantics.RealStatePhaseEq a b ↔
        RealRay.mk a = RealRay.mk b) := by
  exact ⟨rfl,
    RealRay.distribution_mk a,
    rfl,
    RealRay.basisWeight_mk a false,
    RealRay.distribution_weight r false,
    rfl,
    RealRay.eventWeight_mk a {false},
    rfl,
    RealRay.pushforward_mk a f,
    RealRay.pushforward_id r,
    RealRay.pushforward_comp r f g,
    rfl,
    RealRay.evolveUnitary_mk a U hU,
    RealRay.evolveUnitary_one r,
    RealRay.evolveUnitary_comp r U V hU hV,
    rfl,
    RealRay.evolveCircuit_mk x C hC,
    RealRay.evolveCircuit_nil q,
    RealRay.evolveCircuit_append q C D hC hD,
    Semantics.RealStatePhaseEq.iff_realRay_mk_eq⟩

/-! ## Complete complex-ray consumer -/

/-- Complete named consumer for every complex-ray observable, evolution, and semantic bridge. -/
theorem complexRayDescent_api
    (r : ComplexRay Bool) (a b : ComplexState Bool)
    (f g : Bool → Bool)
    (U V : Matrix Bool Bool ℂ)
    (hU : U ∈ unitary (Matrix Bool Bool ℂ))
    (hV : V ∈ unitary (Matrix Bool Bool ℂ))
    (q : ComplexRay (BitBasis Unit))
    (x : ComplexState (BitBasis Unit))
    (C D : OrderedCircuit ℂ Unit)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    ComplexRay.distribution r = ComplexRay.distribution r ∧
      ComplexRay.distribution (ComplexRay.mk a) =
        FiniteDistribution.ofNormalizedState
          complexWeight complexWeight_nonneg a ∧
      ComplexRay.basisWeight r false =
        (ComplexRay.distribution r).weight false ∧
      ComplexRay.basisWeight (ComplexRay.mk a) false =
        complexBasisWeight a false ∧
      (ComplexRay.distribution r).weight false =
        ComplexRay.basisWeight r false ∧
      ComplexRay.eventWeight r {false} =
        (ComplexRay.distribution r).eventWeight {false} ∧
      ComplexRay.eventWeight (ComplexRay.mk a) {false} =
        (FiniteDistribution.ofNormalizedState
          complexWeight complexWeight_nonneg a).eventWeight {false} ∧
      ComplexRay.pushforward r f =
        (ComplexRay.distribution r).pushforward f ∧
      ComplexRay.pushforward (ComplexRay.mk a) f =
        (FiniteDistribution.ofNormalizedState
          complexWeight complexWeight_nonneg a).pushforward f ∧
      ComplexRay.pushforward r id = ComplexRay.distribution r ∧
      ComplexRay.pushforward r (g ∘ f) =
        (ComplexRay.pushforward r f).pushforward g ∧
      ComplexRay.evolveUnitary r U hU =
        ComplexRay.evolveUnitary r U hU ∧
      ComplexRay.evolveUnitary (ComplexRay.mk a) U hU =
        ComplexRay.mk (ComplexState.evolveUnitary a U hU) ∧
      ComplexRay.evolveUnitary r 1
          (unitary (Matrix Bool Bool ℂ)).one_mem = r ∧
      ComplexRay.evolveUnitary
          (ComplexRay.evolveUnitary r U hU) V hV =
        ComplexRay.evolveUnitary r (V * U)
          ((unitary (Matrix Bool Bool ℂ)).mul_mem hV hU) ∧
      ComplexRay.evolveCircuit q C hC =
        ComplexRay.evolveCircuit q C hC ∧
      ComplexRay.evolveCircuit (ComplexRay.mk x) C hC =
        ComplexRay.mk
          (ComplexState.evolveUnitary x C.eval (C.eval_mem_unitary hC)) ∧
      ComplexRay.evolveCircuit q []
          OrderedCircuit.isLocallyUnitary_nil = q ∧
      ComplexRay.evolveCircuit q (C ++ D) (hC.append hD) =
        ComplexRay.evolveCircuit (ComplexRay.evolveCircuit q C hC) D hD ∧
      (Semantics.ComplexStatePhaseEq a b ↔
        ComplexRay.mk a = ComplexRay.mk b) := by
  exact ⟨rfl,
    ComplexRay.distribution_mk a,
    rfl,
    ComplexRay.basisWeight_mk a false,
    ComplexRay.distribution_weight r false,
    rfl,
    ComplexRay.eventWeight_mk a {false},
    rfl,
    ComplexRay.pushforward_mk a f,
    ComplexRay.pushforward_id r,
    ComplexRay.pushforward_comp r f g,
    rfl,
    ComplexRay.evolveUnitary_mk a U hU,
    ComplexRay.evolveUnitary_one r,
    ComplexRay.evolveUnitary_comp r U V hU hV,
    rfl,
    ComplexRay.evolveCircuit_mk x C hC,
    ComplexRay.evolveCircuit_nil q,
    ComplexRay.evolveCircuit_append q C D hC hD,
    Semantics.ComplexStatePhaseEq.iff_complexRay_mk_eq⟩

/-! ## Complete quaternionic-ray consumer -/

/--
Complete named consumer for every quaternionic right-ray observable,
evolution, and semantic bridge.
-/
theorem quaternionRayDescent_api
    (r : QuaternionRay Bool) (a b : QuaternionState Bool)
    (f g : Bool → Bool)
    (U V : Matrix Bool Bool ℍ[ℝ])
    (hU : U ∈ unitary (Matrix Bool Bool ℍ[ℝ]))
    (hV : V ∈ unitary (Matrix Bool Bool ℍ[ℝ]))
    (q : QuaternionRay (BitBasis Unit))
    (x : QuaternionState (BitBasis Unit))
    (C D : OrderedCircuit ℍ[ℝ] Unit)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    QuaternionRay.distribution r = QuaternionRay.distribution r ∧
      QuaternionRay.distribution (QuaternionRay.mk a) =
        FiniteDistribution.ofNormalizedState
          quaternionWeight quaternionWeight_nonneg a ∧
      QuaternionRay.basisWeight r false =
        (QuaternionRay.distribution r).weight false ∧
      QuaternionRay.basisWeight (QuaternionRay.mk a) false =
        quaternionBasisWeight a false ∧
      (QuaternionRay.distribution r).weight false =
        QuaternionRay.basisWeight r false ∧
      QuaternionRay.eventWeight r {false} =
        (QuaternionRay.distribution r).eventWeight {false} ∧
      QuaternionRay.eventWeight (QuaternionRay.mk a) {false} =
        (FiniteDistribution.ofNormalizedState
          quaternionWeight quaternionWeight_nonneg a).eventWeight {false} ∧
      QuaternionRay.pushforward r f =
        (QuaternionRay.distribution r).pushforward f ∧
      QuaternionRay.pushforward (QuaternionRay.mk a) f =
        (FiniteDistribution.ofNormalizedState
          quaternionWeight quaternionWeight_nonneg a).pushforward f ∧
      QuaternionRay.pushforward r id = QuaternionRay.distribution r ∧
      QuaternionRay.pushforward r (g ∘ f) =
        (QuaternionRay.pushforward r f).pushforward g ∧
      QuaternionRay.evolveUnitary r U hU =
        QuaternionRay.evolveUnitary r U hU ∧
      QuaternionRay.evolveUnitary (QuaternionRay.mk a) U hU =
        QuaternionRay.mk (QuaternionState.evolveUnitary a U hU) ∧
      QuaternionRay.evolveUnitary r 1
          (unitary (Matrix Bool Bool ℍ[ℝ])).one_mem = r ∧
      QuaternionRay.evolveUnitary
          (QuaternionRay.evolveUnitary r U hU) V hV =
        QuaternionRay.evolveUnitary r (V * U)
          ((unitary (Matrix Bool Bool ℍ[ℝ])).mul_mem hV hU) ∧
      QuaternionRay.evolveCircuit q C hC =
        QuaternionRay.evolveCircuit q C hC ∧
      QuaternionRay.evolveCircuit (QuaternionRay.mk x) C hC =
        QuaternionRay.mk
          (QuaternionState.evolveUnitary x C.eval (C.eval_mem_unitary hC)) ∧
      QuaternionRay.evolveCircuit q []
          OrderedCircuit.isLocallyUnitary_nil = q ∧
      QuaternionRay.evolveCircuit q (C ++ D) (hC.append hD) =
        QuaternionRay.evolveCircuit
          (QuaternionRay.evolveCircuit q C hC) D hD ∧
      (Semantics.QuaternionStatePhaseEq a b ↔
        QuaternionRay.mk a = QuaternionRay.mk b) := by
  exact ⟨rfl,
    QuaternionRay.distribution_mk a,
    rfl,
    QuaternionRay.basisWeight_mk a false,
    QuaternionRay.distribution_weight r false,
    rfl,
    QuaternionRay.eventWeight_mk a {false},
    rfl,
    QuaternionRay.pushforward_mk a f,
    QuaternionRay.pushforward_id r,
    QuaternionRay.pushforward_comp r f g,
    rfl,
    QuaternionRay.evolveUnitary_mk a U hU,
    QuaternionRay.evolveUnitary_one r,
    QuaternionRay.evolveUnitary_comp r U V hU hV,
    rfl,
    QuaternionRay.evolveCircuit_mk x C hC,
    QuaternionRay.evolveCircuit_nil q,
    QuaternionRay.evolveCircuit_append q C D hC hD,
    Semantics.QuaternionStatePhaseEq.iff_quaternionRay_mk_eq⟩

/-! ## Concrete rebit, qubit, and quaterbit examples -/

/-- A normalized real `|false⟩` representative. -/
def rebitFalse : Rebit :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool]⟩

/-- A normalized complex `|false⟩` representative. -/
def qubitFalse : Qubit :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

/-- A normalized quaternionic `|false⟩` representative. -/
def quaterbitFalse : Quaterbit :=
  ⟨fun b ↦ if b then 0 else 1, by
    simp [totalWeight, basisWeight, quaternionWeight, Fintype.univ_bool]⟩

/-- Concrete rebit weights, event, postprocessing, and identity evolution. -/
theorem rebit_observable_evolution_example :
    RealRay.basisWeight (RealRay.mk rebitFalse) false = 1 ∧
      RealRay.basisWeight (RealRay.mk rebitFalse) true = 0 ∧
      RealRay.eventWeight (RealRay.mk rebitFalse) {false} = 1 ∧
      (RealRay.pushforward (RealRay.mk rebitFalse)
        (fun _ ↦ ())).weight () = 1 ∧
      RealRay.evolveUnitary (RealRay.mk rebitFalse) 1
        (unitary (Matrix Bool Bool ℝ)).one_mem = RealRay.mk rebitFalse := by
  simp [rebitFalse, realBasisWeight, basisWeight, realWeight,
    RealRay.eventWeight, FiniteDistribution.eventWeight,
    FiniteDistribution.pushforward_weight]

/-- Concrete qubit weights, event, postprocessing, and identity evolution. -/
theorem qubit_observable_evolution_example :
    ComplexRay.basisWeight (ComplexRay.mk qubitFalse) false = 1 ∧
      ComplexRay.basisWeight (ComplexRay.mk qubitFalse) true = 0 ∧
      ComplexRay.eventWeight (ComplexRay.mk qubitFalse) {false} = 1 ∧
      (ComplexRay.pushforward (ComplexRay.mk qubitFalse)
        (fun _ ↦ ())).weight () = 1 ∧
      ComplexRay.evolveUnitary (ComplexRay.mk qubitFalse) 1
        (unitary (Matrix Bool Bool ℂ)).one_mem = ComplexRay.mk qubitFalse := by
  simp [qubitFalse, complexBasisWeight, basisWeight, complexWeight,
    ComplexRay.eventWeight, FiniteDistribution.eventWeight,
    FiniteDistribution.pushforward_weight]

/-- Concrete quaterbit weights, event, postprocessing, and identity evolution. -/
theorem quaterbit_observable_evolution_example :
    QuaternionRay.basisWeight (QuaternionRay.mk quaterbitFalse) false = 1 ∧
      QuaternionRay.basisWeight (QuaternionRay.mk quaterbitFalse) true = 0 ∧
      QuaternionRay.eventWeight (QuaternionRay.mk quaterbitFalse) {false} = 1 ∧
      (QuaternionRay.pushforward (QuaternionRay.mk quaterbitFalse)
        (fun _ ↦ ())).weight () = 1 ∧
      QuaternionRay.evolveUnitary (QuaternionRay.mk quaterbitFalse) 1
          (unitary (Matrix Bool Bool ℍ[ℝ])).one_mem =
        QuaternionRay.mk quaterbitFalse := by
  simp [quaterbitFalse, quaternionBasisWeight, basisWeight, quaternionWeight,
    QuaternionRay.eventWeight, FiniteDistribution.eventWeight,
    FiniteDistribution.pushforward_weight,
    _root_.Quaternion.normSq_def']

/-! ## Quaternionic chronological-order sanity -/

namespace QuaternionOrder

open Circuit.OrderingWitness

/-- The `i`-then-`j` witness evolved as a quaternionic ray. -/
def iThenJRay : QuaternionRay (BitBasis Bool) :=
  QuaternionRay.evolveCircuit (QuaternionRay.mk inputState)
    iThenJ iThenJ_locallyUnitary

/-- The `j`-then-`i` witness evolved as a quaternionic ray. -/
def jThenIRay : QuaternionRay (BitBasis Bool) :=
  QuaternionRay.evolveCircuit (QuaternionRay.mk inputState)
    jThenI jThenI_locallyUnitary

/-- Descended evolution retains the first order's exact `00` output weight. -/
@[simp]
theorem iThenJRay_basis00_weight :
    QuaternionRay.basisWeight iThenJRay basis00 = 8281 / 15625 := by
  simpa [iThenJRay, iThenJOutput] using iThenJOutput_basis00_weight

/-- Descended evolution retains the reverse order's exact `00` output weight. -/
@[simp]
theorem jThenIRay_basis00_weight :
    QuaternionRay.basisWeight jThenIRay basis00 = 1369 / 15625 := by
  simpa [jThenIRay, jThenIOutput] using jThenIOutput_basis00_weight

/-- After quotient descent, the two orders still give different `00` basis weights. -/
theorem ray_order_is_observable :
    QuaternionRay.basisWeight iThenJRay basis00 ≠
      QuaternionRay.basisWeight jThenIRay basis00 := by
  rw [iThenJRay_basis00_weight, jThenIRay_basis00_weight]
  norm_num

/-- The one-gate `i` circuit is locally unitary. -/
theorem iSingleton_locallyUnitary :
    OrderedCircuit.IsLocallyUnitary
      ([iGate] : OrderedCircuit ℍ[ℝ] Bool) :=
  OrderedCircuit.isLocallyUnitary_cons.mpr
    ⟨iGate_locallyUnitary, OrderedCircuit.isLocallyUnitary_nil⟩

/-- The one-gate `j` circuit is locally unitary. -/
theorem jSingleton_locallyUnitary :
    OrderedCircuit.IsLocallyUnitary
      ([jGate] : OrderedCircuit ℍ[ℝ] Bool) :=
  OrderedCircuit.isLocallyUnitary_cons.mpr
    ⟨jGate_locallyUnitary, OrderedCircuit.isLocallyUnitary_nil⟩

/--
Appending the later `j` gate evolves first by the `i` singleton and then by
the `j` singleton.
-/
theorem ray_append_chronology :
    QuaternionRay.evolveCircuit (QuaternionRay.mk inputState)
        ([iGate] ++ [jGate])
        (iSingleton_locallyUnitary.append jSingleton_locallyUnitary) =
      QuaternionRay.evolveCircuit
        (QuaternionRay.evolveCircuit (QuaternionRay.mk inputState)
          [iGate] iSingleton_locallyUnitary)
        [jGate] jSingleton_locallyUnitary :=
  QuaternionRay.evolveCircuit_append _ _ _
    iSingleton_locallyUnitary jSingleton_locallyUnitary

end QuaternionOrder

/-! ## Empty-index and zero-wire boundaries -/

/-- Empty amplitude index types still admit no rays after adding descended operations. -/
theorem emptyIndex_rays_are_empty :
    IsEmpty (RealRay Empty) ∧
      IsEmpty (ComplexRay Empty) ∧
      IsEmpty (QuaternionRay Empty) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Zero-wire computational-basis spaces admit rays for all three scalars. -/
theorem zeroWire_rays_are_nonempty :
    Nonempty (RealRay (BitBasis Empty)) ∧
      Nonempty (ComplexRay (BitBasis Empty)) ∧
      Nonempty (QuaternionRay (BitBasis Empty)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/--
The empty circuit acts identically on zero-wire rays, and its local-unitarity
proof arguments do not affect descended evolution.
-/
theorem zeroWire_nil_and_proof_irrelevance
    (rr : RealRay (BitBasis Empty))
    (cr : ComplexRay (BitBasis Empty))
    (qr : QuaternionRay (BitBasis Empty))
    (hr hr' : OrderedCircuit.IsLocallyUnitary
      ([] : OrderedCircuit ℝ Empty))
    (hc hc' : OrderedCircuit.IsLocallyUnitary
      ([] : OrderedCircuit ℂ Empty))
    (hq hq' : OrderedCircuit.IsLocallyUnitary
      ([] : OrderedCircuit ℍ[ℝ] Empty)) :
    RealRay.evolveCircuit rr [] hr = rr ∧
      RealRay.evolveCircuit rr [] hr = RealRay.evolveCircuit rr [] hr' ∧
      ComplexRay.evolveCircuit cr [] hc = cr ∧
      ComplexRay.evolveCircuit cr [] hc =
        ComplexRay.evolveCircuit cr [] hc' ∧
      QuaternionRay.evolveCircuit qr [] hq = qr ∧
      QuaternionRay.evolveCircuit qr [] hq =
        QuaternionRay.evolveCircuit qr [] hq' := by
  exact ⟨RealRay.evolveCircuit_nil rr,
    rfl,
    ComplexRay.evolveCircuit_nil cr,
    rfl,
    QuaternionRay.evolveCircuit_nil qr,
    rfl⟩

/-! ## Representative axiom audit -/

#print axioms sharedDescent_api
#print axioms realRayDescent_api
#print axioms complexRayDescent_api
#print axioms quaternionRayDescent_api
#print axioms rebit_observable_evolution_example
#print axioms qubit_observable_evolution_example
#print axioms quaterbit_observable_evolution_example
#print axioms QuaternionOrder.ray_order_is_observable
#print axioms QuaternionOrder.ray_append_chronology
#print axioms zeroWire_nil_and_proof_irrelevance

end QuaternionicComputing.State.RayDescentAudit
