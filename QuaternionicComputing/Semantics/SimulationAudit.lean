module

public import QuaternionicComputing.Semantics.SimulationEncoding
public import QuaternionicComputing.State.RealificationOrbitBoundary
public import QuaternionicComputing.State.RealificationOrbitObservables
public import QuaternionicComputing.Simulation.NonProductWitness

/-!
# Directional simulation semantic audit

This non-root leaf consumes the complete initial Stage 9 relation and
representative-encoding APIs.  Its abstract aggregate sections allocate every
stable declaration from `Semantics.Simulation` exactly once, while the concrete
sections exercise those relations on the complex-to-real and
quaternion-to-complex state encodings.

The top-sector consumers below quantify `Rebit` and `Qubit` values exactly.
They are pure normalized parameter types, not mixed density inputs or proofs
that the encoded target column factors as a top/bottom product.  The final
boundary section reuses the existing ordinary-real-ray non-descent and
nonproduct witnesses.  Nothing in this audit finalizes a Stage 9B/9C cohort
family or claims same-space, ray, channel, or all-effect equality.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.SimulationAudit

open QuaternionicComputing.State

universe uS uT uU uOS uIS uOT uIT uOU uIU uO uM uP uTop uInput

/-! ## Exact allocation of the 38 generic relation declarations -/

/-- Complete consumer for all five `ExactStateEncoding` declarations. -/
theorem exactStateEncoding_api
    {S : Type uS} {T : Type uT} {U : Type uU}
    {encodeST : S → T} {decodeTS : T → S}
    {encodeTU : T → U} {decodeUT : U → T}
    (hleft : Function.LeftInverse decodeTS encodeST)
    (hST : ExactStateEncoding encodeST decodeTS)
    (hTU : ExactStateEncoding encodeTU decodeUT) :
    ExactStateEncoding encodeST decodeTS ∧
      Function.LeftInverse decodeTS encodeST ∧
      Function.Injective encodeST ∧
      ExactStateEncoding (encodeTU ∘ encodeST) (decodeTS ∘ decodeUT) :=
  ⟨ExactStateEncoding.of_leftInverse hleft,
    ExactStateEncoding.leftInverse hST,
    ExactStateEncoding.injective hST,
    ExactStateEncoding.comp hST hTU⟩

/-- Complete consumer for all six `LosslessStateEncoding` declarations. -/
theorem losslessStateEncoding_api
    {S : Type uS} {T : Type uT} {U : Type uU}
    {encodeST : S → T} {decodeTS : T → S}
    {encodeTU : T → U} {decodeUT : U → T}
    {sourceWeight : S → ℝ} {middleWeight : T → ℝ}
    {targetWeight : U → ℝ}
    (hexact : ExactStateEncoding encodeST decodeTS)
    (hweight : ∀ source, middleWeight (encodeST source) = sourceWeight source)
    (hST : LosslessStateEncoding encodeST decodeTS sourceWeight middleWeight)
    (hTU : LosslessStateEncoding encodeTU decodeUT middleWeight targetWeight)
    (source : S) :
    LosslessStateEncoding encodeST decodeTS sourceWeight middleWeight ∧
      ExactStateEncoding encodeST decodeTS ∧
      middleWeight (encodeST source) = sourceWeight source ∧
      Function.Injective encodeST ∧
      LosslessStateEncoding (encodeTU ∘ encodeST) (decodeTS ∘ decodeUT)
        sourceWeight targetWeight :=
  ⟨LosslessStateEncoding.of_exact_of_totalWeight hexact hweight,
    LosslessStateEncoding.exact hST,
    LosslessStateEncoding.preservesTotalWeight hST source,
    LosslessStateEncoding.injective hST,
    LosslessStateEncoding.comp hST hTU⟩

/-- Complete consumer for all four `ExactOperatorEmbedding` declarations. -/
theorem exactOperatorEmbedding_api
    {RS : Type uS} {RT : Type uT} {RU : Type uU}
    {OS : Type uOS} {IS : Type uIS}
    {OT : Type uOT} {IT : Type uIT}
    {OU : Type uOU} {IU : Type uIU}
    {embedST : Matrix OS IS RS → Matrix OT IT RT}
    {embedTU : Matrix OT IT RT → Matrix OU IU RU}
    {source : Matrix OS IS RS} {middle : Matrix OT IT RT}
    {target : Matrix OU IU RU}
    (heq : middle = embedST source)
    (hST : ExactOperatorEmbedding embedST source middle)
    (hTU : ExactOperatorEmbedding embedTU middle target) :
    ExactOperatorEmbedding embedST source middle ∧
      middle = embedST source ∧
      ExactOperatorEmbedding (embedTU ∘ embedST) source target :=
  ⟨ExactOperatorEmbedding.of_eq heq,
    ExactOperatorEmbedding.eq hST,
    ExactOperatorEmbedding.comp hST hTU⟩

/-- Complete consumer for all four `StateIntertwining` declarations. -/
theorem stateIntertwining_api
    {RS : Type uS} {RT : Type uT} {RU : Type uU}
    {OS : Type uOS} {IS : Type uIS}
    {OT : Type uOT} {IT : Type uIT}
    {OU : Type uOU} {IU : Type uIU}
    [Fintype IS] [Fintype IT] [Fintype IU]
    [NonUnitalNonAssocSemiring RS]
    [NonUnitalNonAssocSemiring RT]
    [NonUnitalNonAssocSemiring RU]
    {encodeInST : (IS → RS) → (IT → RT)}
    {encodeOutST : (OS → RS) → (OT → RT)}
    {encodeInTU : (IT → RT) → (IU → RU)}
    {encodeOutTU : (OT → RT) → (OU → RU)}
    {source : Matrix OS IS RS} {middle : Matrix OT IT RT}
    {target : Matrix OU IU RU}
    (hforall : ∀ input, middle *ᵥ encodeInST input =
      encodeOutST (source *ᵥ input))
    (hST : StateIntertwining encodeInST encodeOutST source middle)
    (hTU : StateIntertwining encodeInTU encodeOutTU middle target)
    (input : IS → RS) :
    StateIntertwining encodeInST encodeOutST source middle ∧
      middle *ᵥ encodeInST input = encodeOutST (source *ᵥ input) ∧
      StateIntertwining (encodeInTU ∘ encodeInST)
        (encodeOutTU ∘ encodeOutST) source target :=
  ⟨StateIntertwining.of_forall hforall,
    StateIntertwining.apply hST input,
    StateIntertwining.comp hST hTU⟩

/-- Complete consumer for both `AllTopStateIntertwining` declarations. -/
theorem allTopStateIntertwining_api
    {Top : Type uTop}
    {RS : Type uS} {RT : Type uT}
    {OS : Type uOS} {IS : Type uIS}
    {OT : Type uOT} {IT : Type uIT}
    [Fintype IS] [Fintype IT]
    [NonUnitalNonAssocSemiring RS] [NonUnitalNonAssocSemiring RT]
    {encodeInput : Top → (IS → RS) → (IT → RT)}
    {encodeOutput : Top → (OS → RS) → (OT → RT)}
    {source : Matrix OS IS RS} {target : Matrix OT IT RT}
    (h : AllTopStateIntertwining encodeInput encodeOutput source target)
    (top : Top) :
    AllTopStateIntertwining encodeInput encodeOutput source target ∧
      StateIntertwining (encodeInput top) (encodeOutput top) source target :=
  ⟨h, AllTopStateIntertwining.forTop h top⟩

/-- Complete consumer for all five `DecodedBasisWeightAgreement` declarations. -/
theorem decodedBasisWeightAgreement_api
    {SourceOutcome : Type uO} {MiddleOutcome : Type uM}
    {TargetOutcome : Type uP}
    {decodeSM : (MiddleOutcome → ℝ) → (SourceOutcome → ℝ)}
    {decodeMT : (TargetOutcome → ℝ) → (MiddleOutcome → ℝ)}
    {sourceWeight : SourceOutcome → ℝ}
    {middleWeight : MiddleOutcome → ℝ}
    {targetWeight : TargetOutcome → ℝ}
    (heq : decodeSM middleWeight = sourceWeight)
    (hSM : DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight)
    (hMT : DecodedBasisWeightAgreement decodeMT middleWeight targetWeight)
    (outcome : SourceOutcome) :
    DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight ∧
      decodeSM middleWeight = sourceWeight ∧
      decodeSM middleWeight outcome = sourceWeight outcome ∧
      DecodedBasisWeightAgreement (decodeSM ∘ decodeMT)
        sourceWeight targetWeight :=
  ⟨DecodedBasisWeightAgreement.of_eq heq,
    DecodedBasisWeightAgreement.eq hSM,
    DecodedBasisWeightAgreement.apply hSM outcome,
    DecodedBasisWeightAgreement.comp hSM hMT⟩

/-- Complete consumer for all eight `DecodedDistributionAgreement` declarations. -/
theorem decodedDistributionAgreement_api
    {SourceOutcome : Type uO} {MiddleOutcome : Type uM}
    {TargetOutcome : Type uP} {PostOutcome : Type uU}
    [Fintype SourceOutcome] [Fintype MiddleOutcome]
    [Fintype TargetOutcome] [Fintype PostOutcome]
    {decodeSM : FiniteDistribution MiddleOutcome →
      FiniteDistribution SourceOutcome}
    {decodeMT : FiniteDistribution TargetOutcome →
      FiniteDistribution MiddleOutcome}
    {decodeWeight : (MiddleOutcome → ℝ) → (SourceOutcome → ℝ)}
    {source : FiniteDistribution SourceOutcome}
    {middle : FiniteDistribution MiddleOutcome}
    {target : FiniteDistribution TargetOutcome}
    (heq : decodeSM middle = source)
    (hSM : DecodedDistributionAgreement decodeSM source middle)
    (hMT : DecodedDistributionAgreement decodeMT middle target)
    (hcompat : ∀ distribution,
      (decodeSM distribution).weight = decodeWeight distribution.weight)
    (hweight : DecodedBasisWeightAgreement decodeWeight
      source.weight middle.weight)
    (event : Finset SourceOutcome)
    (postprocess : SourceOutcome → PostOutcome) :
    DecodedDistributionAgreement decodeSM source middle ∧
      decodeSM middle = source ∧
      DecodedDistributionAgreement (decodeSM ∘ decodeMT) source target ∧
      DecodedBasisWeightAgreement decodeWeight source.weight middle.weight ∧
      DecodedDistributionAgreement decodeSM source middle ∧
      (decodeSM middle).eventWeight event = source.eventWeight event ∧
      (decodeSM middle).pushforward postprocess =
        source.pushforward postprocess :=
  ⟨DecodedDistributionAgreement.of_eq heq,
    DecodedDistributionAgreement.eq hSM,
    DecodedDistributionAgreement.comp hSM hMT,
    DecodedDistributionAgreement.decodedBasisWeightAgreement hcompat hSM,
    DecodedDistributionAgreement.of_decodedBasisWeightAgreement hcompat hweight,
    DecodedDistributionAgreement.eventWeight_eq hSM event,
    DecodedDistributionAgreement.pushforward_eq hSM postprocess⟩

/-- Complete consumer for both `AllTopDecodedBasisWeightAgreement` declarations. -/
theorem allTopDecodedBasisWeightAgreement_api
    {Top : Type uTop} {Input : Type uInput}
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    {decode : (TargetOutcome → ℝ) → (SourceOutcome → ℝ)}
    {sourceWeight : Input → SourceOutcome → ℝ}
    {targetWeight : Top → Input → TargetOutcome → ℝ}
    (h : AllTopDecodedBasisWeightAgreement decode sourceWeight targetWeight)
    (top : Top) (input : Input) :
    AllTopDecodedBasisWeightAgreement decode sourceWeight targetWeight ∧
      DecodedBasisWeightAgreement decode (sourceWeight input)
        (targetWeight top input) :=
  ⟨h, AllTopDecodedBasisWeightAgreement.forTopInput h top input⟩

/-- Complete consumer for both `AllTopDecodedDistributionAgreement` declarations. -/
theorem allTopDecodedDistributionAgreement_api
    {Top : Type uTop} {Input : Type uInput}
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    [Fintype SourceOutcome] [Fintype TargetOutcome]
    {decode : FiniteDistribution TargetOutcome →
      FiniteDistribution SourceOutcome}
    {sourceDistribution : Input → FiniteDistribution SourceOutcome}
    {targetDistribution : Top → Input →
      FiniteDistribution TargetOutcome}
    (h : AllTopDecodedDistributionAgreement decode sourceDistribution
      targetDistribution)
    (top : Top) (input : Input) :
    AllTopDecodedDistributionAgreement decode sourceDistribution
        targetDistribution ∧
      DecodedDistributionAgreement decode (sourceDistribution input)
        (targetDistribution top input) :=
  ⟨h, AllTopDecodedDistributionAgreement.forTopInput h top input⟩

/-! ## Exact allocation of the 12 representative-encoding declarations -/

/--
Complete consumer for the six complex-to-real representative-encoding
declarations: four raw certificates and two normalized embeddings.
-/
theorem realRepresentativeEncoding_api {I : Type uS} [Fintype I] :
    ExactStateEncoding
        (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn0 ∧
      ExactStateEncoding
        (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn1 ∧
      LosslessStateEncoding
        (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn0 State.complexTotalWeight
        State.realTotalWeight ∧
      LosslessStateEncoding
        (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn1 State.complexTotalWeight
        State.realTotalWeight ∧
      Function.Injective (realColumn0StateEmbedding I) ∧
      Function.Injective (realColumn1StateEmbedding I) :=
  ⟨realColumn0_exactStateEncoding,
    realColumn1_exactStateEncoding,
    realColumn0_losslessStateEncoding,
    realColumn1_losslessStateEncoding,
    (realColumn0StateEmbedding I).injective,
    (realColumn1StateEmbedding I).injective⟩

/--
Complete consumer for the six quaternion-to-complex representative-encoding
declarations: four raw certificates and two normalized embeddings.
-/
theorem complexRepresentativeEncoding_api {I : Type uS} [Fintype I] :
    ExactStateEncoding
        (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn0 ∧
      ExactStateEncoding
        (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn1 ∧
      LosslessStateEncoding
        (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn0 State.quaternionTotalWeight
        State.complexTotalWeight ∧
      LosslessStateEncoding
        (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn1 State.quaternionTotalWeight
        State.complexTotalWeight ∧
      Function.Injective (complexColumn0StateEmbedding I) ∧
      Function.Injective (complexColumn1StateEmbedding I) :=
  ⟨complexColumn0_exactStateEncoding,
    complexColumn1_exactStateEncoding,
    complexColumn0_losslessStateEncoding,
    complexColumn1_losslessStateEncoding,
    (complexColumn0StateEmbedding I).injective,
    (complexColumn1StateEmbedding I).injective⟩

/-! ## Concrete state-intertwining consumers -/

/-- Both canonical doubled-real columns instantiate exact state intertwining. -/
theorem realColumn_stateIntertwining_api
    {O : Type uOS} {I : Type uIS} [Fintype I]
    (A : Matrix O I ℂ) :
    StateIntertwining State.realColumn0 State.realColumn0 A
        (QuaternionicComputing.Matrix.realify A) ∧
      StateIntertwining State.realColumn1 State.realColumn1 A
        (QuaternionicComputing.Matrix.realify A) :=
  ⟨fun input ↦ State.realify_mulVec_realColumn0 A input,
    fun input ↦ State.realify_mulVec_realColumn1 A input⟩

/-- Both canonical doubled-complex columns instantiate exact state intertwining. -/
theorem complexColumn_stateIntertwining_api
    {O : Type uOS} {I : Type uIS} [Fintype I]
    (A : Matrix O I ℍ[ℝ]) :
    StateIntertwining State.complexColumn0 State.complexColumn0 A
        (QuaternionicComputing.Quaternion.complexify A) ∧
      StateIntertwining State.complexColumn1 State.complexColumn1 A
        (QuaternionicComputing.Quaternion.complexify A) :=
  ⟨fun input ↦ State.complexify_mulVec_complexColumn0 A input,
    fun input ↦ State.complexify_mulVec_complexColumn1 A input⟩

/-- Every normalized pure top rebit supplies the real state intertwining. -/
theorem allRebit_stateIntertwining_api
    {O : Type uOS} {I : Type uIS} [Fintype I]
    (A : Matrix O I ℂ) :
    AllTopStateIntertwining
      (fun top : State.Rebit ↦
        State.realTopCombination (top false) (top true))
      (fun top : State.Rebit ↦
        State.realTopCombination (top false) (top true))
      A (QuaternionicComputing.Matrix.realify A) := by
  intro top input
  exact State.realify_mulVec_realTopCombination
    A (top false) (top true) input

/-- Every normalized pure top qubit supplies the complex state intertwining. -/
theorem allQubit_stateIntertwining_api
    {O : Type uOS} {I : Type uIS} [Fintype I]
    (A : Matrix O I ℍ[ℝ]) :
    AllTopStateIntertwining
      (fun top : State.Qubit ↦
        State.complexTopCombination (top false) (top true))
      (fun top : State.Qubit ↦
        State.complexTopCombination (top false) (top true))
      A (QuaternionicComputing.Quaternion.complexify A) := by
  intro top input
  exact State.complexify_mulVec_complexTopCombination
    A (top false) (top true) input

/-! ## Concrete decoded basis-weight consumers -/

/-- Sum the two target-sector weights over one source outcome. -/
def sumSectorWeightDecoder {I : Type uO}
    (targetWeight : I ⊕ I → ℝ) (outcome : I) : ℝ :=
  targetWeight (Sum.inl outcome) + targetWeight (Sum.inr outcome)

/-- The two canonical real columns preserve every decoded source weight. -/
theorem realColumn_decodedBasisWeight_api
    {I : Type uO} (input : I → ℂ) :
    DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦ State.complexBasisWeight input outcome)
        (fun targetOutcome ↦
          State.realBasisWeight (State.realColumn0 input) targetOutcome) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦ State.complexBasisWeight input outcome)
        (fun targetOutcome ↦
          State.realBasisWeight (State.realColumn1 input) targetOutcome) := by
  constructor <;> funext outcome
  · exact State.realColumn0_bottomWeight input outcome
  · exact State.realColumn1_bottomWeight input outcome

/-- The two canonical complex columns preserve every decoded quaternionic weight. -/
theorem complexColumn_decodedBasisWeight_api
    {I : Type uO} (input : I → ℍ[ℝ]) :
    DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦ State.quaternionBasisWeight input outcome)
        (fun targetOutcome ↦
          State.complexBasisWeight (State.complexColumn0 input)
            targetOutcome) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦ State.quaternionBasisWeight input outcome)
        (fun targetOutcome ↦
          State.complexBasisWeight (State.complexColumn1 input)
            targetOutcome) := by
  constructor <;> funext outcome
  · exact State.complexColumn0_bottomWeight input outcome
  · exact State.complexColumn1_bottomWeight input outcome

/--
All normalized pure top rebits preserve all decoded complex source weights.
The quantifier says nothing about mixed density inputs or product factoring.
-/
theorem allRebit_decodedBasisWeight_api {I : Type uO} :
    AllTopDecodedBasisWeightAgreement sumSectorWeightDecoder
      (fun input : I → ℂ ↦ fun outcome ↦
        State.complexBasisWeight input outcome)
      (fun (top : State.Rebit) (input : I → ℂ) targetOutcome ↦
        State.realBasisWeight
          (State.realTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  exact State.realTopCombination_bottomWeight_of_rebit top input outcome

/--
All normalized pure top qubits preserve all decoded quaternionic source
weights, with the same strictly pure-parameter scope.
-/
theorem allQubit_decodedBasisWeight_api {I : Type uO} :
    AllTopDecodedBasisWeightAgreement sumSectorWeightDecoder
      (fun input : I → ℍ[ℝ] ↦ fun outcome ↦
        State.quaternionBasisWeight input outcome)
      (fun (top : State.Qubit) (input : I → ℍ[ℝ]) targetOutcome ↦
        State.complexBasisWeight
          (State.complexTopCombination (top false) (top true) input)
          targetOutcome) := by
  intro top input
  funext outcome
  exact State.complexTopCombination_bottomWeight_of_qubit top input outcome

/-! ## Concrete decoded distribution consumers -/

/--
Both canonical normalized real representatives have exactly the source
complex distribution after the two real sectors are decoded to the bottom
outcome type.
-/
theorem realColumns_decodedDistribution_api
    {I : Type uO} [Fintype I] (input : State.ComplexState I) :
    DecodedDistributionAgreement id
        (FiniteDistribution.ofNormalizedState State.complexWeight
          State.complexWeight_nonneg input)
        (State.realBottomDistribution (State.realColumn0State input)) ∧
      DecodedDistributionAgreement id
        (FiniteDistribution.ofNormalizedState State.complexWeight
          State.complexWeight_nonneg input)
        (State.realBottomDistribution (State.realColumn1State input)) := by
  constructor
  · change State.realBottomDistribution (State.realColumn0State input) =
      FiniteDistribution.ofNormalizedState State.complexWeight
        State.complexWeight_nonneg input
    exact State.realBottomDistribution_realColumn0State input
  · change State.realBottomDistribution (State.realColumn1State input) =
      FiniteDistribution.ofNormalizedState State.complexWeight
        State.complexWeight_nonneg input
    exact State.realBottomDistribution_realColumn1State input

/--
Every normalized pure top rebit gives the source complex distribution after
the real target sectors are decoded.  This is a concrete consumer of the
all-top distribution relation, not a mixed-top or channel theorem.
-/
theorem allRebit_decodedDistribution_api {I : Type uO} [Fintype I] :
    AllTopDecodedDistributionAgreement id
      (fun input : State.ComplexState I ↦
        FiniteDistribution.ofNormalizedState State.complexWeight
          State.complexWeight_nonneg input)
      (fun top input ↦
        State.realBottomDistribution (State.realTopState top input)) := by
  intro top input
  apply FiniteDistribution.ext
  intro outcome
  change State.bottomRealWeight
      (State.realTopCombination (top false) (top true) input) outcome =
    State.complexBasisWeight input outcome
  exact State.realTopCombination_bottomWeight_of_rebit top input outcome

/-! ## Constructive singleton and empty boundaries -/

/-- The normalized one-coordinate complex state with amplitude one. -/
def unitComplexState : State.ComplexState Unit :=
  ⟨fun _ ↦ 1, by
    simp [State.totalWeight, State.basisWeight, State.complexWeight]⟩

/-- The normalized one-coordinate quaternionic state with amplitude one. -/
def unitQuaternionState : State.QuaternionState Unit :=
  ⟨fun _ ↦ 1, by
    simp [State.totalWeight, State.basisWeight, State.quaternionWeight,
      _root_.Quaternion.normSq_def']⟩

/-- The computational-basis pure top rebit `|0⟩`. -/
def unitRebitTop : State.Rebit :=
  ⟨fun bit ↦ if bit then 0 else 1, by
    simp [State.totalWeight, State.basisWeight, State.realWeight,
      Fintype.univ_bool]⟩

/-- The computational-basis pure top qubit `|0⟩`. -/
def unitQubitTop : State.Qubit :=
  ⟨fun bit ↦ if bit then 0 else 1, by
    simp [State.totalWeight, State.basisWeight, State.complexWeight,
      Fintype.univ_bool]⟩

/--
The singleton boundary has actual normalized sources and top parameters and
therefore exercises both all-top decoded relations non-vacuously.
-/
theorem unit_allTop_decodedBasisWeight_api :
    DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦ State.complexBasisWeight unitComplexState outcome)
        (fun targetOutcome ↦
          State.realBasisWeight
            (State.realTopCombination (unitRebitTop false)
              (unitRebitTop true) unitComplexState)
            targetOutcome) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (fun outcome ↦
          State.quaternionBasisWeight unitQuaternionState outcome)
        (fun targetOutcome ↦
          State.complexBasisWeight
            (State.complexTopCombination (unitQubitTop false)
              (unitQubitTop true) unitQuaternionState)
            targetOutcome) :=
  ⟨AllTopDecodedBasisWeightAgreement.forTopInput
      (allRebit_decodedBasisWeight_api (I := Unit))
      unitRebitTop unitComplexState,
    AllTopDecodedBasisWeightAgreement.forTopInput
      (allQubit_decodedBasisWeight_api (I := Unit))
      unitQubitTop unitQuaternionState⟩

/-- A raw complex column on the empty index type exists constructively. -/
def emptyComplexColumn : Empty → ℂ := fun index ↦ nomatch index

/-- A raw quaternionic column on the empty index type exists constructively. -/
def emptyQuaternionColumn : Empty → ℍ[ℝ] := fun index ↦ nomatch index

/-- No normalized complex state exists on the empty coordinate type. -/
theorem emptyComplexState_isEmpty : IsEmpty (State.ComplexState Empty) :=
  ⟨fun state ↦ by
    have h := state.property
    simp [State.totalWeight] at h⟩

/-- No normalized quaternionic state exists on the empty coordinate type. -/
theorem emptyQuaternionState_isEmpty :
    IsEmpty (State.QuaternionState Empty) :=
  ⟨fun state ↦ by
    have h := state.property
    simp [State.totalWeight] at h⟩

/--
Raw exact reconstruction remains constructive on `Empty`; normalized source
states are impossible rather than silently supplied to a vacuous consumer.
-/
theorem empty_rawEncoding_normalizedBoundary_api :
    State.complexOfRealColumn0 (State.realColumn0 emptyComplexColumn) =
        emptyComplexColumn ∧
      State.quaternionOfComplexColumn0
          (State.complexColumn0 emptyQuaternionColumn) =
        emptyQuaternionColumn ∧
      IsEmpty (State.ComplexState Empty) ∧
      IsEmpty (State.QuaternionState Empty) :=
  ⟨State.complexOfRealColumn0_realColumn0 emptyComplexColumn,
    State.quaternionOfComplexColumn0_leftInverse emptyQuaternionColumn,
    emptyComplexState_isEmpty,
    emptyQuaternionState_isEmpty⟩

/-! ## Existing ray-descent and top-factor boundaries -/

/--
The canonical real representative does not descend to an ordinary real ray
on `Unit`, and a checked normalized encoding need not factor into independent
pure top and bottom columns.
-/
theorem ordinaryRealRay_nonDescent_nonProduct_boundary :
    (¬ ∃ lift : State.ComplexRay Unit → State.RealRay (Unit ⊕ Unit),
      ∀ source : State.ComplexState Unit,
        lift (State.ComplexRay.mk source) =
          State.RealRay.mk (State.realColumn0State source)) ∧
      State.RealRay.mk
          (State.realColumn0State
            (State.ComplexState.rightPhase unitComplexState Complex.I
              Complex.normSq_I)) ≠
        State.RealRay.mk (State.realColumn0State unitComplexState) ∧
      ¬ QuaternionicComputing.Simulation.IsPureTopBottomProduct
        (fun target ↦
          QuaternionicComputing.Simulation.NonProductWitness.encodedState
            target) :=
  ⟨State.no_complexRay_realColumn0_lift,
    State.realColumn0State_rightPhase_I_realRay_ne unitComplexState,
    QuaternionicComputing.Simulation.NonProductWitness.encodedState_not_pureTopBottomProduct⟩

end QuaternionicComputing.Semantics.SimulationAudit

#print axioms QuaternionicComputing.Semantics.SimulationAudit.exactStateEncoding_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.decodedDistributionAgreement_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.realRepresentativeEncoding_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.allRebit_stateIntertwining_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.allQubit_decodedBasisWeight_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.empty_rawEncoding_normalizedBoundary_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.ordinaryRealRay_nonDescent_nonProduct_boundary
