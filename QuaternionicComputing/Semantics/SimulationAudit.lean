module

public import QuaternionicComputing.Semantics.SimulationEncoding
public import QuaternionicComputing.Semantics.SimulationWrappers
public import QuaternionicComputing.Semantics.SimulationOutcomes
public import QuaternionicComputing.Circuit.OrderingWitness
public import QuaternionicComputing.State.RealificationOrbitBoundary
public import QuaternionicComputing.State.RealificationOrbitObservables
public import QuaternionicComputing.Simulation.NonProductWitness
public import QuaternionicComputing.Simulation.Examples

/-!
# Directional simulation semantic audit

This non-root leaf consumes the Stage 9A relation and representative-encoding
APIs, the Stage 9B operator/state wrapper API, and the Stage 9C decoded-outcome
API. Its abstract aggregate
sections allocate every stable declaration from those leaves exactly once,
while the concrete sections exercise the intended scalar, index, coefficient,
schedule, compiler, and boundary policies.

The top-sector consumers below quantify `Rebit` and `Qubit` values exactly.
They are normalized coefficient parameter types, not mixed density inputs or
proofs that the encoded target column factors as a top/bottom product.  The final
boundary section reuses the existing ordinary-real-ray non-descent and
nonproduct witnesses. The Stage 9C aggregates consume full target
distributions through explicit one- and two-wire decoders. Nothing here claims
same-space, ray, product, mixed-top, channel, or all-effect equality.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics.SimulationAudit

open QuaternionicComputing.State
open QuaternionicComputing.Circuit
open QuaternionicComputing.Simulation
open QuaternionicComputing.Simulation.Examples
open QuaternionicComputing.Circuit.OrderingWitness

universe uS uT uU uOS uIS uOT uIT uOU uIU uO uM uP uTop uInput

/-! ## Exact allocation of the 38 generic relation declarations -/

/-
Allocation, in source order:

* `ExactStateEncoding`: `5`;
* `LosslessStateEncoding`: `6`;
* `ExactOperatorEmbedding`: `4`;
* `StateIntertwining`: `4`;
* `AllTopStateIntertwining`: `2`;
* `DecodedBasisWeightAgreement`: `5`;
* `DecodedDistributionAgreement`: `8`;
* `AllTopDecodedBasisWeightAgreement`: `2`;
* `AllTopDecodedDistributionAgreement`: `2`.

Thus the nine aggregates below allocate `5+6+4+4+2+5+8+2+2 = 38`
stable declarations exactly once.
-/

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

/-! ## Exact allocation of the 20 representative-encoding declarations -/

/-
The next two aggregates allocate the ten real and ten complex declarations in
`SimulationEncoding`: exact reconstruction, right inverses, losslessness, raw
real-linear equivalences, and normalized representative equivalences.
Together the two stable leaves therefore contribute exactly `38 + 20 = 58`
declarations to this audit.
-/

/--
Complete consumer for all ten complex-to-real representative-encoding
declarations.
-/
theorem realRepresentativeEncoding_api {I : Type uS} [Fintype I] :
    ExactStateEncoding
        (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn0 ∧
      ExactStateEncoding
        (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn1 ∧
      Function.RightInverse
        (State.complexOfRealColumn0 : (I ⊕ I → ℝ) → (I → ℂ))
        State.realColumn0 ∧
      Function.RightInverse
        (State.complexOfRealColumn1 : (I ⊕ I → ℝ) → (I → ℂ))
        State.realColumn1 ∧
      LosslessStateEncoding
        (State.realColumn0 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn0 State.complexTotalWeight
        State.realTotalWeight ∧
      LosslessStateEncoding
        (State.realColumn1 : (I → ℂ) → (I ⊕ I → ℝ))
        State.complexOfRealColumn1 State.complexTotalWeight
        State.realTotalWeight ∧
      Function.Bijective (realColumn0LinearEquiv I) ∧
      Function.Bijective (realColumn1LinearEquiv I) ∧
      Function.Bijective (realColumn0StateEquiv I) ∧
      Function.Bijective (realColumn1StateEquiv I) :=
  ⟨realColumn0_exactStateEncoding,
    realColumn1_exactStateEncoding,
    realColumn0_rightInverse,
    realColumn1_rightInverse,
    realColumn0_losslessStateEncoding,
    realColumn1_losslessStateEncoding,
    (realColumn0LinearEquiv I).bijective,
    (realColumn1LinearEquiv I).bijective,
    (realColumn0StateEquiv I).bijective,
    (realColumn1StateEquiv I).bijective⟩

/--
Complete consumer for all ten quaternion-to-complex representative-encoding
declarations.
-/
theorem complexRepresentativeEncoding_api {I : Type uS} [Fintype I] :
    ExactStateEncoding
        (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn0 ∧
      ExactStateEncoding
        (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn1 ∧
      Function.RightInverse
        (State.quaternionOfComplexColumn0 :
          (I ⊕ I → ℂ) → (I → ℍ[ℝ]))
        State.complexColumn0 ∧
      Function.RightInverse
        (State.quaternionOfComplexColumn1 :
          (I ⊕ I → ℂ) → (I → ℍ[ℝ]))
        State.complexColumn1 ∧
      LosslessStateEncoding
        (State.complexColumn0 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn0 State.quaternionTotalWeight
        State.complexTotalWeight ∧
      LosslessStateEncoding
        (State.complexColumn1 : (I → ℍ[ℝ]) → (I ⊕ I → ℂ))
        State.quaternionOfComplexColumn1 State.quaternionTotalWeight
        State.complexTotalWeight ∧
      Function.Bijective (complexColumn0LinearEquiv I) ∧
      Function.Bijective (complexColumn1LinearEquiv I) ∧
      Function.Bijective (complexColumn0StateEquiv I) ∧
      Function.Bijective (complexColumn1StateEquiv I) :=
  ⟨complexColumn0_exactStateEncoding,
    complexColumn1_exactStateEncoding,
    complexColumn0_rightInverse,
    complexColumn1_rightInverse,
    complexColumn0_losslessStateEncoding,
    complexColumn1_losslessStateEncoding,
    (complexColumn0LinearEquiv I).bijective,
    (complexColumn1LinearEquiv I).bijective,
    (complexColumn0StateEquiv I).bijective,
    (complexColumn1StateEquiv I).bijective⟩

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

/--
The normalized bottom distribution obtained by summing the two complex target
sectors.  This audit-local decoder is the quaternion-to-complex analogue of
the stable real-sector bottom distribution.
-/
def complexBottomDistribution {I : Type uO} [Fintype I]
    (target : State.ComplexState (I ⊕ I)) : FiniteDistribution I where
  weight outcome := State.bottomComplexWeight target outcome
  nonnegative outcome := add_nonneg
    (State.ComplexState.basisWeight_nonneg target (Sum.inl outcome))
    (State.ComplexState.basisWeight_nonneg target (Sum.inr outcome))
  normalized := by
    rw [← State.complexTotalWeight_eq_sum_bottomComplexWeight]
    exact target.property

/--
Every normalized pure top qubit gives exactly the source quaternionic
distribution after the two complex target sectors are decoded.
-/
theorem allQubit_decodedDistribution_api {I : Type uO} [Fintype I] :
    AllTopDecodedDistributionAgreement id
      (fun input : State.QuaternionState I ↦
        FiniteDistribution.ofNormalizedState State.quaternionWeight
          State.quaternionWeight_nonneg input)
      (fun top input ↦ complexBottomDistribution
        (State.complexTopState top input)) := by
  intro top input
  apply FiniteDistribution.ext
  intro outcome
  change State.bottomComplexWeight
      (State.complexTopCombination (top false) (top true) input) outcome =
    State.quaternionBasisWeight input outcome
  exact State.complexTopCombination_bottomWeight_of_qubit top input outcome

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
therefore exercises both scalar transitions' all-top decoded basis-weight
relations non-vacuously.
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

/-! ## Exact allocation of the 16 Stage 9B wrapper declarations -/

/-
The six aggregates below allocate the stable wrapper leaf in source order as
`2 + 3 + 4 + 3 + 2 + 2 = 16`.  Canonical coefficient pairs are recovered from
the stronger all-coefficient statements.  The additional empty-input,
zero-wire, schedule-gap, and identity-compiler conjuncts use actual raw values;
none manufactures a normalized state on `Empty`.
-/

/--
Complete consumer for both rectangular matrix-intertwining wrappers, including
both canonical coefficient pairs and constructive raw `Empty` inputs.
-/
theorem matrixStateIntertwining_wrappers_api
    {O : Type uOS} {I : Type uIS} [Fintype I]
    (complexMatrix : Matrix O I ℂ)
    (quaternionMatrix : Matrix O I ℍ[ℝ]) :
    AllTopStateIntertwining
        (fun top : ℝ × ℝ ↦ State.realTopCombination top.1 top.2)
        (fun top : ℝ × ℝ ↦ State.realTopCombination top.1 top.2)
        complexMatrix
        (QuaternionicComputing.Matrix.realify complexMatrix) ∧
      AllTopStateIntertwining
        (fun top : ℂ × ℂ ↦ State.complexTopCombination top.1 top.2)
        (fun top : ℂ × ℂ ↦ State.complexTopCombination top.1 top.2)
        quaternionMatrix
        (QuaternionicComputing.Quaternion.complexify quaternionMatrix) ∧
      StateIntertwining (State.realTopCombination 1 0)
        (State.realTopCombination 1 0) complexMatrix
        (QuaternionicComputing.Matrix.realify complexMatrix) ∧
      StateIntertwining (State.realTopCombination 0 1)
        (State.realTopCombination 0 1) complexMatrix
        (QuaternionicComputing.Matrix.realify complexMatrix) ∧
      StateIntertwining (State.complexTopCombination 1 0)
        (State.complexTopCombination 1 0) quaternionMatrix
        (QuaternionicComputing.Quaternion.complexify quaternionMatrix) ∧
      StateIntertwining (State.complexTopCombination 0 1)
        (State.complexTopCombination 0 1) quaternionMatrix
        (QuaternionicComputing.Quaternion.complexify quaternionMatrix) ∧
      StateIntertwining (State.realTopCombination 1 0)
        (State.realTopCombination 1 0)
        (0 : Matrix Unit Empty ℂ)
        (QuaternionicComputing.Matrix.realify (0 : Matrix Unit Empty ℂ)) ∧
      StateIntertwining (State.complexTopCombination 1 0)
        (State.complexTopCombination 1 0)
        (0 : Matrix Unit Empty ℍ[ℝ])
        (QuaternionicComputing.Quaternion.complexify
          (0 : Matrix Unit Empty ℍ[ℝ])) := by
  have hReal := realifyMatrix_allCoefficient_stateIntertwining complexMatrix
  have hComplex :=
    complexifyMatrix_allCoefficient_stateIntertwining quaternionMatrix
  refine ⟨hReal, hComplex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      (AllTopStateIntertwining.forTop hReal ((1, 0) : ℝ × ℝ))
  · simpa using
      (AllTopStateIntertwining.forTop hReal ((0, 1) : ℝ × ℝ))
  · simpa using
      (AllTopStateIntertwining.forTop hComplex ((1, 0) : ℂ × ℂ))
  · simpa using
      (AllTopStateIntertwining.forTop hComplex ((0, 1) : ℂ × ℂ))
  · intro input
    exact State.realify_mulVec_realTopCombination
      (0 : Matrix Unit Empty ℂ) 1 0 input
  · intro input
    exact State.complexify_mulVec_complexTopCombination
      (0 : Matrix Unit Empty ℍ[ℝ]) 1 0 input

/--
Complete consumer for the Equation 63 reindexing wrapper and both placed-gate
operator wrappers.  Source/output indices remain independent and the gates are
actual locality-bearing values.
-/
theorem reindexPlacement_wrappers_api
    {O : Type uOS} {I : Type uIS} {W : Type uT} [Fintype W]
    (source : Matrix O I ℍ[ℝ])
    (realGate : PlacedGate ℂ W)
    (quaternionGate : PlacedGate ℍ[ℝ] W) :
    ExactOperatorEmbedding
        (fun matrix ↦
          Matrix.reindex
            (QuaternionicComputing.Quaternion.eq63PaperToComposed O).symm
            (QuaternionicComputing.Quaternion.eq63PaperToComposed I).symm
            (QuaternionicComputing.Matrix.realify
              (QuaternionicComputing.Quaternion.complexify matrix)))
        source (QuaternionicComputing.Quaternion.directRealify source) ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireRealify
        realGate.denote
        (QuaternionicComputing.Circuit.realifyPlacedGate realGate).denote ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireComplexify
        quaternionGate.denote
        (QuaternionicComputing.Circuit.complexifyPlacedGate
          quaternionGate).denote :=
  ⟨directRealify_exactOperatorEmbedding source,
    realifyPlacedGate_exactOperatorEmbedding realGate,
    complexifyPlacedGate_exactOperatorEmbedding quaternionGate⟩

/-- Complete consumer for all four primary ordered-circuit wrappers. -/
theorem primaryCircuit_wrappers_api
    {W : Type uT} [Fintype W]
    (complexCircuit : OrderedCircuit ℂ W)
    (quaternionCircuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding QuaternionicComputing.Circuit.wireRealify
        (OrderedCircuit.eval complexCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.realifyCircuit complexCircuit)) ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireComplexify
        (OrderedCircuit.eval quaternionCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            quaternionCircuit)) ∧
      AllTopStateIntertwining
        (fun top : ℝ × ℝ ↦
          QuaternionicComputing.Simulation.wireRealTopCombination
            top.1 top.2)
        (fun top : ℝ × ℝ ↦
          QuaternionicComputing.Simulation.wireRealTopCombination
            top.1 top.2)
        (OrderedCircuit.eval complexCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.realifyCircuit complexCircuit)) ∧
      AllTopStateIntertwining
        (fun top : ℂ × ℂ ↦
          QuaternionicComputing.Simulation.wireComplexTopCombination
            top.1 top.2)
        (fun top : ℂ × ℂ ↦
          QuaternionicComputing.Simulation.wireComplexTopCombination
            top.1 top.2)
        (OrderedCircuit.eval quaternionCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            quaternionCircuit)) ∧
      StateIntertwining
        (QuaternionicComputing.Simulation.wireRealTopCombination 1 0)
        (QuaternionicComputing.Simulation.wireRealTopCombination 1 0)
        (OrderedCircuit.eval complexCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.realifyCircuit complexCircuit)) ∧
      StateIntertwining
        (QuaternionicComputing.Simulation.wireRealTopCombination 0 1)
        (QuaternionicComputing.Simulation.wireRealTopCombination 0 1)
        (OrderedCircuit.eval complexCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.realifyCircuit complexCircuit)) ∧
      StateIntertwining
        (QuaternionicComputing.Simulation.wireComplexTopCombination 1 0)
        (QuaternionicComputing.Simulation.wireComplexTopCombination 1 0)
        (OrderedCircuit.eval quaternionCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            quaternionCircuit)) ∧
      StateIntertwining
        (QuaternionicComputing.Simulation.wireComplexTopCombination 0 1)
        (QuaternionicComputing.Simulation.wireComplexTopCombination 0 1)
        (OrderedCircuit.eval quaternionCircuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            quaternionCircuit)) := by
  have hRealState :=
    realifyCircuit_allCoefficient_stateIntertwining complexCircuit
  have hComplexState :=
    complexifyCircuit_allCoefficient_stateIntertwining quaternionCircuit
  exact ⟨realifyCircuit_exactOperatorEmbedding complexCircuit,
    complexifyCircuit_exactOperatorEmbedding quaternionCircuit,
    hRealState, hComplexState,
    AllTopStateIntertwining.forTop hRealState ((1, 0) : ℝ × ℝ),
    AllTopStateIntertwining.forTop hRealState ((0, 1) : ℝ × ℝ),
    AllTopStateIntertwining.forTop hComplexState ((1, 0) : ℂ × ℂ),
    AllTopStateIntertwining.forTop hComplexState ((0, 1) : ℂ × ℂ)⟩

/--
Complete consumer for the three scheduled wrappers.  The inequality conjunct
uses the library's explicit two-schedule quaternionic witness rather than a
hypothetical inequality premise.
-/
theorem scheduledCircuit_wrappers_api
    {ι : Type uS} [Fintype ι] [DecidableEq ι]
    {W : Type uT} [Fintype W] {precedes : ι → ι → Prop}
    (schedule : LegalSchedule ι precedes)
    (gates : ι → PlacedGate ℍ[ℝ] W) :
    ExactOperatorEmbedding QuaternionicComputing.Circuit.wireComplexify
        (schedule.scheduledEval gates)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            (schedule.scheduledCircuit gates))) ∧
      AllTopStateIntertwining
        (fun top : ℂ × ℂ ↦
          QuaternionicComputing.Simulation.wireComplexTopCombination
            top.1 top.2)
        (fun top : ℂ × ℂ ↦
          QuaternionicComputing.Simulation.wireComplexTopCombination
            top.1 top.2)
        (schedule.scheduledEval gates)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            (schedule.scheduledCircuit gates))) ∧
      OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            (iThenJSchedule.scheduledCircuit
              gateFamily)) ≠
        OrderedCircuit.eval
          (QuaternionicComputing.Simulation.complexifyCircuit
            (jThenISchedule.scheduledCircuit
              gateFamily)) :=
  ⟨scheduledComplexifyCircuit_exactOperatorEmbedding schedule gates,
    scheduledComplexifyCircuit_allCoefficient_stateIntertwining schedule gates,
    scheduledComplexifyCircuit_eval_ne_of_source_ne
      iThenJSchedule
      jThenISchedule
      gateFamily
      scheduled_operators_ne⟩

/--
Complete consumer for the composed quaternion-to-real wrappers, including the
canonical nested inner-complex/outer-real coefficient specialization.
-/
theorem composedCircuit_wrappers_api
    {W : Type uT} [Fintype W]
    (circuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding
        (QuaternionicComputing.Circuit.wireRealify ∘
          QuaternionicComputing.Circuit.wireComplexify)
        (OrderedCircuit.eval circuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.quaternionToRealCircuit circuit)) ∧
      AllTopStateIntertwining
        (fun top : (ℂ × ℂ) × (ℝ × ℝ) ↦
          QuaternionicComputing.Simulation.wireRealTopCombination
              top.2.1 top.2.2 ∘
            QuaternionicComputing.Simulation.wireComplexTopCombination
              top.1.1 top.1.2)
        (fun top : (ℂ × ℂ) × (ℝ × ℝ) ↦
          QuaternionicComputing.Simulation.wireRealTopCombination
              top.2.1 top.2.2 ∘
            QuaternionicComputing.Simulation.wireComplexTopCombination
              top.1.1 top.1.2)
        (OrderedCircuit.eval circuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.quaternionToRealCircuit circuit)) ∧
      StateIntertwining
        (QuaternionicComputing.Simulation.wireRealTopCombination 1 0 ∘
          QuaternionicComputing.Simulation.wireComplexTopCombination 1 0)
        (QuaternionicComputing.Simulation.wireRealTopCombination 1 0 ∘
          QuaternionicComputing.Simulation.wireComplexTopCombination 1 0)
        (OrderedCircuit.eval circuit)
        (OrderedCircuit.eval
          (QuaternionicComputing.Simulation.quaternionToRealCircuit circuit)) := by
  have hOperator := quaternionToRealCircuit_exactOperatorEmbedding circuit
  have hState :=
    quaternionToRealCircuit_allCoefficient_stateIntertwining circuit
  refine ⟨hOperator, hState, ?_⟩
  simpa using
    (AllTopStateIntertwining.forTop hState
      (((1, 0), (1, 0)) : (ℂ × ℂ) × (ℝ × ℝ)))

/--
The identity gate compiler witnesses that `ExactGateCompiler` is inhabited
without asserting a finite primitive library or a synthesis procedure.
-/
def identityExactGateCompiler (R W : Type*) [Semiring R] [Fintype W] :
    ExactGateCompiler R W where
  primitive := fun _ ↦ True
  compileGate := fun gate ↦ [gate]
  compileGate_primitive := by
    intro gate compiled hmem
    trivial
  eval_compileGate := by
    intro gate
    simp

/--
Complete consumer for both conditional compiler wrappers.  The final two
conjuncts instantiate the local identity compilers on actual zero-wire empty
circuits; no normalized empty state is required.
-/
theorem compiledCircuit_wrappers_api
    {W : Type uT} [Fintype W]
    (complexCircuit : OrderedCircuit ℂ W)
    (quaternionCircuit : OrderedCircuit ℍ[ℝ] W) :
    ExactOperatorEmbedding QuaternionicComputing.Circuit.wireRealify
        (OrderedCircuit.eval complexCircuit)
        (OrderedCircuit.eval
          ((identityExactGateCompiler ℝ (AddedWire W)).compileCircuit
            (QuaternionicComputing.Simulation.realifyCircuit
              complexCircuit))) ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireComplexify
        (OrderedCircuit.eval quaternionCircuit)
        (OrderedCircuit.eval
          ((identityExactGateCompiler ℂ (AddedWire W)).compileCircuit
            (QuaternionicComputing.Simulation.complexifyCircuit
              quaternionCircuit))) ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireRealify
        (OrderedCircuit.eval ([] : OrderedCircuit ℂ Empty))
        (OrderedCircuit.eval
          ((identityExactGateCompiler ℝ (AddedWire Empty)).compileCircuit
            (QuaternionicComputing.Simulation.realifyCircuit
              ([] : OrderedCircuit ℂ Empty)))) ∧
      ExactOperatorEmbedding QuaternionicComputing.Circuit.wireComplexify
        (OrderedCircuit.eval ([] : OrderedCircuit ℍ[ℝ] Empty))
        (OrderedCircuit.eval
          ((identityExactGateCompiler ℂ (AddedWire Empty)).compileCircuit
            (QuaternionicComputing.Simulation.complexifyCircuit
              ([] : OrderedCircuit ℍ[ℝ] Empty)))) :=
  ⟨compileRealifyCircuit_exactOperatorEmbedding
      (identityExactGateCompiler ℝ (AddedWire W)) complexCircuit,
    compileComplexifyCircuit_exactOperatorEmbedding
      (identityExactGateCompiler ℂ (AddedWire W)) quaternionCircuit,
    QuaternionicComputing.Simulation.eval_compile_realifyCircuit
      (identityExactGateCompiler ℝ (AddedWire Empty)) [],
    QuaternionicComputing.Simulation.eval_compile_complexifyCircuit
      (identityExactGateCompiler ℂ (AddedWire Empty)) []⟩

/-! ## Exact allocation of the 18 Stage 9C outcome wrappers -/

/-
The five aggregates below allocate the stable outcome wrapper leaf in source
order as `2 + 4 + 4 + 4 + 4 = 18`.  They use full target distributions and the
stable explicit decoders; none uses `id` to hide an added-wire carrier.
-/

/-! ### Concrete normalized tops and zero-wire states -/

/-- Computational-basis rebit `|0⟩`. -/
def outcomeTopRebitZero : Rebit :=
  ⟨fun bit ↦ if bit then 0 else 1, by
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool]⟩

/-- Computational-basis rebit `|1⟩`. -/
def outcomeTopRebitOne : Rebit :=
  ⟨fun bit ↦ if bit then 1 else 0, by
    simp [totalWeight, basisWeight, realWeight, Fintype.univ_bool]⟩

/-- Computational-basis qubit `|0⟩`. -/
def outcomeTopQubitZero : Qubit :=
  ⟨fun bit ↦ if bit then 0 else 1, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

/-- Computational-basis qubit `|1⟩`. -/
def outcomeTopQubitOne : Qubit :=
  ⟨fun bit ↦ if bit then 1 else 0, by
    simp [totalWeight, basisWeight, complexWeight, Fintype.univ_bool]⟩

/-- One-coordinate raw complex column used by both canonical rebit tops. -/
def outcomeUnitComplexColumn : Unit → ℂ := fun _ ↦ 1

/-- Genuinely quaternionic raw `j` column used by both canonical qubit tops. -/
def outcomeUnitQuaternionJColumn : Unit → ℍ[ℝ] := fun _ ↦ QuaternionicComputing.Quaternion.j

/-- Normalized source state on the singleton zero-wire basis. -/
def outcomeZeroWireComplexState : ComplexState (BitBasis Empty) :=
  ⟨complexOneColumn, by
    simp [totalWeight, basisWeight, complexWeight,
      complexOneColumn, bitBasisEmpty_eq_emptyBasis]⟩

/-- Normalized quaternionic source state on the singleton zero-wire basis. -/
def outcomeZeroWireQuaternionState : QuaternionState (BitBasis Empty) :=
  ⟨quaternionOneColumn, by
    simp [totalWeight, basisWeight, quaternionWeight,
      quaternionOneColumn, _root_.Quaternion.normSq_def',
      bitBasisEmpty_eq_emptyBasis]⟩

/-- The scalar-`I` zero-wire example gate is genuinely locally unitary. -/
theorem outcomeComplexIGate_locallyUnitary :
    complexIGate.IsLocallyUnitary := by
  rw [complexIGate, PlacedGate.isLocallyUnitary_ofSplit]
  constructor <;> ext x y
  all_goals
    have hx : x = emptyBasis := Subsingleton.elim _ _
    have hy : y = emptyBasis := Subsingleton.elim _ _
    subst x
    subst y
    simp [complexILocal, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The scalar-`I` one-gate circuit has locally unitary gates. -/
theorem outcomeComplexICircuit_locallyUnitary :
    complexICircuit.IsLocallyUnitary := by
  simp [complexICircuit, OrderedCircuit.IsLocallyUnitary,
    outcomeComplexIGate_locallyUnitary]

/-- The scalar-`j` zero-wire example gate is genuinely locally unitary. -/
theorem outcomeQuaternionJGate_locallyUnitary :
    quaternionJGate.IsLocallyUnitary := by
  rw [quaternionJGate, PlacedGate.isLocallyUnitary_ofSplit]
  constructor <;> ext x y
  all_goals
    have hx : x = emptyBasis := Subsingleton.elim _ _
    have hy : y = emptyBasis := Subsingleton.elim _ _
    subst x
    subst y
    simp [quaternionJLocal, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The scalar-`j` one-gate circuit has locally unitary gates. -/
theorem outcomeQuaternionJCircuit_locallyUnitary :
    quaternionJCircuit.IsLocallyUnitary := by
  simp [quaternionJCircuit, OrderedCircuit.IsLocallyUnitary,
    outcomeQuaternionJGate_locallyUnitary]

/-- Every gate in the concrete two-gate scheduling witness is locally unitary. -/
theorem outcomeWitnessGateFamily_locallyUnitary (q : Bool) :
    (gateFamily q).IsLocallyUnitary := by
  cases q
  · exact iGate_locallyUnitary
  · exact jGate_locallyUnitary

/-! ### Decoder and concrete-source infrastructure allocation -/

/--
Complete consumer for the ten public decoder declarations. The one-wire
distribution is also checked against the deterministic `tailBits` pushforward,
and the nested decoder visibly removes the outer wire before the inner wire.
-/
theorem outcomeDecoder_api
    {W : Type uT} [Finite W]
    (genericWeight : Unit ⊕ Unit → ℝ)
    (oneWire : FiniteDistribution (BitBasis (AddedWire W)))
    (twoWire : FiniteDistribution (BitBasis (AddedWire (AddedWire W))))
    (outcome : BitBasis W) :
    sumSectorWeightDecoder genericWeight () =
        genericWeight (Sum.inl ()) + genericWeight (Sum.inr ()) ∧
      addedWireWeightDecoder oneWire.weight outcome =
        oneWire.weight (addedBasisEquiv W (Sum.inl outcome)) +
          oneWire.weight (addedBasisEquiv W (Sum.inr outcome)) ∧
      (addedWireDistributionDecoder oneWire).weight outcome =
        addedWireWeightDecoder oneWire.weight outcome ∧
      (addedWireDistributionDecoder oneWire).weight =
        addedWireWeightDecoder oneWire.weight ∧
      addedWireDistributionDecoder oneWire = oneWire.pushforward tailBits ∧
      twoAddedWireWeightDecoder twoWire.weight outcome =
        addedWireWeightDecoder (W := W)
          (addedWireWeightDecoder (W := AddedWire W) twoWire.weight)
          outcome ∧
      twoAddedWireDistributionDecoder twoWire =
        addedWireDistributionDecoder (W := W)
          (addedWireDistributionDecoder (W := AddedWire W) twoWire) ∧
      (twoAddedWireDistributionDecoder twoWire).weight outcome =
        twoAddedWireWeightDecoder twoWire.weight outcome ∧
      (twoAddedWireDistributionDecoder twoWire).weight =
        twoAddedWireWeightDecoder twoWire.weight :=
  ⟨rfl, rfl,
    addedWireDistributionDecoder_weight oneWire outcome,
    addedWireDistributionDecoder_compat oneWire,
    addedWireDistributionDecoder_eq_pushforward oneWire,
    rfl, rfl,
    twoAddedWireDistributionDecoder_weight twoWire outcome,
    twoAddedWireDistributionDecoder_compat twoWire⟩

/--
Complete consumer for the eight new concrete postprocessing declarations,
using the real scalar-`I` target and the composed scalar-`j` target rather than
abstract placeholders.
-/
theorem outcomePostprocessing_api :
    addedWireDistributionDecoder
        (FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg
          (realifyCircuitOutput complexICircuit
            outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
            outcomeZeroWireComplexState)) =
      addedWireBottomDistribution realWeight_nonneg
        (realifyCircuitOutput complexICircuit
          outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
          outcomeZeroWireComplexState) ∧
      realifyCircuitFullOutputDistribution complexICircuit
          outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
          outcomeZeroWireComplexState =
        FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg
          (realifyCircuitOutput complexICircuit
            outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
            outcomeZeroWireComplexState) ∧
      complexifyCircuitFullOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeZeroWireQuaternionState =
        FiniteDistribution.ofNormalizedState complexWeight
          complexWeight_nonneg
          (complexifyCircuitOutput quaternionJCircuit
            outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
            outcomeZeroWireQuaternionState) ∧
      quaternionToRealCircuitFullOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeTopRebitZero outcomeZeroWireQuaternionState =
        FiniteDistribution.ofNormalizedState realWeight realWeight_nonneg
          (quaternionToRealCircuitOutput quaternionJCircuit
            outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
            outcomeTopRebitZero outcomeZeroWireQuaternionState) ∧
      quaternionToRealCircuitBottomDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeTopRebitZero outcomeZeroWireQuaternionState =
        twoAddedWireDistributionDecoder
          (quaternionToRealCircuitFullOutputDistribution quaternionJCircuit
            outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
            outcomeTopRebitZero outcomeZeroWireQuaternionState) ∧
      quaternionToRealCircuitBottomDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeTopRebitZero outcomeZeroWireQuaternionState =
        quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState ∧
      (quaternionToRealCircuitBottomDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeTopRebitZero outcomeZeroWireQuaternionState).eventWeight
            {emptyBasis} =
        (quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState).eventWeight {emptyBasis} ∧
      (quaternionToRealCircuitBottomDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeTopRebitZero outcomeZeroWireQuaternionState).pushforward
            (fun _ ↦ true) =
        (quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState).pushforward (fun _ ↦ true) := by
  classical
  exact ⟨addedWireDistributionDecoder_ofNormalizedState _ _,
    rfl, rfl, rfl, rfl,
    quaternionToRealCircuitBottomDistribution_eq quaternionJCircuit
      outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
      outcomeTopRebitZero outcomeZeroWireQuaternionState,
    quaternionToRealCircuitOutput_eventWeight quaternionJCircuit
      outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
      outcomeTopRebitZero outcomeZeroWireQuaternionState {emptyBasis},
    quaternionToRealCircuitOutput_pushforward_eq quaternionJCircuit
      outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
      outcomeTopRebitZero outcomeZeroWireQuaternionState (fun _ ↦ true)⟩

/-! ### Five disjoint outcome-wrapper aggregates -/

/--
Complete consumer for both representative-level wrappers, with both canonical
tops and a genuinely quaternionic `j` input.
-/
theorem representativeOutcomes_wrappers_api :
    DecodedBasisWeightAgreement sumSectorWeightDecoder
        (complexBasisWeight outcomeUnitComplexColumn)
        (realBasisWeight
          (realTopCombination
            (outcomeTopRebitZero false) (outcomeTopRebitZero true)
            outcomeUnitComplexColumn)) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (complexBasisWeight outcomeUnitComplexColumn)
        (realBasisWeight
          (realTopCombination
            (outcomeTopRebitOne false) (outcomeTopRebitOne true)
            outcomeUnitComplexColumn)) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (quaternionBasisWeight outcomeUnitQuaternionJColumn)
        (complexBasisWeight
          (complexTopCombination
            (outcomeTopQubitZero false) (outcomeTopQubitZero true)
            outcomeUnitQuaternionJColumn)) ∧
      DecodedBasisWeightAgreement sumSectorWeightDecoder
        (quaternionBasisWeight outcomeUnitQuaternionJColumn)
        (complexBasisWeight
          (complexTopCombination
            (outcomeTopQubitOne false) (outcomeTopQubitOne true)
            outcomeUnitQuaternionJColumn)) := by
  have hReal :=
    realTopCombination_allRebit_raw_decodedBasisWeightAgreement (I := Unit)
  have hQuaternion :=
    complexTopCombination_allQubit_raw_decodedBasisWeightAgreement (I := Unit)
  exact ⟨AllTopDecodedBasisWeightAgreement.forTopInput hReal
      outcomeTopRebitZero outcomeUnitComplexColumn,
    AllTopDecodedBasisWeightAgreement.forTopInput hReal
      outcomeTopRebitOne outcomeUnitComplexColumn,
    AllTopDecodedBasisWeightAgreement.forTopInput hQuaternion
      outcomeTopQubitZero outcomeUnitQuaternionJColumn,
    AllTopDecodedBasisWeightAgreement.forTopInput hQuaternion
      outcomeTopQubitOne outcomeUnitQuaternionJColumn⟩

/--
Complete consumer for the four complex-to-real outcome levels on the actual
scalar-`I` zero-wire circuit. `BitBasis Empty` is a singleton, not empty.
-/
theorem complexToRealOutcomes_wrappers_api :
    DecodedBasisWeightAgreement (addedWireWeightDecoder (W := Empty))
        (fun outcome ↦ complexBasisWeight
          (OrderedCircuit.eval complexICircuit *ᵥ
            complexOneColumn) outcome)
        (fun targetOutcome ↦ realBasisWeight
          (OrderedCircuit.eval
              (realifyCircuit complexICircuit) *ᵥ
            wireRealTopCombination
              (outcomeTopRebitOne false) (outcomeTopRebitOne true)
              complexOneColumn)
          targetOutcome) ∧
      DecodedDistributionAgreement
        (addedWireDistributionDecoder (W := Empty))
        (complexCircuitOutputDistribution complexICircuit
          outcomeComplexICircuit_locallyUnitary outcomeZeroWireComplexState)
        (realifyCircuitFullOutputDistribution complexICircuit
          outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
          outcomeZeroWireComplexState) ∧
      (addedWireDistributionDecoder
          (realifyCircuitFullOutputDistribution complexICircuit
            outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
            outcomeZeroWireComplexState)).eventWeight
            {emptyBasis} =
        (complexCircuitOutputDistribution complexICircuit
          outcomeComplexICircuit_locallyUnitary
          outcomeZeroWireComplexState).eventWeight {emptyBasis} ∧
      (addedWireDistributionDecoder
          (realifyCircuitFullOutputDistribution complexICircuit
            outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
            outcomeZeroWireComplexState)).pushforward (fun _ ↦ true) =
        (complexCircuitOutputDistribution complexICircuit
          outcomeComplexICircuit_locallyUnitary
          outcomeZeroWireComplexState).pushforward (fun _ ↦ true) := by
  classical
  exact ⟨AllTopDecodedBasisWeightAgreement.forTopInput
      (realifyCircuit_allRebit_raw_decodedBasisWeightAgreement
        complexICircuit)
      outcomeTopRebitOne complexOneColumn,
    AllTopDecodedDistributionAgreement.forTopInput
      (realifyCircuit_allRebit_decodedDistributionAgreement
        complexICircuit outcomeComplexICircuit_locallyUnitary)
      outcomeTopRebitZero outcomeZeroWireComplexState,
    realifyCircuit_decodedEventWeight_eq complexICircuit
      outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
      outcomeZeroWireComplexState {emptyBasis},
    realifyCircuit_decodedPushforward_eq complexICircuit
      outcomeComplexICircuit_locallyUnitary outcomeTopRebitZero
      outcomeZeroWireComplexState (fun _ ↦ true)⟩

/--
Complete consumer for the four quaternion-to-complex outcome levels on the
actual scalar-`j` zero-wire circuit.
-/
theorem quaternionToComplexOutcomes_wrappers_api :
    DecodedBasisWeightAgreement (addedWireWeightDecoder (W := Empty))
        (fun outcome ↦ quaternionBasisWeight
          (OrderedCircuit.eval quaternionJCircuit *ᵥ
            quaternionOneColumn) outcome)
        (fun targetOutcome ↦ complexBasisWeight
          (OrderedCircuit.eval
              (complexifyCircuit quaternionJCircuit) *ᵥ
            wireComplexTopCombination
              (outcomeTopQubitOne false) (outcomeTopQubitOne true)
              quaternionOneColumn)
          targetOutcome) ∧
      DecodedDistributionAgreement
        (addedWireDistributionDecoder (W := Empty))
        (quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState)
        (complexifyCircuitFullOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
          outcomeZeroWireQuaternionState) ∧
      (addedWireDistributionDecoder
          (complexifyCircuitFullOutputDistribution
            quaternionJCircuit
            outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
            outcomeZeroWireQuaternionState)).eventWeight
            {emptyBasis} =
        (quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState).eventWeight {emptyBasis} ∧
      (addedWireDistributionDecoder
          (complexifyCircuitFullOutputDistribution
            quaternionJCircuit
            outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
            outcomeZeroWireQuaternionState)).pushforward (fun _ ↦ false) =
        (quaternionCircuitOutputDistribution quaternionJCircuit
          outcomeQuaternionJCircuit_locallyUnitary
          outcomeZeroWireQuaternionState).pushforward (fun _ ↦ false) := by
  classical
  exact ⟨AllTopDecodedBasisWeightAgreement.forTopInput
      (complexifyCircuit_allQubit_raw_decodedBasisWeightAgreement
        quaternionJCircuit)
      outcomeTopQubitOne quaternionOneColumn,
    AllTopDecodedDistributionAgreement.forTopInput
      (complexifyCircuit_allQubit_decodedDistributionAgreement
        quaternionJCircuit outcomeQuaternionJCircuit_locallyUnitary)
      outcomeTopQubitZero outcomeZeroWireQuaternionState,
    complexifyCircuit_decodedEventWeight_eq quaternionJCircuit
      outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
      outcomeZeroWireQuaternionState {emptyBasis},
    complexifyCircuit_decodedPushforward_eq quaternionJCircuit
      outcomeQuaternionJCircuit_locallyUnitary outcomeTopQubitZero
      outcomeZeroWireQuaternionState (fun _ ↦ false)⟩

/--
Complete consumer for the four scheduled outcome wrappers on the actual
`iThenJ` legal schedule, including a two-outcome event and bit projection.
-/
theorem scheduledQuaternionToComplexOutcomes_wrappers_api :
    DecodedBasisWeightAgreement (addedWireWeightDecoder (W := Bool))
        (fun outcome ↦ quaternionBasisWeight
          (iThenJSchedule.scheduledEval gateFamily *ᵥ
            inputColumn) outcome)
        (fun targetOutcome ↦ complexBasisWeight
          (OrderedCircuit.eval
              (complexifyCircuit
                (iThenJSchedule.scheduledCircuit
                  gateFamily)) *ᵥ
            wireComplexTopCombination
              (outcomeTopQubitOne false) (outcomeTopQubitOne true)
              inputColumn)
          targetOutcome) ∧
      DecodedDistributionAgreement
        (addedWireDistributionDecoder (W := Bool))
        (quaternionCircuitOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          inputState)
        (complexifyCircuitFullOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          outcomeTopQubitZero inputState) ∧
      (addedWireDistributionDecoder
        (complexifyCircuitFullOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          outcomeTopQubitZero inputState)).eventWeight
            {basis00, basis11} =
        (quaternionCircuitOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          inputState).eventWeight
            {basis00, basis11} ∧
      (addedWireDistributionDecoder
        (complexifyCircuitFullOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          outcomeTopQubitZero inputState)).pushforward
            (fun outcome ↦ outcome false) =
        (quaternionCircuitOutputDistribution
          (iThenJSchedule.scheduledCircuit gateFamily)
          (LegalSchedule.scheduledCircuit_isLocallyUnitary
            iThenJSchedule gateFamily
            outcomeWitnessGateFamily_locallyUnitary)
          inputState).pushforward (fun outcome ↦ outcome false) := by
  classical
  exact ⟨AllTopDecodedBasisWeightAgreement.forTopInput
      (scheduledComplexifyCircuit_allQubit_raw_decodedBasisWeightAgreement
        iThenJSchedule gateFamily)
      outcomeTopQubitOne inputColumn,
    AllTopDecodedDistributionAgreement.forTopInput
      (scheduledComplexifyCircuit_allQubit_decodedDistributionAgreement
        iThenJSchedule gateFamily
        outcomeWitnessGateFamily_locallyUnitary)
      outcomeTopQubitZero inputState,
    scheduledComplexifyCircuit_decodedEventWeight_eq
      iThenJSchedule gateFamily
      outcomeWitnessGateFamily_locallyUnitary
      outcomeTopQubitZero inputState
      {basis00, basis11},
    scheduledComplexifyCircuit_decodedPushforward_eq
      iThenJSchedule gateFamily
      outcomeWitnessGateFamily_locallyUnitary
      outcomeTopQubitZero inputState
      (fun outcome ↦ outcome false)⟩

/--
Complete consumer for the four composed outcome wrappers.  The explicit
two-wire decoder removes the outer realification wire before the inner
complexification wire.
-/
theorem composedQuaternionToRealOutcomes_wrappers_api :
    DecodedBasisWeightAgreement (twoAddedWireWeightDecoder (W := Bool))
        (fun outcome ↦ quaternionBasisWeight
          (OrderedCircuit.eval iThenJ *ᵥ inputColumn)
          outcome)
        (fun targetOutcome ↦ realBasisWeight
          (OrderedCircuit.eval (quaternionToRealCircuit iThenJ) *ᵥ
            wireRealTopCombination
              (outcomeTopRebitZero false) (outcomeTopRebitZero true)
              (wireComplexTopCombination
                (outcomeTopQubitOne false) (outcomeTopQubitOne true)
                inputColumn))
          targetOutcome) ∧
      DecodedDistributionAgreement
        (twoAddedWireDistributionDecoder (W := Bool))
        (quaternionCircuitOutputDistribution iThenJ
          iThenJ_locallyUnitary inputState)
        (quaternionToRealCircuitFullOutputDistribution iThenJ
          iThenJ_locallyUnitary outcomeTopQubitOne
          outcomeTopRebitZero inputState) ∧
      (twoAddedWireDistributionDecoder
        (quaternionToRealCircuitFullOutputDistribution iThenJ
          iThenJ_locallyUnitary outcomeTopQubitOne
          outcomeTopRebitZero inputState)).eventWeight
            {basis00, basis11} =
        (quaternionCircuitOutputDistribution iThenJ
          iThenJ_locallyUnitary inputState).eventWeight
            {basis00, basis11} ∧
      (twoAddedWireDistributionDecoder
        (quaternionToRealCircuitFullOutputDistribution iThenJ
          iThenJ_locallyUnitary outcomeTopQubitOne
          outcomeTopRebitZero inputState)).pushforward
            (fun outcome ↦ outcome true) =
        (quaternionCircuitOutputDistribution iThenJ
          iThenJ_locallyUnitary inputState).pushforward
            (fun outcome ↦ outcome true) := by
  classical
  exact ⟨AllTopDecodedBasisWeightAgreement.forTopInput
      (quaternionToRealCircuit_allPureTop_raw_decodedBasisWeightAgreement
        iThenJ)
      (outcomeTopQubitOne, outcomeTopRebitZero) inputColumn,
    AllTopDecodedDistributionAgreement.forTopInput
      (quaternionToRealCircuit_allPureTop_decodedDistributionAgreement
        iThenJ iThenJ_locallyUnitary)
      (outcomeTopQubitOne, outcomeTopRebitZero) inputState,
    quaternionToRealCircuit_decodedEventWeight_eq iThenJ
      iThenJ_locallyUnitary outcomeTopQubitOne outcomeTopRebitZero
      inputState {basis00, basis11},
    quaternionToRealCircuit_decodedPushforward_eq iThenJ
      iThenJ_locallyUnitary outcomeTopQubitOne outcomeTopRebitZero
      inputState (fun outcome ↦ outcome true)⟩

end QuaternionicComputing.Semantics.SimulationAudit

#print axioms QuaternionicComputing.Semantics.SimulationAudit.exactStateEncoding_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.decodedDistributionAgreement_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.realRepresentativeEncoding_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.complexRepresentativeEncoding_api
#print axioms QuaternionicComputing.Semantics.SimulationAudit.allRebit_stateIntertwining_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.empty_rawEncoding_normalizedBoundary_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.ordinaryRealRay_nonDescent_nonProduct_boundary
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.outcomeDecoder_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.outcomePostprocessing_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.representativeOutcomes_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.complexToRealOutcomes_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.quaternionToComplexOutcomes_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.scheduledQuaternionToComplexOutcomes_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.composedQuaternionToRealOutcomes_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.matrixStateIntertwining_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.reindexPlacement_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.primaryCircuit_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.scheduledCircuit_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.composedCircuit_wrappers_api
#print axioms
  QuaternionicComputing.Semantics.SimulationAudit.compiledCircuit_wrappers_api
