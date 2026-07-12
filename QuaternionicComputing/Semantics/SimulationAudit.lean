module

public import QuaternionicComputing.Semantics.SimulationEncoding
public import QuaternionicComputing.State.RealificationOrbitBoundary
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

end QuaternionicComputing.Semantics.SimulationAudit
