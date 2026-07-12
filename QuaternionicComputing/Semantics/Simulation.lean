module

public import QuaternionicComputing.State.Distribution

/-!
# Directional cross-model simulation semantics

This leaf names exact comparisons between source and target models whose
scalars, index types, or dimensions may differ.  Every predicate keeps the
encoding, embedding, or decoder visible and is oriented from source to target.
These predicates are not same-space equivalence relations and deliberately
have no reflexivity, symmetry, transitivity, or `Equivalence` instances.

The generic `AllTop...` predicates quantify an explicitly supplied top-sector
parameter type.  A concrete wrapper must use the actual normalized type, such
as `Rebit` or `Qubit`, before describing that quantifier as an all-pure-top
result.  Nothing in this generic leaf asserts a product-state, mixed-state,
entanglement, marginal, channel, or all-effect interpretation.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Semantics

universe uS uT uU uOS uIS uOT uIT uOU uIU uO uP uTop uInput

/-! ## Exact state encodings -/

/--
A directional state encoding with exact reconstruction on encoded states.
This is a left-inverse certificate, not an equivalence between the carriers.
-/
def ExactStateEncoding {S : Type uS} {T : Type uT}
    (encode : S → T) (decode : T → S) : Prop :=
  Function.LeftInverse decode encode

namespace ExactStateEncoding

variable {S : Type uS} {T : Type uT} {U : Type uU}
variable {encodeST : S → T} {decodeTS : T → S}
variable {encodeTU : T → U} {decodeUT : U → T}

theorem of_leftInverse (h : Function.LeftInverse decodeTS encodeST) :
    ExactStateEncoding encodeST decodeTS :=
  h

theorem leftInverse (h : ExactStateEncoding encodeST decodeTS) :
    Function.LeftInverse decodeTS encodeST :=
  h

theorem injective (h : ExactStateEncoding encodeST decodeTS) :
    Function.Injective encodeST :=
  h.leftInverse.injective

/-- Exact state encodings compose in source-to-target order. -/
theorem comp (hST : ExactStateEncoding encodeST decodeTS)
    (hTU : ExactStateEncoding encodeTU decodeUT) :
    ExactStateEncoding (encodeTU ∘ encodeST) (decodeTS ∘ decodeUT) := by
  intro source
  simp only [Function.comp_apply]
  rw [hTU.leftInverse (encodeST source), hST.leftInverse source]

end ExactStateEncoding

/--
An exactly reconstructible state encoding that also preserves a supplied
total-weight functional.  The weight functions remain explicit because source
and target models may use different scalar conventions.
-/
def LosslessStateEncoding {S : Type uS} {T : Type uT}
    (encode : S → T) (decode : T → S)
    (sourceTotalWeight : S → ℝ) (targetTotalWeight : T → ℝ) : Prop :=
  ExactStateEncoding encode decode ∧
    ∀ source, targetTotalWeight (encode source) = sourceTotalWeight source

namespace LosslessStateEncoding

variable {S : Type uS} {T : Type uT} {U : Type uU}
variable {encodeST : S → T} {decodeTS : T → S}
variable {encodeTU : T → U} {decodeUT : U → T}
variable {sourceTotalWeight : S → ℝ} {middleTotalWeight : T → ℝ}
variable {targetTotalWeight : U → ℝ}

theorem of_exact_of_totalWeight
    (hexact : ExactStateEncoding encodeST decodeTS)
    (hweight : ∀ source,
      middleTotalWeight (encodeST source) = sourceTotalWeight source) :
    LosslessStateEncoding encodeST decodeTS sourceTotalWeight middleTotalWeight :=
  ⟨hexact, hweight⟩

theorem exact
    (h : LosslessStateEncoding encodeST decodeTS sourceTotalWeight
      middleTotalWeight) :
    ExactStateEncoding encodeST decodeTS :=
  h.1

theorem preservesTotalWeight
    (h : LosslessStateEncoding encodeST decodeTS sourceTotalWeight
      middleTotalWeight) (source : S) :
    middleTotalWeight (encodeST source) = sourceTotalWeight source :=
  h.2 source

theorem injective
    (h : LosslessStateEncoding encodeST decodeTS sourceTotalWeight
      middleTotalWeight) :
    Function.Injective encodeST :=
  h.exact.injective

/-- Lossless state encodings compose with the intermediate weight visible. -/
theorem comp
    (hST : LosslessStateEncoding encodeST decodeTS sourceTotalWeight
      middleTotalWeight)
    (hTU : LosslessStateEncoding encodeTU decodeUT middleTotalWeight
      targetTotalWeight) :
    LosslessStateEncoding (encodeTU ∘ encodeST) (decodeTS ∘ decodeUT)
      sourceTotalWeight targetTotalWeight := by
  refine ⟨hST.exact.comp hTU.exact, ?_⟩
  intro source
  simp only [Function.comp_apply]
  rw [hTU.preservesTotalWeight (encodeST source),
    hST.preservesTotalWeight source]

end LosslessStateEncoding

/-! ## Exact operator embeddings and state intertwining -/

/--
The target operator is exactly the image of the source operator under a named
cross-space embedding.  This is not `ExactOperatorEq`, since the matrix types
may differ.
-/
def ExactOperatorEmbedding
    {RS : Type uS} {RT : Type uT}
    {OS : Type uOS} {IS : Type uIS} {OT : Type uOT} {IT : Type uIT}
    (embed : Matrix OS IS RS → Matrix OT IT RT)
    (source : Matrix OS IS RS) (target : Matrix OT IT RT) : Prop :=
  target = embed source

namespace ExactOperatorEmbedding

variable {RS : Type uS} {RT : Type uT} {RU : Type uU}
variable {OS : Type uOS} {IS : Type uIS}
variable {OT : Type uOT} {IT : Type uIT}
variable {OU : Type uOU} {IU : Type uIU}
variable {embedST : Matrix OS IS RS → Matrix OT IT RT}
variable {embedTU : Matrix OT IT RT → Matrix OU IU RU}
variable {source : Matrix OS IS RS} {middle : Matrix OT IT RT}
variable {target : Matrix OU IU RU}

theorem of_eq (h : middle = embedST source) :
    ExactOperatorEmbedding embedST source middle :=
  h

theorem eq (h : ExactOperatorEmbedding embedST source middle) :
    middle = embedST source :=
  h

/-- Exact operator embeddings compose without identifying the matrix spaces. -/
theorem comp (hST : ExactOperatorEmbedding embedST source middle)
    (hTU : ExactOperatorEmbedding embedTU middle target) :
    ExactOperatorEmbedding (embedTU ∘ embedST) source target := by
  rw [hTU.eq, hST.eq]
  rfl

end ExactOperatorEmbedding

/--
Exact compatibility of source and target matrix actions with supplied input
and output encoders.  Separate encoders retain rectangular operator support.
-/
def StateIntertwining
    {RS : Type uS} {RT : Type uT}
    {OS : Type uOS} {IS : Type uIS} {OT : Type uOT} {IT : Type uIT}
    [Fintype IS] [Fintype IT]
    [NonUnitalNonAssocSemiring RS] [NonUnitalNonAssocSemiring RT]
    (encodeInput : (IS → RS) → (IT → RT))
    (encodeOutput : (OS → RS) → (OT → RT))
    (source : Matrix OS IS RS) (target : Matrix OT IT RT) : Prop :=
  ∀ input, target *ᵥ encodeInput input = encodeOutput (source *ᵥ input)

namespace StateIntertwining

variable {RS : Type uS} {RT : Type uT} {RU : Type uU}
variable {OS : Type uOS} {IS : Type uIS}
variable {OT : Type uOT} {IT : Type uIT}
variable {OU : Type uOU} {IU : Type uIU}
variable [Fintype IS] [Fintype IT] [Fintype IU]
variable [NonUnitalNonAssocSemiring RS]
variable [NonUnitalNonAssocSemiring RT]
variable [NonUnitalNonAssocSemiring RU]
variable {encodeInST : (IS → RS) → (IT → RT)}
variable {encodeOutST : (OS → RS) → (OT → RT)}
variable {encodeInTU : (IT → RT) → (IU → RU)}
variable {encodeOutTU : (OT → RT) → (OU → RU)}
variable {source : Matrix OS IS RS} {middle : Matrix OT IT RT}
variable {target : Matrix OU IU RU}

theorem of_forall
    (h : ∀ input, middle *ᵥ encodeInST input =
      encodeOutST (source *ᵥ input)) :
    StateIntertwining encodeInST encodeOutST source middle :=
  h

theorem apply (h : StateIntertwining encodeInST encodeOutST source middle)
    (input : IS → RS) :
    middle *ᵥ encodeInST input = encodeOutST (source *ᵥ input) :=
  h input

/-- State intertwinings compose while retaining both encoder directions. -/
theorem comp
    (hST : StateIntertwining encodeInST encodeOutST source middle)
    (hTU : StateIntertwining encodeInTU encodeOutTU middle target) :
    StateIntertwining (encodeInTU ∘ encodeInST)
      (encodeOutTU ∘ encodeOutST) source target := by
  intro input
  simp only [Function.comp_apply]
  rw [hTU.apply, hST.apply]

end StateIntertwining

/--
Every value of an explicit top-sector parameter type supplies a state
intertwining.  Concrete wrappers determine whether that type represents
normalized pure states, arbitrary coefficients, or another stated policy.
-/
def AllTopStateIntertwining
    {Top : Type uTop}
    {RS : Type uS} {RT : Type uT}
    {OS : Type uOS} {IS : Type uIS} {OT : Type uOT} {IT : Type uIT}
    [Fintype IS] [Fintype IT]
    [NonUnitalNonAssocSemiring RS] [NonUnitalNonAssocSemiring RT]
    (encodeInput : Top → (IS → RS) → (IT → RT))
    (encodeOutput : Top → (OS → RS) → (OT → RT))
    (source : Matrix OS IS RS) (target : Matrix OT IT RT) : Prop :=
  ∀ top, StateIntertwining (encodeInput top) (encodeOutput top) source target

namespace AllTopStateIntertwining

variable {Top : Type uTop}
variable {RS : Type uS} {RT : Type uT}
variable {OS : Type uOS} {IS : Type uIS} {OT : Type uOT} {IT : Type uIT}
variable [Fintype IS] [Fintype IT]
variable [NonUnitalNonAssocSemiring RS] [NonUnitalNonAssocSemiring RT]
variable {encodeInput : Top → (IS → RS) → (IT → RT)}
variable {encodeOutput : Top → (OS → RS) → (OT → RT)}
variable {source : Matrix OS IS RS} {target : Matrix OT IT RT}

theorem forTop
    (h : AllTopStateIntertwining encodeInput encodeOutput source target)
    (top : Top) :
    StateIntertwining (encodeInput top) (encodeOutput top) source target :=
  h top

end AllTopStateIntertwining

/-! ## Decoded computational-basis weights -/

/--
Decode a target computational-basis weight function and compare it with the
source weight function.  The decoder explicitly records any reindexing or
marginalization policy.
-/
def DecodedBasisWeightAgreement
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    (decode : (TargetOutcome → ℝ) → (SourceOutcome → ℝ))
    (sourceWeight : SourceOutcome → ℝ)
    (targetWeight : TargetOutcome → ℝ) : Prop :=
  decode targetWeight = sourceWeight

namespace DecodedBasisWeightAgreement

variable {SourceOutcome : Type uO} {MiddleOutcome : Type uP}
variable {TargetOutcome : Type uU}
variable {decodeSM : (MiddleOutcome → ℝ) → (SourceOutcome → ℝ)}
variable {decodeMT : (TargetOutcome → ℝ) → (MiddleOutcome → ℝ)}
variable {sourceWeight : SourceOutcome → ℝ}
variable {middleWeight : MiddleOutcome → ℝ}
variable {targetWeight : TargetOutcome → ℝ}

theorem of_eq (h : decodeSM middleWeight = sourceWeight) :
    DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight :=
  h

theorem eq (h : DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight) :
    decodeSM middleWeight = sourceWeight :=
  h

theorem apply (h : DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight)
    (outcome : SourceOutcome) :
    decodeSM middleWeight outcome = sourceWeight outcome :=
  congrFun h.eq outcome

/-- Decoded basis-weight agreement composes by composing the decoders. -/
theorem comp
    (hSM : DecodedBasisWeightAgreement decodeSM sourceWeight middleWeight)
    (hMT : DecodedBasisWeightAgreement decodeMT middleWeight targetWeight) :
    DecodedBasisWeightAgreement (decodeSM ∘ decodeMT) sourceWeight targetWeight := by
  simp only [DecodedBasisWeightAgreement, Function.comp_apply]
  rw [hMT.eq, hSM.eq]

end DecodedBasisWeightAgreement

/-! ## Decoded finite distributions -/

/--
Decode a target finite distribution into the source outcome space and compare
it exactly with the source distribution.
-/
def DecodedDistributionAgreement
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    [Fintype SourceOutcome] [Fintype TargetOutcome]
    (decode : State.FiniteDistribution TargetOutcome →
      State.FiniteDistribution SourceOutcome)
    (source : State.FiniteDistribution SourceOutcome)
    (target : State.FiniteDistribution TargetOutcome) : Prop :=
  decode target = source

namespace DecodedDistributionAgreement

open State

variable {SourceOutcome : Type uO} {MiddleOutcome : Type uP}
variable {TargetOutcome : Type uU}
variable [Fintype SourceOutcome] [Fintype MiddleOutcome]
variable [Fintype TargetOutcome]
variable {decodeSM : FiniteDistribution MiddleOutcome →
  FiniteDistribution SourceOutcome}
variable {decodeMT : FiniteDistribution TargetOutcome →
  FiniteDistribution MiddleOutcome}
variable {source : FiniteDistribution SourceOutcome}
variable {middle : FiniteDistribution MiddleOutcome}
variable {target : FiniteDistribution TargetOutcome}

theorem of_eq (h : decodeSM middle = source) :
    DecodedDistributionAgreement decodeSM source middle :=
  h

theorem eq (h : DecodedDistributionAgreement decodeSM source middle) :
    decodeSM middle = source :=
  h

/-- Decoded distribution agreement composes by composing the decoders. -/
theorem comp
    (hSM : DecodedDistributionAgreement decodeSM source middle)
    (hMT : DecodedDistributionAgreement decodeMT middle target) :
    DecodedDistributionAgreement (decodeSM ∘ decodeMT) source target := by
  simp only [DecodedDistributionAgreement, Function.comp_apply]
  rw [hMT.eq, hSM.eq]

/-- Distribution agreement gives decoded point weights for a compatible decoder. -/
theorem decodedBasisWeightAgreement
    {decodeWeight : (MiddleOutcome → ℝ) → (SourceOutcome → ℝ)}
    (hcompat : ∀ distribution,
      (decodeSM distribution).weight = decodeWeight distribution.weight)
    (h : DecodedDistributionAgreement decodeSM source middle) :
    DecodedBasisWeightAgreement decodeWeight source.weight middle.weight := by
  unfold DecodedBasisWeightAgreement
  rw [← hcompat middle, h.eq]

/-- Compatible decoded point weights determine the decoded finite distribution. -/
theorem of_decodedBasisWeightAgreement
    {decodeWeight : (MiddleOutcome → ℝ) → (SourceOutcome → ℝ)}
    (hcompat : ∀ distribution,
      (decodeSM distribution).weight = decodeWeight distribution.weight)
    (h : DecodedBasisWeightAgreement decodeWeight source.weight middle.weight) :
    DecodedDistributionAgreement decodeSM source middle := by
  apply FiniteDistribution.ext
  intro outcome
  have hfun : (decodeSM middle).weight = source.weight := by
    rw [hcompat middle]
    exact h.eq
  exact congrFun hfun outcome

/-- Every finite source event has equal weight after target decoding. -/
theorem eventWeight_eq
    (h : DecodedDistributionAgreement decodeSM source middle)
    (event : Finset SourceOutcome) :
    (decodeSM middle).eventWeight event = source.eventWeight event := by
  rw [h.eq]

/-- Every deterministic finite postprocessing agrees after target decoding. -/
theorem pushforward_eq {PostOutcome : Type uU} [Fintype PostOutcome]
    (h : DecodedDistributionAgreement decodeSM source middle)
    (postprocess : SourceOutcome → PostOutcome) :
    (decodeSM middle).pushforward postprocess =
      source.pushforward postprocess := by
  rw [h.eq]

end DecodedDistributionAgreement

/-! ## Explicit top-sector quantifier policies -/

/--
Decoded basis-weight agreement for every value of a supplied top-sector
parameter type and every value of a supplied source-input type.
-/
def AllTopDecodedBasisWeightAgreement
    {Top : Type uTop} {Input : Type uInput}
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    (decode : (TargetOutcome → ℝ) → (SourceOutcome → ℝ))
    (sourceWeight : Input → SourceOutcome → ℝ)
    (targetWeight : Top → Input → TargetOutcome → ℝ) : Prop :=
  ∀ top input,
    DecodedBasisWeightAgreement decode (sourceWeight input)
      (targetWeight top input)

namespace AllTopDecodedBasisWeightAgreement

variable {Top : Type uTop} {Input : Type uInput}
variable {SourceOutcome : Type uO} {TargetOutcome : Type uP}
variable {decode : (TargetOutcome → ℝ) → (SourceOutcome → ℝ)}
variable {sourceWeight : Input → SourceOutcome → ℝ}
variable {targetWeight : Top → Input → TargetOutcome → ℝ}

theorem forTopInput
    (h : AllTopDecodedBasisWeightAgreement decode sourceWeight targetWeight)
    (top : Top) (input : Input) :
    DecodedBasisWeightAgreement decode (sourceWeight input)
      (targetWeight top input) :=
  h top input

end AllTopDecodedBasisWeightAgreement

/--
Decoded distribution agreement for every value of a supplied top-sector
parameter type and every value of a supplied source-input type.
-/
def AllTopDecodedDistributionAgreement
    {Top : Type uTop} {Input : Type uInput}
    {SourceOutcome : Type uO} {TargetOutcome : Type uP}
    [Fintype SourceOutcome] [Fintype TargetOutcome]
    (decode : State.FiniteDistribution TargetOutcome →
      State.FiniteDistribution SourceOutcome)
    (sourceDistribution : Input → State.FiniteDistribution SourceOutcome)
    (targetDistribution : Top → Input →
      State.FiniteDistribution TargetOutcome) : Prop :=
  ∀ top input,
    DecodedDistributionAgreement decode (sourceDistribution input)
      (targetDistribution top input)

namespace AllTopDecodedDistributionAgreement

open State

variable {Top : Type uTop} {Input : Type uInput}
variable {SourceOutcome : Type uO} {TargetOutcome : Type uP}
variable [Fintype SourceOutcome] [Fintype TargetOutcome]
variable {decode : FiniteDistribution TargetOutcome →
  FiniteDistribution SourceOutcome}
variable {sourceDistribution : Input → FiniteDistribution SourceOutcome}
variable {targetDistribution : Top → Input →
  FiniteDistribution TargetOutcome}

theorem forTopInput
    (h : AllTopDecodedDistributionAgreement decode sourceDistribution
      targetDistribution)
    (top : Top) (input : Input) :
    DecodedDistributionAgreement decode (sourceDistribution input)
      (targetDistribution top input) :=
  h top input

end AllTopDecodedDistributionAgreement

end QuaternionicComputing.Semantics
