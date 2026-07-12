module

public import QuaternionicComputing.Circuit.ScheduleCount
public import QuaternionicComputing.Matrix.KroneckerCommute
public import QuaternionicComputing.Matrix.ProperImage
public import QuaternionicComputing.Semantics.ExistingResults
public import QuaternionicComputing.Simulation.CompiledResources
public import QuaternionicComputing.Simulation.NonProductWitness

/-!
# Audit of semantic classifications for existing exact results

This non-root leaf allocates the six stable declarations introduced by
`Semantics.ExistingResults` to three source-order aggregate consumers:

* three normalized-state and reduced-matrix boundary declarations;
* two schedule and order-distinction declarations;
* one conditional exact-compilation declaration.

It also gives each Stage 11-owned diagnostic, algebraic, combinatorial, and
resource family a meaningful theorem consumer.  Those consumers deliberately
remain nonbehavioral: an injective algebraic embedding, image description,
schedule count, or finite resource bound is not circuit or channel equality.

The aggregates retain the concrete counterexample inputs and observations.
In particular, they do not promote one-input output agreement to an all-input
claim, and they do not turn a supplied exact compiler into a synthesis result.
The public root deliberately does not import this file.
-/

@[expose] public noncomputable section

open scoped Kronecker Matrix Quaternion

namespace QuaternionicComputing.Semantics.ExistingResultsAudit

universe u v w

open QuaternionicComputing.Circuit
open QuaternionicComputing.State
open QuaternionicComputing.Quaternion
open QuaternionicComputing.Semantics

/-! ## Exact allocation of the three state and reduced-matrix declarations -/

/--
Source-order consumer for the normalized left-phase rejection, canonical
reduced-outer agreement, and quaternionic distribution/ray separation.
-/
theorem stateResults_api (column : n → ℂ) :
    (∃ a b : QuaternionState Bool,
      LeftPhaseEquivalent (a : Bool → ℍ[ℝ]) b ∧
        quaternionTotalWeight (phaseWitnessGate a) = 1 ∧
        quaternionTotalWeight (phaseWitnessGate b) = 1 ∧
        ¬ LeftPhaseEquivalent (phaseWitnessGate a) (phaseWitnessGate b)) ∧
      (reducedRealOuter (realColumn0 column) =
          reducedRealOuter (realColumn1 column) ∧
        ∀ i, reducedRealOuter (realColumn0 column) i i =
          complexBasisWeight column i) ∧
      (NormalizedDistributionEq quaternionWeight quaternionWeight_nonneg
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
        ¬ QuaternionStatePhaseEq
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
        State.QuaternionRay.mk
            Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
          State.QuaternionRay.mk
            Circuit.ProductInputOrderingWitness.jThenIGroundOutput) :=
  ⟨normalizedQuaternionLeftPhase_rejection,
    realCanonicalColumns_reducedOuterAgreement column,
    quaternionGroundOutputs_distributionEq_not_rayEq⟩

/-! ## Exact allocation of the two schedule declarations -/

/--
Source-order consumer for commuting-schedule exact equality and the complete
fixed quaternionic order-witness boundary, including its exact translation.
-/
theorem scheduleResults_api
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {precedes : ι → ι → Prop}
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s t : LegalSchedule ι precedes) (gates : ι → PlacedGate R W)
    (hcomm : Pairwise fun i j : ι ↦
      Commute (gates i).denote (gates j).denote) :
    ExactCircuitEq (s.scheduledCircuit gates) (t.scheduledCircuit gates) ∧
      (¬ ExactCircuitEq
          (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily) ∧
        OutputWeightEqAt quaternionWeight
          (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          Circuit.ProductInputOrderingWitness.groundColumn ∧
        ¬ PureInputBasisMeasurementEq quaternionWeight
          (Circuit.OrderingWitness.iThenJSchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily)
          (Circuit.OrderingWitness.jThenISchedule.scheduledEval
            Circuit.OrderingWitness.gateFamily) ∧
        ¬ ExactCircuitEq
          (Simulation.complexifyCircuit
            (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
              Circuit.OrderingWitness.gateFamily))
          (Simulation.complexifyCircuit
            (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
              Circuit.OrderingWitness.gateFamily)) ∧
        Simulation.wireComplexBottomWeight
            Simulation.OrderingWitness.iThenJComplexOutput
            Circuit.OrderingWitness.basis00 ≠
          Simulation.wireComplexBottomWeight
            Simulation.OrderingWitness.jThenIComplexOutput
            Circuit.OrderingWitness.basis00) :=
  ⟨scheduledCircuit_exactCircuitEq_of_pairwise_commute s t gates hcomm,
    quaternionOrderingWitness_scopeBoundary⟩

/-! ## Exact allocation of the conditional compiler declaration -/

/--
Source-order consumer for the exact circuit-equality wrapper supplied by an
existing certified compiler.  No compiler inhabitant is synthesized here.
-/
theorem compilerResult_api
    {R : Type u} {W : Type v} [Semiring R] [Fintype W]
    (compiler : ExactGateCompiler R W) (circuit : OrderedCircuit R W) :
    ExactCircuitEq (compiler.compileCircuit circuit) circuit :=
  compiler.compileCircuit_exactCircuitEq circuit

/-! ## Concrete boundary endpoint -/

/--
The fixed ordering example simultaneously exhibits equality of the complete
ground-input distribution, inequality of quaternionic rays, source-circuit
inequality, and inequality after exact complex translation.
-/
theorem concreteOrderingBoundaries_api :
    NormalizedDistributionEq quaternionWeight quaternionWeight_nonneg
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
        State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      ¬ ExactCircuitEq
        (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
          Circuit.OrderingWitness.gateFamily)
        (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
          Circuit.OrderingWitness.gateFamily) ∧
      ¬ ExactCircuitEq
        (Simulation.complexifyCircuit
          (Circuit.OrderingWitness.iThenJSchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily))
        (Simulation.complexifyCircuit
          (Circuit.OrderingWitness.jThenISchedule.scheduledCircuit
            Circuit.OrderingWitness.gateFamily)) := by
  rcases quaternionGroundOutputs_distributionEq_not_rayEq with
    ⟨hDistribution, -, hRay⟩
  rcases quaternionOrderingWitness_scopeBoundary with
    ⟨hSource, -, -, hTranslated, -⟩
  exact ⟨hDistribution, hRay, hSource, hTranslated⟩

/-! ## Diagnostic and algebraic family consumers -/

/--
`EQC-015`: the normalized encoded witness fails even the unnormalized
top-times-bottom factorization predicate.  This is a structural obstruction,
not by itself a mixed-state or operational entanglement theorem.
-/
theorem nonProductWitness_family :
    ¬ Simulation.IsPureTopBottomProduct
      (fun x ↦ Simulation.NonProductWitness.encodedState x) :=
  Simulation.NonProductWitness.encodedState_not_pureTopBottomProduct

/--
`EQC-017`: realification preserves compatible products and adjoints and loses
no matrix entries.  These are algebraic embedding facts, not behavioral
relations between source and target circuits.
-/
theorem realifyAlgebra_family
    {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    QuaternionicComputing.Matrix.realify (A * B) =
        QuaternionicComputing.Matrix.realify A *
          QuaternionicComputing.Matrix.realify B ∧
      QuaternionicComputing.Matrix.realify Aᴴ =
        (QuaternionicComputing.Matrix.realify A)ᵀ ∧
      Function.Injective
        (QuaternionicComputing.Matrix.realify : Matrix m n ℂ →
          Matrix (m ⊕ m) (n ⊕ n) ℝ) :=
  ⟨QuaternionicComputing.Matrix.realify_mul A B,
    QuaternionicComputing.Matrix.realify_conjTranspose A,
    QuaternionicComputing.Matrix.realify_injective⟩

/--
`EQC-018`: quaternionic complexification preserves compatible products and
adjoints and is injective.  The statement is solely about the block embedding.
-/
theorem complexifyAlgebra_family
    {m n p : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n p ℍ[ℝ]) :
    QuaternionicComputing.Quaternion.complexify (A * B) =
        QuaternionicComputing.Quaternion.complexify A *
          QuaternionicComputing.Quaternion.complexify B ∧
      QuaternionicComputing.Quaternion.complexify Aᴴ =
        (QuaternionicComputing.Quaternion.complexify A)ᴴ ∧
      Function.Injective
        (QuaternionicComputing.Quaternion.complexify : Matrix m n ℍ[ℝ] →
          Matrix (m ⊕ m) (n ⊕ n) ℂ) :=
  ⟨QuaternionicComputing.Quaternion.complexify_mul A B,
    QuaternionicComputing.Quaternion.complexify_conjTranspose A,
    QuaternionicComputing.Quaternion.complexify_injective⟩

/--
`EQC-020`: each unitary embedding is an equivalence only with its explicitly
defined range.  Bijectivity here must not be read as surjectivity onto the
ambient orthogonal, unitary, or special-orthogonal group.
-/
theorem unitaryImageEquivalences_family
    (n : Type u) [Fintype n] [DecidableEq n] :
    Function.Bijective
        (QuaternionicComputing.Matrix.realifyUnitaryEquivImage n) ∧
      Function.Bijective
        (QuaternionicComputing.Quaternion.complexifyUnitaryEquivImage n) ∧
      Function.Bijective
        (QuaternionicComputing.Quaternion.directRealifyUnitaryEquivImage n) :=
  ⟨(QuaternionicComputing.Matrix.realifyUnitaryEquivImage n).bijective,
    (QuaternionicComputing.Quaternion.complexifyUnitaryEquivImage n).bijective,
    (QuaternionicComputing.Quaternion.directRealifyUnitaryEquivImage n).bijective⟩

/--
`EQC-021`: determinant and target-group conclusions for all three embeddings.
The quaternion-to-complex conclusion intentionally retains the unresolved
`1`-or-`-1` sign branch rather than claiming special-unitary membership.
-/
theorem determinantImage_family
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    {Q : Matrix n n ℍ[ℝ]} (hQ : Q ∈ unitary (Matrix n n ℍ[ℝ])) :
    (QuaternionicComputing.Matrix.realify A).det =
        Complex.normSq A.det ∧
      QuaternionicComputing.Matrix.realify U ∈
        Matrix.specialOrthogonalGroup (n ⊕ n) ℝ ∧
      ((QuaternionicComputing.Quaternion.complexify Q).det = 1 ∨
        (QuaternionicComputing.Quaternion.complexify Q).det = -1) ∧
      QuaternionicComputing.Quaternion.directRealify Q ∈
        Matrix.specialOrthogonalGroup
          (QuaternionicComputing.Quaternion.DirectRealIndex n) ℝ :=
  ⟨QuaternionicComputing.Matrix.realify_det A,
    QuaternionicComputing.Matrix.realify_mem_specialOrthogonal hU,
    QuaternionicComputing.Quaternion.complexify_det_eq_one_or_neg_one_of_mem_unitary hQ,
    QuaternionicComputing.Quaternion.directRealify_mem_specialOrthogonal hQ⟩

/--
`EQC-022`: explicit members of the ambient target groups lie outside each of
the three algebraic embedding images.  These nonimage witnesses do not imply
an operational lower bound.
-/
theorem properImageWitnesses_family :
    (QuaternionicComputing.Matrix.ProperImage.realWitness ∈
        Matrix.specialOrthogonalGroup (Bool ⊕ Bool) ℝ ∧
      ¬ ∃ A : Matrix Bool Bool ℂ,
        QuaternionicComputing.Matrix.realify A =
          QuaternionicComputing.Matrix.ProperImage.realWitness) ∧
      (QuaternionicComputing.Matrix.ProperImage.complexWitness ∈
          Matrix.specialUnitaryGroup (Bool ⊕ Bool) ℂ ∧
        ¬ ∃ A : Matrix Bool Bool ℍ[ℝ],
          QuaternionicComputing.Quaternion.complexify A =
            QuaternionicComputing.Matrix.ProperImage.complexWitness) ∧
      (QuaternionicComputing.Matrix.ProperImage.directWitness ∈
          Matrix.specialOrthogonalGroup
            (QuaternionicComputing.Quaternion.DirectRealIndex Unit) ℝ ∧
        ¬ ∃ A : Matrix Unit Unit ℍ[ℝ],
          QuaternionicComputing.Quaternion.directRealify A =
            QuaternionicComputing.Matrix.ProperImage.directWitness) :=
  ⟨QuaternionicComputing.Matrix.ProperImage.realWitness_specialOrthogonal_not_realify,
    QuaternionicComputing.Matrix.ProperImage.complexWitness_specialUnitary_not_complexify,
    QuaternionicComputing.Matrix.ProperImage.directWitness_specialOrthogonal_not_directRealify⟩

/--
`EQC-023`: the noncommutative Kronecker interchange law can hold beyond the
zero-one sufficient condition and can also fail.  This records an algebraic
boundary, not a generic schedule-equivalence theorem.
-/
theorem kroneckerInterchange_family
    {R l m n p q r : Type u} [Semiring R] [Fintype m] [Fintype p]
    (A : _root_.Matrix l m R) (B : _root_.Matrix n p R)
    (C : _root_.Matrix m q R) (D : _root_.Matrix p r R)
    (h : QuaternionicComputing.Matrix.EntrywiseCommute B C) :
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) ∧
      (¬ QuaternionicComputing.Matrix.IsZeroOneMatrix
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
            QuaternionicComputing.Quaternion.i) ∧
        ¬ QuaternionicComputing.Matrix.IsZeroOneMatrix
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
            QuaternionicComputing.Quaternion.j) ∧
        (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i) *
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j) =
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i) ⊗ₖ
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j)) ∧
      ¬ ((QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1 ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i) *
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j ⊗ₖ
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1) =
        (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1 *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.j) ⊗ₖ
          (QuaternionicComputing.Matrix.QuaternionExamples.oneByOne
              QuaternionicComputing.Quaternion.i *
            QuaternionicComputing.Matrix.QuaternionExamples.oneByOne 1)) :=
  ⟨QuaternionicComputing.Matrix.kronecker_mul_kronecker_of_entrywiseCommute
      A B C D h,
    QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_without_zeroOne,
    QuaternionicComputing.Matrix.QuaternionExamples.oneByOne_interchange_i_j_failure⟩

/--
`EQC-024`: contextual placement preserves multiplication, adjoints, and
unitarity and is injective.  These facts concern the contextual operator, not
an observational quotient.
-/
theorem placementAlgebra_family
    {R L K W : Type*} [Semiring R] [StarRing R]
    [Fintype L] [Fintype K] [Fintype W]
    (split : L ⊕ K ≃ W)
    (U V : Matrix (BitBasis L) (BitBasis L) R)
    (hU : U ∈ unitary (Matrix (BitBasis L) (BitBasis L) R)) :
    Circuit.place split (U * V) = Circuit.place split U * Circuit.place split V ∧
      Circuit.place split Uᴴ = (Circuit.place split U)ᴴ ∧
      Function.Injective
        (Circuit.place split : Matrix (BitBasis L) (BitBasis L) R →
          Matrix (BitBasis W) (BitBasis W) R) ∧
      Circuit.place split U ∈ unitary (Matrix (BitBasis W) (BitBasis W) R) :=
  ⟨Circuit.place_mul split U V,
    Circuit.place_conjTranspose split U,
    Circuit.place_injective split,
    Circuit.place_mem_unitary split hU⟩

/-! ## Combinatorial and resource family consumers -/

/--
`EQC-029`: all finite chronological orders are enumerated once and every legal
schedule's order occurs in that enumeration.  The Boolean-chain witness shows
why the factorial count is not a count of schedules satisfying an arbitrary
precedence relation.
-/
theorem scheduleEnumeration_family
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {precedes : ι → ι → Prop} (schedule : LegalSchedule ι precedes) :
    (Circuit.allChronologicalOrders ι).length =
        Nat.factorial (Fintype.card ι) ∧
      schedule.order ∈ Circuit.allChronologicalOrders ι ∧
      [true, false] ∈ Circuit.allChronologicalOrders Bool ∧
      ¬ ∃ s : LegalSchedule Bool Circuit.ScheduleCount.BoolChain.precedes,
        s.order = [true, false] :=
  ⟨Circuit.length_allChronologicalOrders ι,
    schedule.order_mem_allChronologicalOrders,
    Circuit.ScheduleCount.BoolChain.reverseOrder_mem_allChronologicalOrders,
    Circuit.ScheduleCount.BoolChain.reverseOrder_not_legal⟩

/--
`EQC-041`: representative exact count, width, arity, dense-slot, and
shared-top depth certificates for the literal translations.  Slot counts are
not runtime or bit-complexity claims, and the depth equality is specific to
the present shared-top support layering.
-/
theorem translationResources_family
    {W : Type u} [Fintype W]
    (complexCircuit : OrderedCircuit ℂ W)
    (quaternionCircuit : OrderedCircuit ℍ[ℝ] W)
    (realLayering : SupportLayering
      (Simulation.realifyCircuit complexCircuit))
    (complexLayering : SupportLayering
      (Simulation.complexifyCircuit quaternionCircuit))
    (composedLayering : SupportLayering
      (Simulation.quaternionToRealCircuit quaternionCircuit)) :
    Fintype.card (AddedWire W) = Fintype.card W + 1 ∧
      Fintype.card (AddedWire (AddedWire W)) = Fintype.card W + 2 ∧
      (Simulation.realifyCircuit complexCircuit).gateCount =
        complexCircuit.gateCount ∧
      (Simulation.complexifyCircuit quaternionCircuit).gateCount =
        quaternionCircuit.gateCount ∧
      (Simulation.quaternionToRealCircuit quaternionCircuit).gateCount =
        quaternionCircuit.gateCount ∧
      (Simulation.realifyCircuit complexCircuit).maxLocalArity ≤
        complexCircuit.maxLocalArity + 1 ∧
      (Simulation.complexifyCircuit quaternionCircuit).maxLocalArity ≤
        quaternionCircuit.maxLocalArity + 1 ∧
      (Simulation.quaternionToRealCircuit quaternionCircuit).maxLocalArity ≤
        quaternionCircuit.maxLocalArity + 2 ∧
      (Simulation.realifyCircuit complexCircuit).totalDenseEntrySlots =
        4 * complexCircuit.totalDenseEntrySlots ∧
      (Simulation.complexifyCircuit quaternionCircuit).totalDenseEntrySlots =
        4 * quaternionCircuit.totalDenseEntrySlots ∧
      (Simulation.quaternionToRealCircuit quaternionCircuit).totalDenseEntrySlots =
        16 * quaternionCircuit.totalDenseEntrySlots ∧
      realLayering.depth =
        complexCircuit.gateCount ∧
      complexLayering.depth = quaternionCircuit.gateCount ∧
      composedLayering.depth = quaternionCircuit.gateCount :=
  ⟨Simulation.width_realifyCircuit W,
    Simulation.width_quaternionToRealCircuit W,
    Simulation.gateCount_realifyCircuit complexCircuit,
    Simulation.gateCount_complexifyCircuit quaternionCircuit,
    Simulation.gateCount_quaternionToRealCircuit quaternionCircuit,
    Simulation.maxLocalArity_realifyCircuit_le complexCircuit,
    Simulation.maxLocalArity_complexifyCircuit_le quaternionCircuit,
    Simulation.maxLocalArity_quaternionToRealCircuit_le quaternionCircuit,
    Simulation.totalDenseEntrySlots_realifyCircuit complexCircuit,
    Simulation.totalDenseEntrySlots_complexifyCircuit quaternionCircuit,
    Simulation.totalDenseEntrySlots_quaternionToRealCircuit quaternionCircuit,
    Simulation.depth_realifyCircuit_eq_gateCount complexCircuit realLayering,
    Simulation.depth_complexifyCircuit_eq_gateCount quaternionCircuit complexLayering,
    Simulation.depth_quaternionToRealCircuit_eq_gateCount
      quaternionCircuit composedLayering⟩

/--
`EQC-041`: a supplied per-image-gate primitive count bound gives both compiled
gate-count and canonical serial-depth bounds.  The hypotheses expose that this
is conditional accounting, not an elementary-gate synthesis theorem.
-/
theorem compiledResourceBounds_family
    {W : Type u} [Fintype W]
    (realCompiler : ExactGateCompiler ℝ (AddedWire W))
    (complexCompiler : ExactGateCompiler ℂ (AddedWire W))
    (complexCircuit : OrderedCircuit ℂ W)
    (quaternionCircuit : OrderedCircuit ℍ[ℝ] W) (K : ℕ)
    (hReal : ∀ k ∈ Simulation.realifyCircuit complexCircuit,
      (realCompiler.compileGate k).gateCount ≤ K)
    (hComplex : ∀ k ∈ Simulation.complexifyCircuit quaternionCircuit,
      (complexCompiler.compileGate k).gateCount ≤ K) :
    (realCompiler.compileCircuit
        (Simulation.realifyCircuit complexCircuit)).gateCount ≤
        complexCircuit.gateCount * K ∧
      (Simulation.compileRealifyCircuitSerialLayering
        realCompiler complexCircuit).depth ≤ complexCircuit.gateCount * K ∧
      (complexCompiler.compileCircuit
        (Simulation.complexifyCircuit quaternionCircuit)).gateCount ≤
        quaternionCircuit.gateCount * K ∧
      (Simulation.compileComplexifyCircuitSerialLayering
        complexCompiler quaternionCircuit).depth ≤
          quaternionCircuit.gateCount * K :=
  ⟨Simulation.gateCount_compile_realifyCircuit_le
      realCompiler complexCircuit K hReal,
    Simulation.depth_compileRealifyCircuitSerialLayering_le
      realCompiler complexCircuit K hReal,
    Simulation.gateCount_compile_complexifyCircuit_le
      complexCompiler quaternionCircuit K hComplex,
    Simulation.depth_compileComplexifyCircuitSerialLayering_le
      complexCompiler quaternionCircuit K hComplex⟩

#print axioms stateResults_api
#print axioms scheduleResults_api
#print axioms compilerResult_api
#print axioms concreteOrderingBoundaries_api
#print axioms nonProductWitness_family
#print axioms realifyAlgebra_family
#print axioms complexifyAlgebra_family
#print axioms unitaryImageEquivalences_family
#print axioms determinantImage_family
#print axioms properImageWitnesses_family
#print axioms kroneckerInterchange_family
#print axioms placementAlgebra_family
#print axioms scheduleEnumeration_family
#print axioms translationResources_family
#print axioms compiledResourceBounds_family

end QuaternionicComputing.Semantics.ExistingResultsAudit
