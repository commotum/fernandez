module

public import QuaternionicComputing.Circuit.Compilation
public import QuaternionicComputing.Circuit.ProductInputOrderingWitness
public import QuaternionicComputing.Semantics.Ray
public import QuaternionicComputing.Simulation.OrderingWitness
public import QuaternionicComputing.State.Realification

/-!
# Semantic classifications of existing exact results

This leaf gives reusable semantic names to six results that previously lived
only as raw equalities, counterexamples, or non-root audit packages.  Each
statement records its exact scope: the rejected quaternionic phase convention
is left-sided, the reduced matrix is the explicit two-sector block sum, the
ordering witnesses distinguish one-input from all-pure-input observations,
and exact compilation remains conditional on a supplied compiler certificate.

No converse schedule theorem, compiler-existence theorem, generic partial
trace, or all-input conclusion is asserted here.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

universe u v w

open QuaternionicComputing.Circuit
open QuaternionicComputing.State
open QuaternionicComputing.Quaternion

/-! ## Existing normalized-state and reduced-matrix boundaries -/

/--
There are normalized quaternionic inputs related by a unit scalar on the left
whose images under the norm-preserving diagnostic gate are not related by any
unit scalar on the left.  This rejects left phase as a natural state-ray
convention; it says nothing against the library's right-sided quaternionic ray.
-/
theorem normalizedQuaternionLeftPhase_rejection :
    ∃ a b : QuaternionState Bool,
      LeftPhaseEquivalent (a : Bool → ℍ[ℝ]) b ∧
        quaternionTotalWeight (phaseWitnessGate a) = 1 ∧
        quaternionTotalWeight (phaseWitnessGate b) = 1 ∧
        ¬ LeftPhaseEquivalent (phaseWitnessGate a) (phaseWitnessGate b) := by
  let x : Bool → ℍ[ℝ] :=
    fun bit => if bit then ⟨4 / 5, 0, 0, 0⟩ else ⟨3 / 5, 0, 0, 0⟩
  let y : Bool → ℍ[ℝ] := i • x
  have hx : quaternionTotalWeight x = 1 := by
    simp [x, quaternionTotalWeight, totalWeight, basisWeight,
      quaternionWeight, Fintype.univ_bool, _root_.Quaternion.normSq_def']
    norm_num
  have hy : quaternionTotalWeight y = 1 := by
    simp [y, x, quaternionTotalWeight, totalWeight, basisWeight,
      quaternionWeight, Fintype.univ_bool, _root_.Quaternion.normSq_def', i]
    norm_num
  let a : QuaternionState Bool := ⟨y, hy⟩
  let b : QuaternionState Bool := ⟨x, hx⟩
  have hgate (z : Bool → ℍ[ℝ]) :
      quaternionTotalWeight (phaseWitnessGate z) =
        quaternionTotalWeight z := by
    simpa [quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight]
      using phaseWitnessGate_normSq z
  have hab : LeftPhaseEquivalent (a : Bool → ℍ[ℝ]) b := by
    exact ⟨i, normSq_i, rfl⟩
  have hnot : ¬ LeftPhaseEquivalent (phaseWitnessGate a) (phaseWitnessGate b) := by
    change ¬ LeftPhaseEquivalent (phaseWitnessGate (i • x)) (phaseWitnessGate x)
    rintro ⟨eta, _, heta⟩
    have hfalse := congrFun heta false
    have htrue := congrFun heta true
    simp only [phaseWitnessGate, x, Pi.smul_apply, smul_eq_mul,
      Bool.false_eq_true, ↓reduceIte] at hfalse htrue
    have hre := congrArg (fun q : ℍ[ℝ] => q.re) hfalse
    have himI := congrArg (fun q : ℍ[ℝ] => q.imI) hfalse
    have himJ := congrArg (fun q : ℍ[ℝ] => q.imJ) hfalse
    have himK := congrArg (fun q : ℍ[ℝ] => q.imK) hfalse
    have heta_eq : i = eta := by
      apply QuaternionAlgebra.ext
      all_goals norm_num [i] at hre himI himJ himK ⊢
      all_goals linarith
    subst eta
    have hgateK := congrArg (fun q : ℍ[ℝ] => q.imK) htrue
    norm_num [i, j] at hgateK
  refine ⟨a, b, hab, ?_, ?_, hnot⟩
  · simpa [a] using (hgate y).trans hy
  · simpa [b] using (hgate x).trans hx

/--
The two canonical real encodings of every complex column have the same
explicit reduced rank-one matrix, and its computational diagonal is exactly
the source complex basis-weight family.
-/
theorem realCanonicalColumns_reducedOuterAgreement
    (column : n → ℂ) :
    reducedRealOuter (realColumn0 column) =
        reducedRealOuter (realColumn1 column) ∧
      ∀ i, reducedRealOuter (realColumn0 column) i i =
        complexBasisWeight column i := by
  refine ⟨reducedRealOuter_realColumns column, ?_⟩
  intro i
  rw [reducedRealOuter_diagonal, realColumn0_bottomWeight]

/--
The two normalized product-input ordering outputs induce the same complete
computational-basis distribution, but are neither right-phase-equivalent
representatives nor the same quaternionic ray.
-/
theorem quaternionGroundOutputs_distributionEq_not_rayEq :
    NormalizedDistributionEq quaternionWeight quaternionWeight_nonneg
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      ¬ QuaternionStatePhaseEq
        Circuit.ProductInputOrderingWitness.iThenJGroundOutput
        Circuit.ProductInputOrderingWitness.jThenIGroundOutput ∧
      State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.iThenJGroundOutput ≠
        State.QuaternionRay.mk
          Circuit.ProductInputOrderingWitness.jThenIGroundOutput := by
  have hweights : BasisWeightEq quaternionWeight
      Circuit.ProductInputOrderingWitness.iThenJGroundOutput
      Circuit.ProductInputOrderingWitness.jThenIGroundOutput :=
    Circuit.ProductInputOrderingWitness.ground_outputs_basis_weights_eq
  have hnotPhase : ¬ QuaternionStatePhaseEq
      Circuit.ProductInputOrderingWitness.iThenJGroundOutput
      Circuit.ProductInputOrderingWitness.jThenIGroundOutput :=
    Circuit.ProductInputOrderingWitness.ground_outputs_not_rightPhaseEquivalent
  refine ⟨hweights.normalizedDistributionEq, hnotPhase, ?_⟩
  intro h
  exact hnotPhase (QuaternionStatePhaseEq.iff_quaternionRay_mk_eq.mpr h)

/-! ## Existing schedule and compiler classifications -/

/--
Two legal schedules of the same finite gate-occurrence family are exactly
circuit-equal when all distinct occurrence denotations commute.  This is only
a sufficient condition; no converse is claimed.
-/
theorem scheduledCircuit_exactCircuitEq_of_pairwise_commute
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {precedes : ι → ι → Prop}
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s t : LegalSchedule ι precedes) (gates : ι → PlacedGate R W)
    (hcomm : Pairwise fun i j : ι =>
      Commute (gates i).denote (gates j).denote) :
    ExactCircuitEq (s.scheduledCircuit gates) (t.scheduledCircuit gates) :=
  s.scheduledEval_eq_of_pairwise_commute t gates hcomm

/--
Exact scope of the quaternionic order-distinction witness.  The two source
schedules are not exactly circuit-equal, yet one fixed normalized ground input
has equal output weights.  They fail equality over all normalized pure inputs;
their exact complex translations also remain operator-distinct and retain the
explicit decoded bottom-outcome inequality for the fixed interference input.
-/
theorem quaternionOrderingWitness_scopeBoundary :
    ¬ ExactCircuitEq
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
          Circuit.OrderingWitness.basis00 := by
  refine ⟨?_, ?_, ?_, ?_,
    Simulation.OrderingWitness.complexOutput_basis00_weight_ne⟩
  · exact Circuit.OrderingWitness.scheduled_operators_ne
  · intro x
    exact Circuit.ProductInputOrderingWitness.ground_output_basis_weights_eq x
  · intro h
    have h00 := h Circuit.OrderingWitness.inputState
      Circuit.OrderingWitness.basis00
    apply Circuit.OrderingWitness.output_basis00_weight_ne
    simpa [OutputWeightEqAt, BasisWeightEq, basisWeight, quaternionWeight,
      Circuit.OrderingWitness.iThenJOutput,
      Circuit.OrderingWitness.jThenIOutput,
      Circuit.LegalSchedule.scheduledEval] using h00
  · exact Simulation.OrderingWitness.complexified_scheduled_operators_ne

end QuaternionicComputing.Semantics

namespace QuaternionicComputing.Circuit.ExactGateCompiler

universe u v

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/--
A supplied exact gate compiler produces a circuit that is exactly
evaluation-equal to its source circuit.  The compiler remains data: this
theorem neither constructs an instance nor asserts finite synthesis.
-/
theorem compileCircuit_exactCircuitEq (compiler : ExactGateCompiler R W)
    (circuit : OrderedCircuit R W) :
    Semantics.ExactCircuitEq (compiler.compileCircuit circuit) circuit :=
  compiler.eval_compileCircuit circuit

end QuaternionicComputing.Circuit.ExactGateCompiler
