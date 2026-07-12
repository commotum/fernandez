module

public import QuaternionicComputing.Semantics.ChannelCircuit

/-!
# Unitary-channel semantic audit

This non-root diagnostic leaf is the exact aggregate consumer for the Stage 7
channel surface.  It imports only `ChannelCircuit`, which transitively exposes
the stable channel core and phase-kernel leaves.  The allocation is:

* channel core: `20 + 11 + 10 = 41` declarations;
* phase kernel: `2 + 7 + 7 + 6 + 2 + 2 + 6 + 6 + 2 = 40` declarations;
* circuit lift: `2 + 19 + 2 + 10 + 10 + 1 + 2 + 2 + 2 + 4 + 4 = 58`
  declarations.

Thus the aggregate section covers exactly `139/139` explicitly named stable
declarations.  Generated structure projections and the two anonymous coercion
instances are excluded consistently from the named count, though the
aggregate statements exercise both coercions.

Concrete examples separately check global real sign and complex phase,
physical separation of identity from a swap unitary, chronological operator
and circuit composition, empty-index matrix behavior, and zero-wire circuit
inhabitation.  No example is part of the public root.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicComputing.Semantics.ChannelAudit

open QuaternionicComputing.Circuit

universe u v

/-! ## Exact aggregate consumers: channel core (`41`) -/

/-- Complete aggregate consumer for all 20 bundled-operator declarations. -/
theorem unitaryOperator_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    (U V W : UnitaryOperator 𝕜 I) (hUV : U = V)
    (A : Matrix I I 𝕜) (hA : A ∈ unitary (Matrix I I 𝕜))
    (rho : DensityMatrix 𝕜 I) :
    Nonempty (RealUnitaryOperator I) ∧
      Nonempty (ComplexUnitaryOperator I) ∧
      ((U : Matrix I I 𝕜) = U.matrix) ∧
      U = V ∧
      U = V ∧
      (U = V ↔ (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜)) ∧
      (((UnitaryOperator.ofMatrix A hA : UnitaryOperator 𝕜 I) :
        Matrix I I 𝕜) = A) ∧
      (((UnitaryOperator.identity : UnitaryOperator 𝕜 I) :
        Matrix I I 𝕜) = 1) ∧
      ((U.followedBy V : UnitaryOperator 𝕜 I) : Matrix I I 𝕜) =
        (V : Matrix I I 𝕜) * (U : Matrix I I 𝕜) ∧
      (U.followedBy V).followedBy W = U.followedBy (V.followedBy W) ∧
      (UnitaryOperator.identity : UnitaryOperator 𝕜 I).followedBy U = U ∧
      U.followedBy UnitaryOperator.identity = U ∧
      ((U.evolve rho : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
        (U : Matrix I I 𝕜) * (rho : Matrix I I 𝕜) *
          (U : Matrix I I 𝕜)ᴴ ∧
      (UnitaryOperator.identity : UnitaryOperator 𝕜 I).evolve rho = rho ∧
      (U.followedBy V).evolve rho = V.evolve (U.evolve rho) := by
  have hmatrix : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜) :=
    congrArg (fun T : UnitaryOperator 𝕜 I ↦ (T : Matrix I I 𝕜)) hUV
  have hentries :
      ∀ i j, (U : Matrix I I 𝕜) i j = (V : Matrix I I 𝕜) i j :=
    fun i j ↦ congrFun (congrFun hmatrix i) j
  exact ⟨⟨UnitaryOperator.identity⟩,
    ⟨UnitaryOperator.identity⟩,
    UnitaryOperator.coe_matrix U,
    UnitaryOperator.ext_matrix hmatrix,
    UnitaryOperator.ext hentries,
    UnitaryOperator.eq_iff_matrix_eq,
    UnitaryOperator.ofMatrix_coe A hA,
    UnitaryOperator.identity_coe,
    UnitaryOperator.followedBy_coe U V,
    UnitaryOperator.followedBy_assoc U V W,
    UnitaryOperator.identity_followedBy U,
    UnitaryOperator.followedBy_identity U,
    UnitaryOperator.evolve_coe U rho,
    UnitaryOperator.identity_evolve rho,
    UnitaryOperator.followedBy_evolve U V rho⟩

/-- Complete aggregate consumer for all 11 `ChannelEq` declarations. -/
theorem channelEq_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    {U V W A B : UnitaryOperator 𝕜 I}
    (hUV : ChannelEq U V) (hVW : ChannelEq V W)
    (hAB : ChannelEq A B) (hEq : U = V)
    (hMatrix : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜))
    (rho : DensityMatrix 𝕜 I) :
    ChannelEq U U ∧
      ChannelEq V U ∧
      ChannelEq U W ∧
      Equivalence (@ChannelEq 𝕜 I _ _ _) ∧
      U.evolve rho = V.evolve rho ∧
      ChannelEq U V ∧
      ChannelEq U V ∧
      AllMeasurementEq U V ∧
      ChannelEq (U.followedBy A) (V.followedBy B) ∧
      (ChannelEq U V ↔ AllMeasurementEq U V) :=
  ⟨ChannelEq.refl U,
    ChannelEq.symm hUV,
    ChannelEq.trans hUV hVW,
    ChannelEq.equivalence,
    ChannelEq.evolve_eq hUV rho,
    ChannelEq.of_eq hEq,
    ChannelEq.of_matrix_eq hMatrix,
    ChannelEq.allMeasurementEq hUV,
    ChannelEq.followedBy hUV hAB,
    channelEq_iff_allMeasurementEq U V⟩

/-- Complete aggregate consumer for all 10 `AllMeasurementEq` declarations. -/
theorem allMeasurementEq_api
    {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
    [Fintype I] [DecidableEq I]
    {U V W A B : UnitaryOperator 𝕜 I}
    (hUV : AllMeasurementEq U V) (hVW : AllMeasurementEq V W)
    (hAB : AllMeasurementEq A B) (hEq : U = V)
    (hMatrix : (U : Matrix I I 𝕜) = (V : Matrix I I 𝕜))
    (rho : DensityMatrix 𝕜 I) (F : Effect 𝕜 I) :
    AllMeasurementEq U U ∧
      AllMeasurementEq V U ∧
      AllMeasurementEq U W ∧
      Equivalence (@AllMeasurementEq 𝕜 I _ _ _) ∧
      Effect.bornValue F (U.evolve rho) =
        Effect.bornValue F (V.evolve rho) ∧
      AllMeasurementEq U V ∧
      AllMeasurementEq U V ∧
      ChannelEq U V ∧
      AllMeasurementEq (U.followedBy A) (V.followedBy B) :=
  ⟨AllMeasurementEq.refl U,
    AllMeasurementEq.symm hUV,
    AllMeasurementEq.trans hUV hVW,
    AllMeasurementEq.equivalence,
    AllMeasurementEq.bornValue_eq hUV rho F,
    AllMeasurementEq.of_eq hEq,
    AllMeasurementEq.of_matrix_eq hMatrix,
    AllMeasurementEq.channelEq hUV,
    AllMeasurementEq.followedBy hUV hAB⟩

/-! ## Exact aggregate consumers: phase kernel (`40`) -/

/-- Complete consumer for the two normalized pure-density phase bridges. -/
theorem pureDensityPhase_api
    {I : Type u} [Fintype I]
    {xr yr : I → ℝ} (hxr : star xr ⬝ᵥ xr = 1)
    (her : DensityMatrix.pureMatrix xr = DensityMatrix.pureMatrix yr)
    {xc yc : I → ℂ} (hxc : star xc ⬝ᵥ xc = 1)
    (hec : DensityMatrix.pureMatrix xc = DensityMatrix.pureMatrix yc) :
    Real.SignEquivalent xr yr ∧ Complex.RightPhaseEquivalent xc yc :=
  ⟨realSignEquivalent_of_normalized_pureMatrix_eq hxr her,
    complexRightPhaseEquivalent_of_normalized_pureMatrix_eq hxc hec⟩

/-- Complete consumer for all seven real raw-projective declarations. -/
theorem realRawProjective_api
    {O : Type u} {I : Type v} [Fintype I]
    {U V W : Matrix O I ℝ}
    (hUV : RealRawProjectiveActionEq U V)
    (hVW : RealRawProjectiveActionEq V W)
    (hExact : ExactOperatorEq U V) :
    RealRawProjectiveActionEq U U ∧
      RealRawProjectiveActionEq V U ∧
      RealRawProjectiveActionEq U W ∧
      Equivalence (@RealRawProjectiveActionEq O I _) ∧
      RealRawProjectiveActionEq U V ∧
      RealProjectiveActionEq U V :=
  ⟨RealRawProjectiveActionEq.refl U,
    RealRawProjectiveActionEq.symm hUV,
    RealRawProjectiveActionEq.trans hUV hVW,
    RealRawProjectiveActionEq.equivalence,
    RealRawProjectiveActionEq.of_exact hExact,
    RealRawProjectiveActionEq.projectiveActionEq hUV⟩

/-- Complete consumer for all seven complex raw-projective declarations. -/
theorem complexRawProjective_api
    {O : Type u} {I : Type v} [Fintype I]
    {U V W : Matrix O I ℂ}
    (hUV : ComplexRawProjectiveActionEq U V)
    (hVW : ComplexRawProjectiveActionEq V W)
    (hExact : ExactOperatorEq U V) :
    ComplexRawProjectiveActionEq U U ∧
      ComplexRawProjectiveActionEq V U ∧
      ComplexRawProjectiveActionEq U W ∧
      Equivalence (@ComplexRawProjectiveActionEq O I _) ∧
      ComplexRawProjectiveActionEq U V ∧
      ComplexProjectiveActionEq U V :=
  ⟨ComplexRawProjectiveActionEq.refl U,
    ComplexRawProjectiveActionEq.symm hUV,
    ComplexRawProjectiveActionEq.trans hUV hVW,
    ComplexRawProjectiveActionEq.equivalence,
    ComplexRawProjectiveActionEq.of_exact hExact,
    ComplexRawProjectiveActionEq.projectiveActionEq hUV⟩

/-- Complete consumer for the six raw/normalized/global forward bridges. -/
theorem normalizedRawProjective_api
    {O : Type u} {I : Type v} [Fintype I]
    {UR VR : Matrix O I ℝ} {UC VC : Matrix O I ℂ}
    (hRP : RealProjectiveActionEq UR VR)
    (hCP : ComplexProjectiveActionEq UC VC)
    (hRG : RealGlobalSignEq UR VR)
    (hCG : ComplexGlobalPhaseEq UC VC) :
    RealRawProjectiveActionEq UR VR ∧
      ComplexRawProjectiveActionEq UC VC ∧
      (RealRawProjectiveActionEq UR VR ↔ RealProjectiveActionEq UR VR) ∧
      (ComplexRawProjectiveActionEq UC VC ↔
        ComplexProjectiveActionEq UC VC) ∧
      RealRawProjectiveActionEq UR VR ∧
      ComplexRawProjectiveActionEq UC VC :=
  ⟨RealProjectiveActionEq.rawProjectiveActionEq hRP,
    ComplexProjectiveActionEq.rawProjectiveActionEq hCP,
    realRawProjectiveActionEq_iff_projectiveActionEq,
    complexRawProjectiveActionEq_iff_projectiveActionEq,
    RealGlobalSignEq.rawProjectiveActionEq hRG,
    ComplexGlobalPhaseEq.rawProjectiveActionEq hCG⟩

/-- Complete consumer for the two inhabited real projective-kernel theorems. -/
theorem realProjectiveKernel_api
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℝ}
    (hU : U ∈ unitary (Matrix I I ℝ))
    (hRaw : RealRawProjectiveActionEq U V)
    (hProjective : RealProjectiveActionEq U V) :
    RealGlobalSignEq U V ∧ RealGlobalSignEq U V :=
  ⟨RealRawProjectiveActionEq.globalSignEq_of_unitary hU hRaw,
    RealProjectiveActionEq.globalSignEq_of_unitary hU hProjective⟩

/-- Complete consumer for the two inhabited complex projective-kernel theorems. -/
theorem complexProjectiveKernel_api
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    {U V : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ))
    (hRaw : ComplexRawProjectiveActionEq U V)
    (hProjective : ComplexProjectiveActionEq U V) :
    ComplexGlobalPhaseEq U V ∧ ComplexGlobalPhaseEq U V :=
  ⟨ComplexRawProjectiveActionEq.globalPhaseEq_of_unitary hU hRaw,
    ComplexProjectiveActionEq.globalPhaseEq_of_unitary hU hProjective⟩

/-- Complete consumer for all six real channel/phase characterizations. -/
theorem realChannelPhase_api
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : RealUnitaryOperator I)
    (hGlobal : RealGlobalSignEq
      (U : Matrix I I ℝ) (V : Matrix I I ℝ))
    (hChannel : ChannelEq U V) :
    ChannelEq U V ∧
      RealProjectiveActionEq
        (U : Matrix I I ℝ) (V : Matrix I I ℝ) ∧
      RealRawProjectiveActionEq
        (U : Matrix I I ℝ) (V : Matrix I I ℝ) ∧
      (RealGlobalSignEq (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔
        ChannelEq U V) ∧
      (RealProjectiveActionEq
          (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔ ChannelEq U V) ∧
      (RealRawProjectiveActionEq
          (U : Matrix I I ℝ) (V : Matrix I I ℝ) ↔ ChannelEq U V) :=
  ⟨RealGlobalSignEq.channelEq hGlobal,
    ChannelEq.realProjectiveActionEq hChannel,
    ChannelEq.realRawProjectiveActionEq hChannel,
    realGlobalSignEq_iff_channelEq U V,
    realProjectiveActionEq_iff_channelEq U V,
    realRawProjectiveActionEq_iff_channelEq U V⟩

/-- Complete consumer for all six complex channel/phase characterizations. -/
theorem complexChannelPhase_api
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (U V : ComplexUnitaryOperator I)
    (hGlobal : ComplexGlobalPhaseEq
      (U : Matrix I I ℂ) (V : Matrix I I ℂ))
    (hChannel : ChannelEq U V) :
    ChannelEq U V ∧
      ComplexProjectiveActionEq
        (U : Matrix I I ℂ) (V : Matrix I I ℂ) ∧
      ComplexRawProjectiveActionEq
        (U : Matrix I I ℂ) (V : Matrix I I ℂ) ∧
      (ComplexGlobalPhaseEq (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔
        ChannelEq U V) ∧
      (ComplexProjectiveActionEq
          (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔ ChannelEq U V) ∧
      (ComplexRawProjectiveActionEq
          (U : Matrix I I ℂ) (V : Matrix I I ℂ) ↔ ChannelEq U V) :=
  ⟨ComplexGlobalPhaseEq.channelEq hGlobal,
    ChannelEq.complexProjectiveActionEq hChannel,
    ChannelEq.complexRawProjectiveActionEq hChannel,
    complexGlobalPhaseEq_iff_channelEq U V,
    complexProjectiveActionEq_iff_channelEq U V,
    complexRawProjectiveActionEq_iff_channelEq U V⟩

/-- Complete consumer for both empty-index matrix boundary theorems. -/
theorem emptyPhaseBoundary_api
    {I : Type u} [Fintype I] [DecidableEq I] [IsEmpty I]
    (UR VR : RealUnitaryOperator I) (UC VC : ComplexUnitaryOperator I) :
    RealGlobalSignEq (UR : Matrix I I ℝ) (VR : Matrix I I ℝ) ∧
      ComplexGlobalPhaseEq (UC : Matrix I I ℂ) (VC : Matrix I I ℂ) :=
  ⟨realGlobalSignEq_of_isEmpty UR VR,
    complexGlobalPhaseEq_of_isEmpty UC VC⟩

/-! ## Exact aggregate consumers: circuit lift (`58`) -/

/-- Complete consumer for the two circuit-to-operator constructor declarations. -/
theorem ofCircuit_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    (C : OrderedCircuit 𝕜 W) (hC : C.IsLocallyUnitary) :
    ((UnitaryOperator.ofCircuit C hC :
      UnitaryOperator 𝕜 (BitBasis W)) :
        Matrix (BitBasis W) (BitBasis W) 𝕜) = C.eval :=
  UnitaryOperator.ofCircuit_coe C hC

/-- Complete aggregate consumer for all 19 certified-circuit declarations. -/
theorem unitaryCircuit_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    (C D E : UnitaryCircuit 𝕜 W) (hCD : C.circuit = D.circuit) :
    Nonempty (RealUnitaryCircuit W) ∧
      Nonempty (ComplexUnitaryCircuit W) ∧
      ((C : OrderedCircuit 𝕜 W) = C.circuit) ∧
      C = D ∧
      C = D ∧
      (C = D ↔ C.circuit = D.circuit) ∧
      C.circuit.eval ∈
        unitary (Matrix (BitBasis W) (BitBasis W) 𝕜) ∧
      ((C.toOperator : UnitaryOperator 𝕜 (BitBasis W)) :
        Matrix (BitBasis W) (BitBasis W) 𝕜) = C.circuit.eval ∧
      (UnitaryCircuit.identity : UnitaryCircuit 𝕜 W).circuit = [] ∧
      (UnitaryCircuit.identity : UnitaryCircuit 𝕜 W).toOperator =
        UnitaryOperator.identity ∧
      (C.append D).circuit = C.circuit ++ D.circuit ∧
      (C.append D).append E = C.append (D.append E) ∧
      (UnitaryCircuit.identity : UnitaryCircuit 𝕜 W).append C = C ∧
      C.append UnitaryCircuit.identity = C ∧
      (C.append D).toOperator = C.toOperator.followedBy D.toOperator := by
  have hcoe : (C : OrderedCircuit 𝕜 W) = (D : OrderedCircuit 𝕜 W) := by
    simpa only [UnitaryCircuit.coe_circuit] using hCD
  exact ⟨⟨UnitaryCircuit.identity⟩,
    ⟨UnitaryCircuit.identity⟩,
    UnitaryCircuit.coe_circuit C,
    UnitaryCircuit.ext_circuit hCD,
    UnitaryCircuit.ext hcoe,
    UnitaryCircuit.eq_iff_circuit_eq,
    UnitaryCircuit.eval_mem_unitary C,
    UnitaryCircuit.toOperator_coe C,
    UnitaryCircuit.identity_circuit,
    UnitaryCircuit.toOperator_identity,
    UnitaryCircuit.append_circuit C D,
    UnitaryCircuit.append_assoc C D E,
    UnitaryCircuit.identity_append C,
    UnitaryCircuit.append_identity C,
    UnitaryCircuit.toOperator_append C D⟩

/-- Complete consumer for the two evaluator-backed circuit relation definitions. -/
theorem circuitRelationDefinitions_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    (C D : UnitaryCircuit 𝕜 W) :
    (CircuitChannelEq C D ↔ ChannelEq C.toOperator D.toOperator) ∧
      (CircuitAllMeasurementEq C D ↔
        AllMeasurementEq C.toOperator D.toOperator) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Complete consumer for all ten `CircuitChannelEq` namespace declarations. -/
theorem circuitChannelEq_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    {C D E C1 C2 D1 D2 : UnitaryCircuit 𝕜 W}
    (hCD : CircuitChannelEq C D) (hDE : CircuitChannelEq D E)
    (h1 : CircuitChannelEq C1 D1) (h2 : CircuitChannelEq C2 D2)
    (rho : DensityMatrix 𝕜 (BitBasis W)) :
    (CircuitChannelEq C D ↔ ChannelEq C.toOperator D.toOperator) ∧
      C.toOperator.evolve rho = D.toOperator.evolve rho ∧
      CircuitChannelEq C C ∧
      CircuitChannelEq D C ∧
      CircuitChannelEq C E ∧
      Equivalence (@CircuitChannelEq 𝕜 W _ _) ∧
      CircuitAllMeasurementEq C D ∧
      CircuitChannelEq (C1.append C2) (D1.append D2) ∧
      CircuitChannelEq (C.append E) (D.append E) ∧
      CircuitChannelEq (E.append C) (E.append D) :=
  ⟨CircuitChannelEq.iff_toOperator,
    CircuitChannelEq.evolve_eq hCD rho,
    CircuitChannelEq.refl C,
    CircuitChannelEq.symm hCD,
    CircuitChannelEq.trans hCD hDE,
    CircuitChannelEq.equivalence,
    CircuitChannelEq.allMeasurementEq hCD,
    CircuitChannelEq.append h1 h2,
    CircuitChannelEq.append_same_later E hCD,
    CircuitChannelEq.prepend_same_earlier E hCD⟩

/-- Complete consumer for all ten `CircuitAllMeasurementEq` declarations. -/
theorem circuitAllMeasurementEq_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    {C D E C1 C2 D1 D2 : UnitaryCircuit 𝕜 W}
    (hCD : CircuitAllMeasurementEq C D)
    (hDE : CircuitAllMeasurementEq D E)
    (h1 : CircuitAllMeasurementEq C1 D1)
    (h2 : CircuitAllMeasurementEq C2 D2)
    (rho : DensityMatrix 𝕜 (BitBasis W))
    (F : Effect 𝕜 (BitBasis W)) :
    (CircuitAllMeasurementEq C D ↔
      AllMeasurementEq C.toOperator D.toOperator) ∧
      Effect.bornValue F (C.toOperator.evolve rho) =
        Effect.bornValue F (D.toOperator.evolve rho) ∧
      CircuitAllMeasurementEq C C ∧
      CircuitAllMeasurementEq D C ∧
      CircuitAllMeasurementEq C E ∧
      Equivalence (@CircuitAllMeasurementEq 𝕜 W _ _) ∧
      CircuitChannelEq C D ∧
      CircuitAllMeasurementEq (C1.append C2) (D1.append D2) ∧
      CircuitAllMeasurementEq (C.append E) (D.append E) ∧
      CircuitAllMeasurementEq (E.append C) (E.append D) :=
  ⟨CircuitAllMeasurementEq.iff_toOperator,
    CircuitAllMeasurementEq.bornValue_eq hCD rho F,
    CircuitAllMeasurementEq.refl C,
    CircuitAllMeasurementEq.symm hCD,
    CircuitAllMeasurementEq.trans hCD hDE,
    CircuitAllMeasurementEq.equivalence,
    CircuitAllMeasurementEq.channelEq hCD,
    CircuitAllMeasurementEq.append h1 h2,
    CircuitAllMeasurementEq.append_same_later E hCD,
    CircuitAllMeasurementEq.prepend_same_earlier E hCD⟩

/-- Complete consumer for the circuit channel/all-measurement equivalence. -/
theorem circuitChannelMeasurementIff_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    (C D : UnitaryCircuit 𝕜 W) :
    CircuitChannelEq C D ↔ CircuitAllMeasurementEq C D :=
  circuitChannelEq_iff_allMeasurementEq C D

/-- Complete consumer for both exact-evaluator implications. -/
theorem exactCircuitChannel_api
    {𝕜 : Type u} {W : Type v} [RCLike 𝕜] [Fintype W]
    {C D : UnitaryCircuit 𝕜 W}
    (h : ExactCircuitEq C.circuit D.circuit) :
    CircuitChannelEq C D ∧ CircuitAllMeasurementEq C D :=
  ⟨ExactCircuitEq.circuitChannelEq h,
    ExactCircuitEq.circuitAllMeasurementEq h⟩

/-- Complete consumer for both real circuit global-sign implications. -/
theorem realCircuitGlobalSign_api
    {W : Type u} [Fintype W] {C D : RealUnitaryCircuit W}
    (h : RealCircuitGlobalSignEq C.circuit D.circuit) :
    CircuitChannelEq C D ∧ CircuitAllMeasurementEq C D :=
  ⟨RealCircuitGlobalSignEq.circuitChannelEq h,
    RealCircuitGlobalSignEq.circuitAllMeasurementEq h⟩

/-- Complete consumer for both complex circuit global-phase implications. -/
theorem complexCircuitGlobalPhase_api
    {W : Type u} [Fintype W] {C D : ComplexUnitaryCircuit W}
    (h : ComplexCircuitGlobalPhaseEq C.circuit D.circuit) :
    CircuitChannelEq C D ∧ CircuitAllMeasurementEq C D :=
  ⟨ComplexCircuitGlobalPhaseEq.circuitChannelEq h,
    ComplexCircuitGlobalPhaseEq.circuitAllMeasurementEq h⟩

/-- Complete consumer for the four channel-to-circuit-phase projections. -/
theorem circuitChannelPhase_api
    {W : Type u} [Fintype W]
    {CR DR : RealUnitaryCircuit W} {CC DC : ComplexUnitaryCircuit W}
    (hR : CircuitChannelEq CR DR) (hC : CircuitChannelEq CC DC) :
    RealCircuitGlobalSignEq CR.circuit DR.circuit ∧
      ComplexCircuitGlobalPhaseEq CC.circuit DC.circuit ∧
      RealCircuitProjectiveActionEq CR.circuit DR.circuit ∧
      ComplexCircuitProjectiveActionEq CC.circuit DC.circuit :=
  ⟨CircuitChannelEq.realGlobalSignEq hR,
    CircuitChannelEq.complexGlobalPhaseEq hC,
    CircuitChannelEq.realProjectiveActionEq hR,
    CircuitChannelEq.complexProjectiveActionEq hC⟩

/-- Complete consumer for the four exact circuit phase/channel iff theorems. -/
theorem circuitPhaseIff_api
    {W : Type u} [Fintype W]
    (CR DR : RealUnitaryCircuit W) (CC DC : ComplexUnitaryCircuit W) :
    (RealCircuitGlobalSignEq CR.circuit DR.circuit ↔
      CircuitChannelEq CR DR) ∧
      (ComplexCircuitGlobalPhaseEq CC.circuit DC.circuit ↔
        CircuitChannelEq CC DC) ∧
      (RealCircuitProjectiveActionEq CR.circuit DR.circuit ↔
        CircuitChannelEq CR DR) ∧
      (ComplexCircuitProjectiveActionEq CC.circuit DC.circuit ↔
        CircuitChannelEq CC DC) :=
  ⟨realCircuitGlobalSignEq_iff_channelEq CR DR,
    complexCircuitGlobalPhaseEq_iff_channelEq CC DC,
    realCircuitProjectiveActionEq_iff_channelEq CR DR,
    complexCircuitProjectiveActionEq_iff_channelEq CC DC⟩

/-! ## Concrete two-level phase and channel witnesses -/

/-- The real negative identity matrix is unitary on the Boolean basis. -/
theorem realNegIdentity_mem_unitary :
    (-1 : Matrix Bool Bool ℝ) ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> simp

/-- The real negative identity bundled as a physical unitary operator. -/
def realNegIdentity : RealUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix (-1) realNegIdentity_mem_unitary

/-- Identity and negative identity differ by exactly one global sign. -/
theorem real_identity_neg_globalSign :
    RealGlobalSignEq
      ((UnitaryOperator.identity : RealUnitaryOperator Bool) :
        Matrix Bool Bool ℝ)
      (realNegIdentity : Matrix Bool Bool ℝ) := by
  refine ⟨-1, by norm_num, ?_⟩
  apply Matrix.ext
  intro i j
  simp [realNegIdentity, UnitaryOperator.identity,
    UnitaryOperator.ofMatrix]

/-- Global negative sign preserves the complete channel and every physical effect. -/
theorem real_identity_neg_channel_and_measurement :
    ChannelEq (UnitaryOperator.identity : RealUnitaryOperator Bool)
        realNegIdentity ∧
      AllMeasurementEq (UnitaryOperator.identity : RealUnitaryOperator Bool)
        realNegIdentity := by
  have h := RealGlobalSignEq.channelEq real_identity_neg_globalSign
  exact ⟨h, h.allMeasurementEq⟩

/-- The complex scalar-`I` identity matrix. -/
def complexIIdentityMatrix : Matrix Bool Bool ℂ :=
  Complex.I • (1 : Matrix Bool Bool ℂ)

/-- The scalar-`I` identity is unitary. -/
theorem complexIIdentity_mem_unitary :
    complexIIdentityMatrix ∈ unitary (Matrix Bool Bool ℂ) := by
  apply ComplexGlobalPhaseEq.mem_unitary
    (U := (1 : Matrix Bool Bool ℂ))
  · exact ⟨Complex.I, by norm_num, rfl⟩
  · exact (unitary (Matrix Bool Bool ℂ)).one_mem

/-- The scalar-`I` identity bundled as a complex unitary operator. -/
def complexIIdentity : ComplexUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix complexIIdentityMatrix
    complexIIdentity_mem_unitary

/-- Identity and scalar-`I` identity differ by exactly one global phase. -/
theorem complex_identity_I_globalPhase :
    ComplexGlobalPhaseEq
      ((UnitaryOperator.identity : ComplexUnitaryOperator Bool) :
        Matrix Bool Bool ℂ)
      (complexIIdentity : Matrix Bool Bool ℂ) := by
  refine ⟨Complex.I, by norm_num, ?_⟩
  rfl

/-- Global complex phase `I` preserves the complete channel and every effect. -/
theorem complex_identity_I_channel_and_measurement :
    ChannelEq (UnitaryOperator.identity : ComplexUnitaryOperator Bool)
        complexIIdentity ∧
      AllMeasurementEq (UnitaryOperator.identity : ComplexUnitaryOperator Bool)
        complexIIdentity := by
  have h := ComplexGlobalPhaseEq.channelEq complex_identity_I_globalPhase
  exact ⟨h, h.allMeasurementEq⟩

/-- The concrete phase witnesses satisfy every raw/normalized/channel iff. -/
theorem concrete_phase_characterizations :
    (RealRawProjectiveActionEq
        ((UnitaryOperator.identity : RealUnitaryOperator Bool) :
          Matrix Bool Bool ℝ)
        (realNegIdentity : Matrix Bool Bool ℝ) ↔
      RealProjectiveActionEq
        ((UnitaryOperator.identity : RealUnitaryOperator Bool) :
          Matrix Bool Bool ℝ)
        (realNegIdentity : Matrix Bool Bool ℝ)) ∧
      (RealGlobalSignEq
          ((UnitaryOperator.identity : RealUnitaryOperator Bool) :
            Matrix Bool Bool ℝ)
          (realNegIdentity : Matrix Bool Bool ℝ) ↔
        ChannelEq (UnitaryOperator.identity : RealUnitaryOperator Bool)
          realNegIdentity) ∧
      (ComplexRawProjectiveActionEq
          ((UnitaryOperator.identity : ComplexUnitaryOperator Bool) :
            Matrix Bool Bool ℂ)
          (complexIIdentity : Matrix Bool Bool ℂ) ↔
        ComplexProjectiveActionEq
          ((UnitaryOperator.identity : ComplexUnitaryOperator Bool) :
            Matrix Bool Bool ℂ)
          (complexIIdentity : Matrix Bool Bool ℂ)) ∧
      (ComplexGlobalPhaseEq
          ((UnitaryOperator.identity : ComplexUnitaryOperator Bool) :
            Matrix Bool Bool ℂ)
          (complexIIdentity : Matrix Bool Bool ℂ) ↔
        ChannelEq (UnitaryOperator.identity : ComplexUnitaryOperator Bool)
          complexIIdentity) :=
  ⟨realRawProjectiveActionEq_iff_projectiveActionEq,
    realGlobalSignEq_iff_channelEq _ _,
    complexRawProjectiveActionEq_iff_projectiveActionEq,
    complexGlobalPhaseEq_iff_channelEq _ _⟩

/-! ## A genuinely distinct channel separated by a physical effect -/

/-- The Boolean swap permutation matrix over the reals. -/
def realSwapMatrix : Matrix Bool Bool ℝ :=
  fun y x ↦ if y = !x then 1 else 0

/-- The Boolean swap permutation matrix is unitary. -/
theorem realSwapMatrix_mem_unitary :
    realSwapMatrix ∈ unitary (Matrix Bool Bool ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> cases i <;> cases j <;>
    norm_num [realSwapMatrix, Matrix.mul_apply, Fintype.univ_bool]

/-- The Boolean swap bundled as a real unitary operator. -/
def realSwapOperator : RealUnitaryOperator Bool :=
  UnitaryOperator.ofMatrix realSwapMatrix realSwapMatrix_mem_unitary

/-- The swap sends the false basis density to the true basis density. -/
theorem realSwap_evolve_false :
    realSwapOperator.evolve (DensityMatrix.basis (𝕜 := ℝ) false) =
      DensityMatrix.basis (𝕜 := ℝ) true := by
  apply DensityMatrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [UnitaryOperator.evolve_coe, realSwapOperator, realSwapMatrix,
      Matrix.mul_apply, DensityMatrix.basis_apply, Fintype.univ_bool]

/--
A basis density and genuine basis effect distinguish identity from swap, so
the two unitaries have neither equal channels nor equal all-effect behavior.
-/
theorem identity_swap_physically_separated :
    Effect.bornValue (Effect.basis (𝕜 := ℝ) false)
        ((UnitaryOperator.identity : RealUnitaryOperator Bool).evolve
          (DensityMatrix.basis (𝕜 := ℝ) false)) = 1 ∧
      Effect.bornValue (Effect.basis (𝕜 := ℝ) false)
        (realSwapOperator.evolve
          (DensityMatrix.basis (𝕜 := ℝ) false)) = 0 ∧
      ¬ ChannelEq (UnitaryOperator.identity : RealUnitaryOperator Bool)
        realSwapOperator ∧
      ¬ AllMeasurementEq
        (UnitaryOperator.identity : RealUnitaryOperator Bool)
        realSwapOperator := by
  have hone :
      Effect.bornValue (Effect.basis (𝕜 := ℝ) false)
          ((UnitaryOperator.identity : RealUnitaryOperator Bool).evolve
            (DensityMatrix.basis (𝕜 := ℝ) false)) = 1 := by
    simp [Effect.bornValue_basis_basis]
  have hzero :
      Effect.bornValue (Effect.basis (𝕜 := ℝ) false)
          (realSwapOperator.evolve
            (DensityMatrix.basis (𝕜 := ℝ) false)) = 0 := by
    rw [realSwap_evolve_false]
    simp [Effect.bornValue_basis_basis]
  refine ⟨hone, hzero, ?_, ?_⟩
  · intro h
    have heq := congrArg
      (Effect.bornValue (Effect.basis (𝕜 := ℝ) false))
      (h (DensityMatrix.basis (𝕜 := ℝ) false))
    rw [hone, hzero] at heq
    norm_num at heq
  · intro h
    have heq := h (DensityMatrix.basis (𝕜 := ℝ) false)
      (Effect.basis (𝕜 := ℝ) false)
    rw [hone, hzero] at heq
    norm_num at heq

/-! ## Chronology and dimensional boundaries -/

/-- Operator composition and circuit append expose the same chronological order. -/
theorem chronological_operator_and_circuit
    {𝕜 : Type u} {I : Type v} {W : Type*} [RCLike 𝕜]
    [Fintype I] [DecidableEq I] [Fintype W]
    (U V : UnitaryOperator 𝕜 I) (rho : DensityMatrix 𝕜 I)
    (C D : UnitaryCircuit 𝕜 W) :
    ((U.followedBy V : UnitaryOperator 𝕜 I) : Matrix I I 𝕜) =
        (V : Matrix I I 𝕜) * (U : Matrix I I 𝕜) ∧
      (U.followedBy V).evolve rho = V.evolve (U.evolve rho) ∧
      (C.append D).circuit = C.circuit ++ D.circuit ∧
      (C.append D).toOperator =
        C.toOperator.followedBy D.toOperator :=
  ⟨UnitaryOperator.followedBy_coe U V,
    UnitaryOperator.followedBy_evolve U V rho,
    UnitaryCircuit.append_circuit C D,
    UnitaryCircuit.toOperator_append C D⟩

/--
On an empty index type, square matrices are equal independently of the
physically vacuous density-input channel quantifier; both phase boundary
theorems record only this exact matrix fact.
-/
theorem empty_index_matrix_boundary
    (UR VR : RealUnitaryOperator Empty)
    (UC VC : ComplexUnitaryOperator Empty) :
    (UR : Matrix Empty Empty ℝ) = (VR : Matrix Empty Empty ℝ) ∧
      (UC : Matrix Empty Empty ℂ) = (VC : Matrix Empty Empty ℂ) ∧
      RealGlobalSignEq
        (UR : Matrix Empty Empty ℝ) (VR : Matrix Empty Empty ℝ) ∧
      ComplexGlobalPhaseEq
        (UC : Matrix Empty Empty ℂ) (VC : Matrix Empty Empty ℂ) :=
  ⟨Subsingleton.elim _ _,
    Subsingleton.elim _ _,
    realGlobalSignEq_of_isEmpty UR VR,
    complexGlobalPhaseEq_of_isEmpty UC VC⟩

/-- Empty-index channel equality is vacuous because no density input exists. -/
theorem empty_channel_vacuous
    (U V : RealUnitaryOperator Empty) : ChannelEq U V := by
  intro rho
  exact (DensityMatrix.isEmpty_of_index_isEmpty.false rho).elim

/-- The zero-wire Boolean basis and its real/complex identity circuits are inhabited. -/
theorem zeroWire_circuit_inhabited :
    Nonempty (BitBasis Empty) ∧
      Nonempty (RealUnitaryCircuit Empty) ∧
      Nonempty (ComplexUnitaryCircuit Empty) ∧
      CircuitChannelEq
        (UnitaryCircuit.identity : RealUnitaryCircuit Empty)
        UnitaryCircuit.identity ∧
      CircuitAllMeasurementEq
        (UnitaryCircuit.identity : ComplexUnitaryCircuit Empty)
        UnitaryCircuit.identity :=
  ⟨⟨fun _ ↦ false⟩,
    ⟨UnitaryCircuit.identity⟩,
    ⟨UnitaryCircuit.identity⟩,
    CircuitChannelEq.refl _,
    CircuitAllMeasurementEq.refl _⟩

/-! ## Representative local axiom audit -/

#print axioms unitaryOperator_api
#print axioms channelEq_api
#print axioms pureDensityPhase_api
#print axioms realChannelPhase_api
#print axioms unitaryCircuit_api
#print axioms circuitChannelEq_api
#print axioms circuitPhaseIff_api
#print axioms identity_swap_physically_separated
#print axioms empty_index_matrix_boundary
#print axioms empty_channel_vacuous
#print axioms zeroWire_circuit_inhabited

end QuaternionicComputing.Semantics.ChannelAudit
