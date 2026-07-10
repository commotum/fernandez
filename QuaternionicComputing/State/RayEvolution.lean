module

public import QuaternionicComputing.State.Ray
public import QuaternionicComputing.State.Unitary
public import QuaternionicComputing.Circuit.LocalUnitary

/-!
# Unitary evolution of normalized rays

Unitary matrices preserve normalization and arbitrary left matrix action
preserves the scalar-correct right-phase relations.  Consequently real,
complex, and quaternionic unitary evolution descends to normalized ray
quotients.  Locally-unitary chronological circuits act through their unitary
evaluators.

Composition order is explicit and noncommutative-safe: applying `U` and then
`V` is multiplication by `V * U`, while a chronological append `C ++ D` acts
first by `C` and then by `D`.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.State

universe u v

/-! ## Real-ray evolution -/

namespace RealRay

variable {I : Type u} [Fintype I]

/-- Evolve a normalized real sign ray by a real unitary matrix. -/
def evolveUnitary [DecidableEq I] (r : RealRay I)
    (U : Matrix I I ℝ) (hU : U ∈ unitary (Matrix I I ℝ)) : RealRay I :=
  lift (fun a ↦ mk (RealState.evolveUnitary a U hU))
    (fun _ _ h ↦ mk_eq_mk_iff.mpr (signEquivalent_real_mulVec U h)) r

/-- Real-ray unitary evolution computes on any normalized representative. -/
@[simp]
theorem evolveUnitary_mk [DecidableEq I] (a : RealState I)
    (U : Matrix I I ℝ) (hU : U ∈ unitary (Matrix I I ℝ)) :
    evolveUnitary (mk a) U hU = mk (RealState.evolveUnitary a U hU) :=
  rfl

/-- The identity real unitary acts identically on real rays. -/
@[simp]
theorem evolveUnitary_one [DecidableEq I] (r : RealRay I) :
    evolveUnitary r 1 (unitary (Matrix I I ℝ)).one_mem = r := by
  refine inductionOn r ?_
  intro a
  rw [evolveUnitary_mk, mk_eq_mk_iff]
  have heq : RealState.evolveUnitary a 1
      (unitary (Matrix I I ℝ)).one_mem = a :=
    Subtype.ext (Matrix.one_mulVec (a : I → ℝ))
  rw [heq]
  exact Real.signEquivalent_refl a

/-- Applying real unitaries `U` then `V` is the action of `V * U`. -/
theorem evolveUnitary_comp [DecidableEq I] (r : RealRay I)
    (U V : Matrix I I ℝ)
    (hU : U ∈ unitary (Matrix I I ℝ))
    (hV : V ∈ unitary (Matrix I I ℝ)) :
    evolveUnitary (evolveUnitary r U hU) V hV =
      evolveUnitary r (V * U)
        ((unitary (Matrix I I ℝ)).mul_mem hV hU) := by
  refine inductionOn r ?_
  intro a
  simp only [evolveUnitary_mk]
  rw [mk_eq_mk_iff]
  have heq : RealState.evolveUnitary (RealState.evolveUnitary a U hU) V hV =
      RealState.evolveUnitary a (V * U)
        ((unitary (Matrix I I ℝ)).mul_mem hV hU) :=
    Subtype.ext (Matrix.mulVec_mulVec (a : I → ℝ) V U)
  rw [heq]
  exact Real.signEquivalent_refl _

variable {W : Type v} [Fintype W]

/-- Evolve a real ray by a chronological circuit of locally-unitary gates. -/
def evolveCircuit (r : RealRay (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℝ W) (hC : C.IsLocallyUnitary) :
    RealRay (Circuit.BitBasis W) := by
  classical
  exact evolveUnitary r C.eval (C.eval_mem_unitary hC)

/-- Real-ray circuit evolution computes on any normalized representative. -/
@[simp]
theorem evolveCircuit_mk (a : RealState (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℝ W) (hC : C.IsLocallyUnitary) :
    evolveCircuit (mk a) C hC =
      mk (RealState.evolveUnitary a C.eval (C.eval_mem_unitary hC)) := by
  classical
  rfl

/-- The empty real circuit acts identically on real rays. -/
@[simp]
theorem evolveCircuit_nil (r : RealRay (Circuit.BitBasis W)) :
    evolveCircuit r [] Circuit.OrderedCircuit.isLocallyUnitary_nil = r := by
  classical
  exact evolveUnitary_one r

/-- Chronological append acts on a real ray first by `C` and then by `D`. -/
theorem evolveCircuit_append (r : RealRay (Circuit.BitBasis W))
    (C D : Circuit.OrderedCircuit ℝ W)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    evolveCircuit r (C ++ D) (hC.append hD) =
      evolveCircuit (evolveCircuit r C hC) D hD := by
  classical
  simpa only [evolveCircuit, Circuit.OrderedCircuit.eval_append] using
    (evolveUnitary_comp r C.eval D.eval
      (C.eval_mem_unitary hC) (D.eval_mem_unitary hD)).symm

end RealRay

/-! ## Complex-ray evolution -/

namespace ComplexRay

variable {I : Type u} [Fintype I]

/-- Evolve a normalized complex phase ray by a complex unitary matrix. -/
def evolveUnitary [DecidableEq I] (r : ComplexRay I)
    (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ)) : ComplexRay I :=
  lift (fun a ↦ mk (ComplexState.evolveUnitary a U hU))
    (fun _ _ h ↦ mk_eq_mk_iff.mpr
      (rightPhaseEquivalent_complex_mulVec U h)) r

/-- Complex-ray unitary evolution computes on any normalized representative. -/
@[simp]
theorem evolveUnitary_mk [DecidableEq I] (a : ComplexState I)
    (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ)) :
    evolveUnitary (mk a) U hU = mk (ComplexState.evolveUnitary a U hU) :=
  rfl

/-- The identity complex unitary acts identically on complex rays. -/
@[simp]
theorem evolveUnitary_one [DecidableEq I] (r : ComplexRay I) :
    evolveUnitary r 1 (unitary (Matrix I I ℂ)).one_mem = r := by
  refine inductionOn r ?_
  intro a
  rw [evolveUnitary_mk, mk_eq_mk_iff]
  have heq : ComplexState.evolveUnitary a 1
      (unitary (Matrix I I ℂ)).one_mem = a :=
    Subtype.ext (Matrix.one_mulVec (a : I → ℂ))
  rw [heq]
  exact Complex.rightPhaseEquivalent_refl a

/-- Applying complex unitaries `U` then `V` is the action of `V * U`. -/
theorem evolveUnitary_comp [DecidableEq I] (r : ComplexRay I)
    (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ))
    (hV : V ∈ unitary (Matrix I I ℂ)) :
    evolveUnitary (evolveUnitary r U hU) V hV =
      evolveUnitary r (V * U)
        ((unitary (Matrix I I ℂ)).mul_mem hV hU) := by
  refine inductionOn r ?_
  intro a
  simp only [evolveUnitary_mk]
  rw [mk_eq_mk_iff]
  have heq :
      ComplexState.evolveUnitary (ComplexState.evolveUnitary a U hU) V hV =
        ComplexState.evolveUnitary a (V * U)
          ((unitary (Matrix I I ℂ)).mul_mem hV hU) :=
    Subtype.ext (Matrix.mulVec_mulVec (a : I → ℂ) V U)
  rw [heq]
  exact Complex.rightPhaseEquivalent_refl _

variable {W : Type v} [Fintype W]

/-- Evolve a complex ray by a chronological circuit of locally-unitary gates. -/
def evolveCircuit (r : ComplexRay (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℂ W) (hC : C.IsLocallyUnitary) :
    ComplexRay (Circuit.BitBasis W) := by
  classical
  exact evolveUnitary r C.eval (C.eval_mem_unitary hC)

/-- Complex-ray circuit evolution computes on any normalized representative. -/
@[simp]
theorem evolveCircuit_mk (a : ComplexState (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℂ W) (hC : C.IsLocallyUnitary) :
    evolveCircuit (mk a) C hC =
      mk (ComplexState.evolveUnitary a C.eval (C.eval_mem_unitary hC)) := by
  classical
  rfl

/-- The empty complex circuit acts identically on complex rays. -/
@[simp]
theorem evolveCircuit_nil (r : ComplexRay (Circuit.BitBasis W)) :
    evolveCircuit r [] Circuit.OrderedCircuit.isLocallyUnitary_nil = r := by
  classical
  exact evolveUnitary_one r

/-- Chronological append acts on a complex ray first by `C` and then by `D`. -/
theorem evolveCircuit_append (r : ComplexRay (Circuit.BitBasis W))
    (C D : Circuit.OrderedCircuit ℂ W)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    evolveCircuit r (C ++ D) (hC.append hD) =
      evolveCircuit (evolveCircuit r C hC) D hD := by
  classical
  simpa only [evolveCircuit, Circuit.OrderedCircuit.eval_append] using
    (evolveUnitary_comp r C.eval D.eval
      (C.eval_mem_unitary hC) (D.eval_mem_unitary hD)).symm

end ComplexRay

/-! ## Quaternionic right-ray evolution -/

namespace QuaternionRay

variable {I : Type u} [Fintype I]

/-- Evolve a normalized quaternionic right-phase ray by a quaternionic unitary. -/
def evolveUnitary [DecidableEq I] (r : QuaternionRay I)
    (U : Matrix I I ℍ[ℝ]) (hU : U ∈ unitary (Matrix I I ℍ[ℝ])) :
    QuaternionRay I :=
  lift (fun a ↦ mk (QuaternionState.evolveUnitary a U hU))
    (fun _ _ h ↦ mk_eq_mk_iff.mpr (rightPhaseEquivalent_mulVec U h)) r

/-- Quaternionic-ray unitary evolution computes on any normalized representative. -/
@[simp]
theorem evolveUnitary_mk [DecidableEq I] (a : QuaternionState I)
    (U : Matrix I I ℍ[ℝ]) (hU : U ∈ unitary (Matrix I I ℍ[ℝ])) :
    evolveUnitary (mk a) U hU =
      mk (QuaternionState.evolveUnitary a U hU) :=
  rfl

/-- The identity quaternionic unitary acts identically on quaternionic rays. -/
@[simp]
theorem evolveUnitary_one [DecidableEq I] (r : QuaternionRay I) :
    evolveUnitary r 1 (unitary (Matrix I I ℍ[ℝ])).one_mem = r := by
  refine inductionOn r ?_
  intro a
  rw [evolveUnitary_mk, mk_eq_mk_iff]
  have heq : QuaternionState.evolveUnitary a 1
      (unitary (Matrix I I ℍ[ℝ])).one_mem = a :=
    Subtype.ext (Matrix.one_mulVec (a : I → ℍ[ℝ]))
  rw [heq]
  exact Quaternion.rightPhaseEquivalent_refl a

/-- Applying quaternionic unitaries `U` then `V` is the action of `V * U`. -/
theorem evolveUnitary_comp [DecidableEq I] (r : QuaternionRay I)
    (U V : Matrix I I ℍ[ℝ])
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ]))
    (hV : V ∈ unitary (Matrix I I ℍ[ℝ])) :
    evolveUnitary (evolveUnitary r U hU) V hV =
      evolveUnitary r (V * U)
        ((unitary (Matrix I I ℍ[ℝ])).mul_mem hV hU) := by
  refine inductionOn r ?_
  intro a
  simp only [evolveUnitary_mk]
  rw [mk_eq_mk_iff]
  have heq :
      QuaternionState.evolveUnitary (QuaternionState.evolveUnitary a U hU) V hV =
        QuaternionState.evolveUnitary a (V * U)
          ((unitary (Matrix I I ℍ[ℝ])).mul_mem hV hU) :=
    Subtype.ext (Matrix.mulVec_mulVec (a : I → ℍ[ℝ]) V U)
  rw [heq]
  exact Quaternion.rightPhaseEquivalent_refl _

variable {W : Type v} [Fintype W]

/-- Evolve a quaternionic ray by a chronological circuit of locally-unitary gates. -/
def evolveCircuit (r : QuaternionRay (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℍ[ℝ] W) (hC : C.IsLocallyUnitary) :
    QuaternionRay (Circuit.BitBasis W) := by
  classical
  exact evolveUnitary r C.eval (C.eval_mem_unitary hC)

/-- Quaternionic-ray circuit evolution computes on any normalized representative. -/
@[simp]
theorem evolveCircuit_mk (a : QuaternionState (Circuit.BitBasis W))
    (C : Circuit.OrderedCircuit ℍ[ℝ] W) (hC : C.IsLocallyUnitary) :
    evolveCircuit (mk a) C hC =
      mk (QuaternionState.evolveUnitary a C.eval (C.eval_mem_unitary hC)) := by
  classical
  rfl

/-- The empty quaternionic circuit acts identically on quaternionic rays. -/
@[simp]
theorem evolveCircuit_nil (r : QuaternionRay (Circuit.BitBasis W)) :
    evolveCircuit r [] Circuit.OrderedCircuit.isLocallyUnitary_nil = r := by
  classical
  exact evolveUnitary_one r

/-- Chronological append acts on a quaternionic ray first by `C` and then by `D`. -/
theorem evolveCircuit_append (r : QuaternionRay (Circuit.BitBasis W))
    (C D : Circuit.OrderedCircuit ℍ[ℝ] W)
    (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    evolveCircuit r (C ++ D) (hC.append hD) =
      evolveCircuit (evolveCircuit r C hC) D hD := by
  classical
  simpa only [evolveCircuit, Circuit.OrderedCircuit.eval_append] using
    (evolveUnitary_comp r C.eval D.eval
      (C.eval_mem_unitary hC) (D.eval_mem_unitary hD)).symm

end QuaternionRay

end QuaternionicComputing.State
