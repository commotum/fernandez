module

public import QuaternionicComputing.Semantics.OperatorPhase.ComplexReal
public import QuaternionicComputing.Semantics.OperatorPhase.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Certified computational-basis behavior

This leaf separates a raw diagnostic relation from genuine classical
reversible behavior.  A `BasisTransition` merely says that one input column
is a phased basis ket.  In contrast, a `BasisPermutationImplementation`
supplies an explicit permutation and proves the corresponding transition for
every input.  `SameBasisBehavior` is available only after supplying two such
certificates and compares their induced permutations.

The generic certificate is parameterized by an explicit unit-phase predicate.
Real signs, complex phases, and quaternionic phases are then specialized
without identifying their different scalar laws.  Quaternionic input phases
act on the right and output phases act on the left throughout.

This file contains no circuit wrappers or counterexample diagnostics.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Basis kets and raw transition diagnostics -/

/-- The scalar-generic computational-basis ket at `x`. -/
def basisKet {R : Type u} {I : Type v} [Zero R] [One R] [DecidableEq I]
    (x : I) : I → R :=
  Pi.single x 1

@[simp]
theorem basisKet_apply {R : Type u} {I : Type v}
    [Zero R] [One R] [DecidableEq I] (x y : I) :
    basisKet (R := R) x y = if y = x then 1 else 0 := by
  simp [basisKet, Pi.single_apply]

/--
The input column `x` of `U` is a unit-phased basis ket at `y`.

This is intentionally only a raw diagnostic predicate.  On a generic matrix
it may fail for every pair `x,y`, so equality of raw transition relations is
not classical reversible behavior.
-/
def BasisTransition {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
    (unitPhase : R → Prop) (U : Matrix I I R) (x y : I) : Prop :=
  ∃ phase : R, unitPhase phase ∧
    ∀ z, U z x = if z = y then phase else 0

/-- Two matrices have the same raw phased-basis transition relation. -/
def BasisTransitionRelationEq {R : Type u} {I : Type v}
    [Zero R] [DecidableEq I] (unitPhase : R → Prop)
    (U V : Matrix I I R) : Prop :=
  ∀ x y, BasisTransition unitPhase U x y ↔
    BasisTransition unitPhase V x y

namespace BasisTransitionRelationEq

variable {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
variable {unitPhase : R → Prop} {U V T : Matrix I I R}

@[refl]
theorem refl (U : Matrix I I R) : BasisTransitionRelationEq unitPhase U U :=
  fun _ _ ↦ Iff.rfl

@[symm]
theorem symm (h : BasisTransitionRelationEq unitPhase U V) :
    BasisTransitionRelationEq unitPhase V U :=
  fun x y ↦ (h x y).symm

@[trans]
theorem trans (hUV : BasisTransitionRelationEq unitPhase U V)
    (hVT : BasisTransitionRelationEq unitPhase V T) :
    BasisTransitionRelationEq unitPhase U T :=
  fun x y ↦ (hUV x y).trans (hVT x y)

/-- Raw basis-transition equality is an equivalence relation. -/
theorem equivalence :
    Equivalence (BasisTransitionRelationEq unitPhase :
      Matrix I I R → Matrix I I R → Prop) :=
  ⟨refl, symm, trans⟩

/-- Exact matrix equality preserves the raw transition diagnostic. -/
theorem of_exact (h : ExactOperatorEq U V) :
    BasisTransitionRelationEq unitPhase U V := by
  subst V
  exact refl U

end BasisTransitionRelationEq

/--
Matrix-vector action on a basis ket is exactly access to the corresponding
input column, so the entrywise transition diagnostic has this equivalent
action formulation.
-/
theorem basisTransition_iff_mulVec_basisKet
    {R : Type u} {I : Type v} [Fintype I] [DecidableEq I]
    [NonAssocSemiring R] (unitPhase : R → Prop)
    (U : Matrix I I R) (x y : I) :
    BasisTransition unitPhase U x y ↔
      ∃ phase : R, unitPhase phase ∧
        U *ᵥ basisKet (R := R) x =
          fun z ↦ if z = y then phase else 0 := by
  simp only [BasisTransition, basisKet, Matrix.mulVec_single_one]
  constructor
  · rintro ⟨phase, hphase, hentry⟩
    exact ⟨phase, hphase, funext hentry⟩
  · rintro ⟨phase, hphase, hentry⟩
    exact ⟨phase, hphase, funext_iff.mp hentry⟩

/-! ## Certified permutation implementations -/

/--
`U` implements the explicit permutation `p` on computational-basis inputs,
with one coefficient satisfying the supplied unit-phase predicate in every
column and zeros everywhere else.

The permutation is an index of the proposition rather than something inferred
from a possibly vacuous raw transition relation.
-/
structure BasisPermutationImplementation
    {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
    (unitPhase : R → Prop) (U : Matrix I I R)
    (p : Equiv.Perm I) : Prop where
  basisTransition : ∀ x, BasisTransition unitPhase U x (p x)

namespace BasisPermutationImplementation

variable {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
variable {unitPhase : R → Prop} {U V : Matrix I I R}
variable {p q : Equiv.Perm I}

/-- A certified implementation has a raw transition at its designated output. -/
theorem transition (h : BasisPermutationImplementation unitPhase U p)
    (x : I) : BasisTransition unitPhase U x (p x) :=
  h.basisTransition x

/--
Under the defining nonzero consequence of unit phase, a certified matrix has
a phased basis transition at `y` exactly when `y` is its certified output.
-/
theorem basisTransition_iff
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (h : BasisPermutationImplementation unitPhase U p) (x y : I) :
    BasisTransition unitPhase U x y ↔ y = p x := by
  constructor
  · rintro ⟨phase, hphase, hentry⟩
    rcases h.basisTransition x with
      ⟨certifiedPhase, hcertifiedPhase, hcertifiedEntry⟩
    by_contra hy
    have hphaseZero : phase = 0 := by
      calc
        phase = U y x := by
          simpa using (hentry y).symm
        _ = 0 := by
          simpa [hy] using hcertifiedEntry y
    exact hnonzero phase hphase hphaseZero
  · rintro rfl
    exact h.basisTransition x

/-- The certified output is the unique target of any unit-phased basis transition. -/
theorem transition_target_unique
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (h : BasisPermutationImplementation unitPhase U p)
    (htransition : BasisTransition unitPhase U x y) :
    y = p x :=
  (h.basisTransition_iff hnonzero x y).mp htransition

/--
The permutation implemented by a fixed matrix is unique.  The proof uses only
the nonzero consequence of the supplied unit-phase predicate; uniqueness is
not an extra field of the certificate.
-/
theorem permutation_unique
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hp : BasisPermutationImplementation unitPhase U p)
    (hq : BasisPermutationImplementation unitPhase U q) :
    p = q := by
  apply Equiv.ext
  intro x
  exact ((hp.basisTransition_iff hnonzero x (q x)).mp
    (hq.basisTransition x)).symm

/--
Mathlib's `p.permMatrix` sends input `x` to output `p.symm x`; this constructor
records that orientation explicitly.
-/
theorem ofPermMatrix [One R] (hone : unitPhase 1) (p : Equiv.Perm I) :
    BasisPermutationImplementation unitPhase (p.permMatrix R) p.symm := by
  constructor
  intro x
  refine ⟨1, hone, ?_⟩
  intro y
  change (p.toPEquiv.toMatrix : Matrix I I R) y x =
    if y = p.symm x then 1 else 0
  simp [PEquiv.toMatrix_apply, Equiv.eq_symm_apply, eq_comm]

end BasisPermutationImplementation

/-! ## Certified-only equality of classical behavior -/

/--
Two certified implementations have the same classical reversible behavior
when their explicitly certified permutations are equal.

This relation cannot be formed for arbitrary matrices without first supplying
both implementation certificates.
-/
def SameBasisBehavior
    {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
    {unitPhase : R → Prop} {U V : Matrix I I R}
    {p q : Equiv.Perm I}
    (_hU : BasisPermutationImplementation unitPhase U p)
    (_hV : BasisPermutationImplementation unitPhase V q) : Prop :=
  p = q

namespace SameBasisBehavior

variable {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
variable {unitPhase : R → Prop} {U V T : Matrix I I R}
variable {p q r : Equiv.Perm I}
variable {hU : BasisPermutationImplementation unitPhase U p}
variable {hV : BasisPermutationImplementation unitPhase V q}
variable {hT : BasisPermutationImplementation unitPhase T r}

@[refl]
theorem refl (hU : BasisPermutationImplementation unitPhase U p) :
    SameBasisBehavior hU hU :=
  rfl

@[symm]
theorem symm (h : SameBasisBehavior hU hV) :
    SameBasisBehavior hV hU :=
  Eq.symm h

@[trans]
theorem trans (hUV : SameBasisBehavior hU hV)
    (hVT : SameBasisBehavior hV hT) :
    SameBasisBehavior hU hT :=
  Eq.trans hUV hVT

/-- Same certified behavior gives equality of the raw transition diagnostics. -/
theorem basisTransitionRelationEq
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (h : SameBasisBehavior hU hV) :
    BasisTransitionRelationEq unitPhase U V := by
  intro x y
  rw [hU.basisTransition_iff hnonzero,
    hV.basisTransition_iff hnonzero, h]

end SameBasisBehavior

/-- Exact operator equality forces the same permutation on certified implementations. -/
theorem ExactOperatorEq.sameBasisBehavior
    {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
    {unitPhase : R → Prop} {U V : Matrix I I R}
    {p q : Equiv.Perm I}
    (hnonzero : ∀ phase, unitPhase phase → phase ≠ 0)
    (hU : BasisPermutationImplementation unitPhase U p)
    (hV : BasisPermutationImplementation unitPhase V q)
    (h : ExactOperatorEq U V) :
    SameBasisBehavior hU hV := by
  subst V
  exact BasisPermutationImplementation.permutation_unique hnonzero hU hV

/-! ## Scalar phase predicates and aliases -/

/-- A real unit sign. -/
def RealUnitSign (s : ℝ) : Prop :=
  s * s = 1

/-- A complex unit phase. -/
def ComplexUnitPhase (phase : ℂ) : Prop :=
  Complex.normSq phase = 1

/-- A quaternionic unit phase. -/
def QuaternionUnitPhase (phase : ℍ[ℝ]) : Prop :=
  _root_.Quaternion.normSq phase = 1

@[simp] theorem realUnitSign_one : RealUnitSign 1 := by
  norm_num [RealUnitSign]

@[simp] theorem complexUnitPhase_one : ComplexUnitPhase 1 := by
  simp [ComplexUnitPhase]

@[simp] theorem quaternionUnitPhase_one : QuaternionUnitPhase 1 := by
  simp [QuaternionUnitPhase]

theorem realUnitSign_ne_zero {s : ℝ} (hs : RealUnitSign s) : s ≠ 0 := by
  intro hzero
  subst s
  norm_num [RealUnitSign] at hs

theorem complexUnitPhase_ne_zero {phase : ℂ}
    (hphase : ComplexUnitPhase phase) : phase ≠ 0 := by
  intro hzero
  subst phase
  norm_num [ComplexUnitPhase] at hphase

theorem quaternionUnitPhase_ne_zero {phase : ℍ[ℝ]}
    (hphase : QuaternionUnitPhase phase) : phase ≠ 0 := by
  intro hzero
  subst phase
  norm_num [QuaternionUnitPhase] at hphase

/-- Real specialization of a certified basis permutation implementation. -/
abbrev RealBasisPermutationImplementation {I : Type v} [DecidableEq I]
    (U : Matrix I I ℝ) (p : Equiv.Perm I) :=
  BasisPermutationImplementation RealUnitSign U p

/-- Complex specialization of a certified basis permutation implementation. -/
abbrev ComplexBasisPermutationImplementation {I : Type v} [DecidableEq I]
    (U : Matrix I I ℂ) (p : Equiv.Perm I) :=
  BasisPermutationImplementation ComplexUnitPhase U p

/-- Quaternionic specialization of a certified basis permutation implementation. -/
abbrev QuaternionBasisPermutationImplementation {I : Type v} [DecidableEq I]
    (U : Matrix I I ℍ[ℝ]) (p : Equiv.Perm I) :=
  BasisPermutationImplementation QuaternionUnitPhase U p

/-! ## Measurement determination of the certified permutation -/

namespace BasisMeasurementEq

variable {R : Type u} {I : Type v} [Zero R] [DecidableEq I]
variable {unitPhase : R → Prop} {weight : R → ℝ}
variable {U V : Matrix I I R} {p q : Equiv.Perm I}

/--
On certified permutation implementations, basis-measurement equality forces
the same permutation whenever zero has weight zero and every unit phase has
weight one.
-/
theorem sameBasisBehavior
    (hzero : weight 0 = 0)
    (hunit : ∀ phase, unitPhase phase → weight phase = 1)
    (hU : BasisPermutationImplementation unitPhase U p)
    (hV : BasisPermutationImplementation unitPhase V q)
    (hmeasure : BasisMeasurementEq weight U V) :
    SameBasisBehavior hU hV := by
  apply Equiv.ext
  intro x
  by_contra hpq
  rcases hU.basisTransition x with ⟨a, ha, hUa⟩
  rcases hV.basisTransition x with ⟨b, hb, hVb⟩
  have hUone : weight (U (p x) x) = 1 := by
    rw [hUa (p x), if_pos rfl, hunit a ha]
  have hVzero : weight (V (p x) x) = 0 := by
    rw [hVb (p x), if_neg hpq, hzero]
  have honezero : (1 : ℝ) = 0 :=
    hUone.symm.trans ((hmeasure x (p x)).trans hVzero)
  exact one_ne_zero honezero

end BasisMeasurementEq

/-! ## Same certified behavior produces the scalar phase relations -/

namespace SameBasisBehavior

variable {I : Type v} [DecidableEq I]

/-- Equal certified real permutations differ only by input-column signs. -/
theorem realInputBasisSignEq
    {U V : Matrix I I ℝ} {p q : Equiv.Perm I}
    {hU : RealBasisPermutationImplementation U p}
    {hV : RealBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    RealInputBasisSignEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun x ↦ a x * b x, ?_, ?_⟩
  · intro x
    calc
      (a x * b x) * (a x * b x) =
          (a x * a x) * (b x * b x) := by ring
      _ = 1 := by rw [ha x, hb x, one_mul]
  · intro y x
    rw [hUa x y, hVb x y]
    by_cases hy : y = p x
    · simp only [if_pos hy]
      rw [← mul_assoc, ha x, one_mul]
    · simp [hy]

/-- Equal certified complex permutations differ only by input-column phases. -/
theorem complexInputBasisPhaseEq
    {U V : Matrix I I ℂ} {p q : Equiv.Perm I}
    {hU : ComplexBasisPermutationImplementation U p}
    {hV : ComplexBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    ComplexInputBasisPhaseEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun x ↦ star (a x) * b x, ?_, ?_⟩
  · intro x
    rw [Complex.normSq_mul]
    change Complex.normSq ((starRingEnd ℂ) (a x)) *
      Complex.normSq (b x) = 1
    rw [Complex.normSq_conj]
    rw [show Complex.normSq (a x) = 1 by
      simpa [ComplexUnitPhase] using ha x]
    rw [show Complex.normSq (b x) = 1 by
      simpa [ComplexUnitPhase] using hb x]
    norm_num
  · intro y x
    rw [hUa x y, hVb x y]
    by_cases hy : y = p x
    · simp only [if_pos hy]
      rw [← mul_assoc]
      change b x = (a x * (starRingEnd ℂ) (a x)) * b x
      rw [Complex.mul_conj, ha x]
      simp
    · simp [hy]

/--
Equal certified quaternionic permutations differ only by input-column phases
on the right.  The witness is `star a * b`, in that order.
-/
theorem quaternionInputRightPhaseEq
    {U V : Matrix I I ℍ[ℝ]} {p q : Equiv.Perm I}
    {hU : QuaternionBasisPermutationImplementation U p}
    {hV : QuaternionBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    QuaternionInputRightPhaseEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun x ↦ star (a x) * b x, ?_, ?_⟩
  · intro x
    rw [map_mul, _root_.Quaternion.normSq_star]
    rw [show _root_.Quaternion.normSq (a x) = 1 by
      simpa [QuaternionUnitPhase] using ha x]
    rw [show _root_.Quaternion.normSq (b x) = 1 by
      simpa [QuaternionUnitPhase] using hb x]
    norm_num
  · intro y x
    rw [hUa x y, hVb x y]
    by_cases hy : y = p x
    · simp only [if_pos hy]
      rw [← mul_assoc, _root_.Quaternion.self_mul_star, ha x]
      simp
    · simp [hy]

/-- Equal certified real permutations differ only by output-row signs. -/
theorem realOutputBasisSignEq
    {U V : Matrix I I ℝ} {p q : Equiv.Perm I}
    {hU : RealBasisPermutationImplementation U p}
    {hV : RealBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    RealOutputBasisSignEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun y ↦ b (p.symm y) * a (p.symm y), ?_, ?_⟩
  · intro y
    calc
      (b (p.symm y) * a (p.symm y)) *
          (b (p.symm y) * a (p.symm y)) =
          (b (p.symm y) * b (p.symm y)) *
            (a (p.symm y) * a (p.symm y)) := by ring
      _ = 1 := by rw [hb, ha, one_mul]
  · intro y x
    by_cases hy : y = p x
    · subst y
      rw [hUa x (p x), hVb x (p x)]
      simp only [Equiv.symm_apply_apply, if_true]
      rw [mul_assoc, ha x, mul_one]
    · rw [hUa x y, hVb x y]
      simp [hy]

/-- Equal certified complex permutations differ only by output-row phases. -/
theorem complexOutputBasisPhaseEq
    {U V : Matrix I I ℂ} {p q : Equiv.Perm I}
    {hU : ComplexBasisPermutationImplementation U p}
    {hV : ComplexBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    ComplexOutputBasisPhaseEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun y ↦ b (p.symm y) * star (a (p.symm y)), ?_, ?_⟩
  · intro y
    rw [Complex.normSq_mul]
    change Complex.normSq (b (p.symm y)) *
      Complex.normSq ((starRingEnd ℂ) (a (p.symm y))) = 1
    rw [Complex.normSq_conj]
    rw [show Complex.normSq (b (p.symm y)) = 1 by
      simpa [ComplexUnitPhase] using hb (p.symm y)]
    rw [show Complex.normSq (a (p.symm y)) = 1 by
      simpa [ComplexUnitPhase] using ha (p.symm y)]
    norm_num
  · intro y x
    by_cases hy : y = p x
    · subst y
      rw [hUa x (p x), hVb x (p x)]
      simp only [Equiv.symm_apply_apply, if_true]
      rw [mul_assoc]
      change b x = b x * ((starRingEnd ℂ) (a x) * a x)
      rw [mul_comm ((starRingEnd ℂ) (a x)) (a x),
        Complex.mul_conj, ha x]
      simp
    · rw [hUa x y, hVb x y]
      simp [hy]

/--
Equal certified quaternionic permutations differ only by output-row phases on
the left.  The witness is `b * star a`, in that order.
-/
theorem quaternionOutputLeftPhaseEq
    {U V : Matrix I I ℍ[ℝ]} {p q : Equiv.Perm I}
    {hU : QuaternionBasisPermutationImplementation U p}
    {hV : QuaternionBasisPermutationImplementation V q}
    (h : SameBasisBehavior hU hV) :
    QuaternionOutputLeftPhaseEq U V := by
  change p = q at h
  subst q
  choose a ha hUa using hU.basisTransition
  choose b hb hVb using hV.basisTransition
  refine ⟨fun y ↦ b (p.symm y) * star (a (p.symm y)), ?_, ?_⟩
  · intro y
    rw [map_mul, _root_.Quaternion.normSq_star]
    rw [show _root_.Quaternion.normSq (b (p.symm y)) = 1 by
      simpa [QuaternionUnitPhase] using hb (p.symm y)]
    rw [show _root_.Quaternion.normSq (a (p.symm y)) = 1 by
      simpa [QuaternionUnitPhase] using ha (p.symm y)]
    norm_num
  · intro y x
    by_cases hy : y = p x
    · subst y
      rw [hUa x (p x), hVb x (p x)]
      simp only [Equiv.symm_apply_apply, if_true]
      rw [mul_assoc, _root_.Quaternion.star_mul_self, ha x]
      simp
    · rw [hUa x y, hVb x y]
      simp [hy]

end SameBasisBehavior

/-! ## Certified unitary operator bundles -/

/-- A square unitary operator together with certified classical basis behavior. -/
structure BasisClassicalUnitaryOperator
    (R : Type u) (I : Type v) [Semiring R] [StarRing R]
    [Fintype I] [DecidableEq I] (unitPhase : R → Prop) where
  matrix : Matrix I I R
  mem_unitary : matrix ∈ unitary (Matrix I I R)
  permutation : Equiv.Perm I
  implementation :
    BasisPermutationImplementation unitPhase matrix permutation

namespace BasisClassicalUnitaryOperator

variable {R : Type u} {I : Type v} [Semiring R] [StarRing R]
variable [Fintype I] [DecidableEq I] {unitPhase : R → Prop}

/-- A permutation matrix, bundled with its unitarity and basis-action certificates. -/
def ofPermMatrix (hone : unitPhase 1) (p : Equiv.Perm I) :
    BasisClassicalUnitaryOperator R I unitPhase where
  matrix := p.permMatrix R
  mem_unitary := by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix]
    constructor <;> rw [← Matrix.permMatrix_mul] <;> simp
  permutation := p.symm
  implementation := BasisPermutationImplementation.ofPermMatrix hone p

end BasisClassicalUnitaryOperator

/-- Real certified basis-classical unitary operators. -/
abbrev RealBasisClassicalUnitaryOperator
    (I : Type v) [Fintype I] [DecidableEq I] :=
  BasisClassicalUnitaryOperator ℝ I RealUnitSign

/-- Complex certified basis-classical unitary operators. -/
abbrev ComplexBasisClassicalUnitaryOperator
    (I : Type v) [Fintype I] [DecidableEq I] :=
  BasisClassicalUnitaryOperator ℂ I ComplexUnitPhase

/-- Quaternionic certified basis-classical unitary operators. -/
abbrev QuaternionBasisClassicalUnitaryOperator
    (I : Type v) [Fintype I] [DecidableEq I] :=
  BasisClassicalUnitaryOperator ℍ[ℝ] I QuaternionUnitPhase

end QuaternionicComputing.Semantics
