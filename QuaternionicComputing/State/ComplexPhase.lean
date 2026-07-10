module

public import QuaternionicComputing.State.Basic

/-!
# Unit complex phase for finite states

Complex pure states are commonly regarded up to multiplication by a unit
complex scalar.  The library continues to use normalized columns as concrete
representatives, but this leaf records the reusable ray-level facts needed by
the paper: unit right phase is an equivalence relation, preserves every basis
weight and total weight, and commutes with arbitrary compatible complex matrix
evolution.

The scalar side is chosen on the right to parallel the corrected quaternionic
API.  Over the commutative complex field this agrees with the usual left-phase
convention.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicComputing.Complex

universe u

/-- Two complex columns differ by a unit scalar on the right. -/
def RightPhaseEquivalent {ι : Type u} (x y : ι → ℂ) : Prop :=
  ∃ η : ℂ, _root_.Complex.normSq η = 1 ∧ x = fun i => y i * η

/-- Right-phase equivalence is reflexive. -/
theorem rightPhaseEquivalent_refl {ι : Type u} (x : ι → ℂ) :
    RightPhaseEquivalent x x := by
  refine ⟨1, by simp, ?_⟩
  funext i
  simp

/-- Right-phase equivalence is symmetric. -/
theorem rightPhaseEquivalent_symm {ι : Type u} {x y : ι → ℂ}
    (hxy : RightPhaseEquivalent x y) : RightPhaseEquivalent y x := by
  rcases hxy with ⟨η, hη, rfl⟩
  refine ⟨star η, by simpa using hη, ?_⟩
  funext i
  change y i = (y i * η) * star η
  rw [mul_assoc]
  change y i = y i * (η * (starRingEnd ℂ) η)
  rw [_root_.Complex.mul_conj, hη]
  simp

/-- Right-phase equivalence is transitive. -/
theorem rightPhaseEquivalent_trans {ι : Type u} {x y z : ι → ℂ}
    (hxy : RightPhaseEquivalent x y) (hyz : RightPhaseEquivalent y z) :
    RightPhaseEquivalent x z := by
  rcases hxy with ⟨η, hη, rfl⟩
  rcases hyz with ⟨θ, hθ, rfl⟩
  refine ⟨θ * η, by rw [_root_.Complex.normSq_mul, hθ, hη, one_mul], ?_⟩
  funext i
  simp [mul_assoc]

/-- The complex right-phase relation is an equivalence relation. -/
theorem rightPhaseEquivalent_equivalence {ι : Type u} :
    Equivalence (@RightPhaseEquivalent ι) :=
  ⟨rightPhaseEquivalent_refl, rightPhaseEquivalent_symm,
    rightPhaseEquivalent_trans⟩

end QuaternionicComputing.Complex

namespace QuaternionicComputing.State

universe u

variable {ι : Type u}

/-- Right multiplication scales a complex basis weight by the scalar norm square. -/
theorem complexBasisWeight_right_mul (ψ : ι → ℂ) (η : ℂ) (i : ι) :
    complexBasisWeight (fun j => ψ j * η) i =
      complexBasisWeight ψ i * _root_.Complex.normSq η := by
  simp [complexBasisWeight, basisWeight, complexWeight,
    _root_.Complex.normSq_mul]

/-- A unit complex scalar on the right preserves every basis weight. -/
theorem complexBasisWeight_right_mul_of_normSq_eq_one
    (ψ : ι → ℂ) (η : ℂ) (hη : _root_.Complex.normSq η = 1) (i : ι) :
    complexBasisWeight (fun j => ψ j * η) i = complexBasisWeight ψ i := by
  rw [complexBasisWeight_right_mul, hη, mul_one]

/-- Right multiplication scales total complex weight by the scalar norm square. -/
theorem complexTotalWeight_right_mul [Fintype ι] (ψ : ι → ℂ) (η : ℂ) :
    complexTotalWeight (fun j => ψ j * η) =
      complexTotalWeight ψ * _root_.Complex.normSq η := by
  change (∑ i, complexBasisWeight (fun j => ψ j * η) i) =
    (∑ i, complexBasisWeight ψ i) * _root_.Complex.normSq η
  simp_rw [complexBasisWeight_right_mul]
  exact (Finset.sum_mul Finset.univ
    (fun i => complexBasisWeight ψ i) (_root_.Complex.normSq η)).symm

/-- A unit complex scalar on the right preserves total weight. -/
theorem complexTotalWeight_right_mul_of_normSq_eq_one [Fintype ι]
    (ψ : ι → ℂ) (η : ℂ) (hη : _root_.Complex.normSq η = 1) :
    complexTotalWeight (fun j => ψ j * η) = complexTotalWeight ψ := by
  rw [complexTotalWeight_right_mul, hη, mul_one]

namespace ComplexState

variable [Fintype ι]

/-- Apply a unit complex phase on the right to a normalized state. -/
def rightPhase (ψ : ComplexState ι) (η : ℂ)
    (hη : _root_.Complex.normSq η = 1) : ComplexState ι :=
  ⟨fun i => ψ i * η, by
    exact complexTotalWeight_right_mul_of_normSq_eq_one ψ η hη |>.trans
      ψ.property⟩

@[simp]
theorem rightPhase_apply (ψ : ComplexState ι) (η : ℂ)
    (hη : _root_.Complex.normSq η = 1) (i : ι) :
    rightPhase ψ η hη i = ψ i * η :=
  rfl

@[simp]
theorem rightPhase_basisWeight (ψ : ComplexState ι) (η : ℂ)
    (hη : _root_.Complex.normSq η = 1) (i : ι) :
    complexBasisWeight (rightPhase ψ η hη) i =
      complexBasisWeight ψ i :=
  complexBasisWeight_right_mul_of_normSq_eq_one ψ η hη i

/-- A normalized state and its explicit unit phase represent the same complex ray. -/
theorem rightPhaseEquivalent_rightPhase (ψ : ComplexState ι) (η : ℂ)
    (hη : _root_.Complex.normSq η = 1) :
    QuaternionicComputing.Complex.RightPhaseEquivalent
      (rightPhase ψ η hη : ι → ℂ) ψ :=
  ⟨η, hη, rfl⟩

end ComplexState

/-- Complex right-phase-equivalent columns have identical basis weights. -/
theorem rightPhaseEquivalent_complexBasisWeight {x y : ι → ℂ}
    (hxy : QuaternionicComputing.Complex.RightPhaseEquivalent x y) (i : ι) :
    complexBasisWeight x i = complexBasisWeight y i := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact complexBasisWeight_right_mul_of_normSq_eq_one y η hη i

/-- Arbitrary compatible complex matrix evolution commutes with right scaling. -/
theorem complex_mulVec_right_mul {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (ψ : n → ℂ) (η : ℂ) :
    A *ᵥ (fun j => ψ j * η) = fun i => (A *ᵥ ψ) i * η := by
  ext i
  simp [Matrix.mulVec, dotProduct, mul_assoc, Finset.sum_mul]

/-- Every compatible complex matrix evolution preserves complex rays. -/
theorem rightPhaseEquivalent_complex_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) {x y : n → ℂ}
    (hxy : QuaternionicComputing.Complex.RightPhaseEquivalent x y) :
    QuaternionicComputing.Complex.RightPhaseEquivalent (A *ᵥ x) (A *ᵥ y) := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact ⟨η, hη, complex_mulVec_right_mul A y η⟩

end QuaternionicComputing.State
