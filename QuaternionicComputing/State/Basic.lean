module

public import QuaternionicComputing.Scalar.Phase
public import Mathlib.Data.Matrix.Mul

/-!
# Finite normalized pure states

This file provides a deliberately small pure-state API.  Normalization is
parameterized by an explicit real-valued scalar weight, rather than by a global
typeclass: a normalized state is a finite column whose total weight is exactly
`1`.

The real, complex, and quaternionic specializations use respectively `x * x`,
`Complex.normSq`, and `Quaternion.normSq`.  Quaternionic columns carry their
physically coherent scalar phase on the right.  The final lemmas show directly
that right phase commutes with arbitrary compatible matrix evolution.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion RightActions

namespace QuaternionicComputing.State

universe u v

variable {ι : Type u} {α : Type v}

/-- The computational-basis weight at coordinate `i`. -/
def basisWeight (weight : α → ℝ) (ψ : ι → α) (i : ι) : ℝ :=
  weight (ψ i)

/-- The total weight of a finite column. -/
def totalWeight [Fintype ι] (weight : α → ℝ) (ψ : ι → α) : ℝ :=
  ∑ i, basisWeight weight ψ i

/-- Pointwise nonnegative scalar weights give nonnegative basis weights. -/
theorem basisWeight_nonneg (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (ψ : ι → α) (i : ι) :
    0 ≤ basisWeight weight ψ i :=
  hweight (ψ i)

/-- A finite sum of pointwise nonnegative scalar weights is nonnegative. -/
theorem totalWeight_nonneg [Fintype ι] (weight : α → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (ψ : ι → α) :
    0 ≤ totalWeight weight ψ := by
  exact Finset.sum_nonneg fun i _ ↦ hweight (ψ i)

/--
A finite pure state normalized with respect to the explicitly supplied scalar
weight.  The equality to `1` is part of the data; it is not inferred from a
global norm instance.
-/
def NormalizedState (ι : Type u) [Fintype ι] (α : Type v)
    (weight : α → ℝ) :=
  { ψ : ι → α // totalWeight weight ψ = 1 }

/-- A normalized state is used as its amplitude column. -/
instance [Fintype ι] {weight : α → ℝ} :
    CoeFun (NormalizedState ι α weight) (fun _ ↦ ι → α) where
  coe ψ := ψ.1

namespace NormalizedState

variable [Fintype ι] {weight : α → ℝ}

/-- The defining normalization equation. -/
@[simp]
theorem totalWeight_eq_one (ψ : NormalizedState ι α weight) :
    totalWeight weight ψ = 1 :=
  ψ.property

/-- Every basis weight of a normalized state is nonnegative when the scalar weight is. -/
theorem basisWeight_nonneg (hweight : ∀ x, 0 ≤ weight x)
    (ψ : NormalizedState ι α weight) (i : ι) :
    0 ≤ QuaternionicComputing.State.basisWeight weight ψ i :=
  hweight (ψ i)

/-- The computational-basis weights of a normalized state sum to one. -/
theorem sum_basisWeight (ψ : NormalizedState ι α weight) :
    (∑ i, QuaternionicComputing.State.basisWeight weight ψ i) = 1 :=
  ψ.property

/-- Two normalized states with the same amplitudes are equal. -/
@[ext]
theorem ext {ψ φ : NormalizedState ι α weight}
    (h : ∀ i, ψ i = φ i) : ψ = φ := by
  apply Subtype.ext
  exact funext h

end NormalizedState

/-! ## Scalar weights and their finite-state specializations -/

/-- Squared real amplitude. -/
def realWeight (x : ℝ) : ℝ :=
  x * x

/-- Squared complex modulus. -/
def complexWeight (z : ℂ) : ℝ :=
  Complex.normSq z

/-- Squared quaternionic modulus. -/
def quaternionWeight (q : ℍ[ℝ]) : ℝ :=
  _root_.Quaternion.normSq q

@[simp] theorem realWeight_apply (x : ℝ) : realWeight x = x * x := rfl
@[simp] theorem complexWeight_apply (z : ℂ) : complexWeight z = Complex.normSq z := rfl
@[simp] theorem quaternionWeight_apply (q : ℍ[ℝ]) :
    quaternionWeight q = _root_.Quaternion.normSq q := rfl

theorem realWeight_nonneg (x : ℝ) : 0 ≤ realWeight x :=
  mul_self_nonneg x

theorem complexWeight_nonneg (z : ℂ) : 0 ≤ complexWeight z :=
  Complex.normSq_nonneg z

theorem quaternionWeight_nonneg (q : ℍ[ℝ]) : 0 ≤ quaternionWeight q :=
  _root_.Quaternion.normSq_nonneg

/-- Computational-basis weight of a real column. -/
def realBasisWeight (ψ : ι → ℝ) (i : ι) : ℝ :=
  basisWeight realWeight ψ i

/-- Computational-basis weight of a complex column. -/
def complexBasisWeight (ψ : ι → ℂ) (i : ι) : ℝ :=
  basisWeight complexWeight ψ i

/-- Computational-basis weight of a quaternionic column. -/
def quaternionBasisWeight (ψ : ι → ℍ[ℝ]) (i : ι) : ℝ :=
  basisWeight quaternionWeight ψ i

/-- Total squared norm of a finite real column. -/
def realTotalWeight [Fintype ι] (ψ : ι → ℝ) : ℝ :=
  totalWeight realWeight ψ

/-- Total squared norm of a finite complex column. -/
def complexTotalWeight [Fintype ι] (ψ : ι → ℂ) : ℝ :=
  totalWeight complexWeight ψ

/-- Total squared norm of a finite quaternionic column. -/
def quaternionTotalWeight [Fintype ι] (ψ : ι → ℍ[ℝ]) : ℝ :=
  totalWeight quaternionWeight ψ

@[simp] theorem realBasisWeight_apply (ψ : ι → ℝ) (i : ι) :
    realBasisWeight ψ i = ψ i * ψ i := rfl

@[simp] theorem complexBasisWeight_apply (ψ : ι → ℂ) (i : ι) :
    complexBasisWeight ψ i = Complex.normSq (ψ i) := rfl

@[simp] theorem quaternionBasisWeight_apply (ψ : ι → ℍ[ℝ]) (i : ι) :
    quaternionBasisWeight ψ i = _root_.Quaternion.normSq (ψ i) := rfl

theorem realBasisWeight_nonneg (ψ : ι → ℝ) (i : ι) :
    0 ≤ realBasisWeight ψ i :=
  realWeight_nonneg (ψ i)

theorem complexBasisWeight_nonneg (ψ : ι → ℂ) (i : ι) :
    0 ≤ complexBasisWeight ψ i :=
  complexWeight_nonneg (ψ i)

theorem quaternionBasisWeight_nonneg (ψ : ι → ℍ[ℝ]) (i : ι) :
    0 ≤ quaternionBasisWeight ψ i :=
  quaternionWeight_nonneg (ψ i)

theorem realTotalWeight_nonneg [Fintype ι] (ψ : ι → ℝ) :
    0 ≤ realTotalWeight ψ :=
  totalWeight_nonneg realWeight realWeight_nonneg ψ

theorem complexTotalWeight_nonneg [Fintype ι] (ψ : ι → ℂ) :
    0 ≤ complexTotalWeight ψ :=
  totalWeight_nonneg complexWeight complexWeight_nonneg ψ

theorem quaternionTotalWeight_nonneg [Fintype ι] (ψ : ι → ℍ[ℝ]) :
    0 ≤ quaternionTotalWeight ψ :=
  totalWeight_nonneg quaternionWeight quaternionWeight_nonneg ψ

/-- A finite normalized real pure state. -/
abbrev RealState (ι : Type u) [Fintype ι] :=
  NormalizedState ι ℝ realWeight

/-- A finite normalized complex pure state. -/
abbrev ComplexState (ι : Type u) [Fintype ι] :=
  NormalizedState ι ℂ complexWeight

/-- A finite normalized quaternionic pure state. -/
abbrev QuaternionState (ι : Type u) [Fintype ι] :=
  NormalizedState ι ℍ[ℝ] quaternionWeight

/-- A normalized two-level real state. -/
abbrev Rebit := RealState Bool

/-- A normalized two-level complex state. -/
abbrev Qubit := ComplexState Bool

/-- A normalized two-level quaternionic state, including the missing equality in paper (44). -/
abbrev Quaterbit := QuaternionState Bool

namespace Rebit

/-- Expanded two-coordinate form of rebit normalization. -/
theorem normalization (ψ : Rebit) :
    realBasisWeight ψ false + realBasisWeight ψ true = 1 := by
  simpa [totalWeight, basisWeight, realBasisWeight, Fintype.univ_bool, add_comm]
    using ψ.property

end Rebit


namespace Qubit

/-- Expanded two-coordinate form of qubit normalization. -/
theorem normalization (ψ : Qubit) :
    complexBasisWeight ψ false + complexBasisWeight ψ true = 1 := by
  simpa [totalWeight, basisWeight, complexBasisWeight, Fintype.univ_bool, add_comm]
    using ψ.property

end Qubit


namespace Quaterbit

/--
Expanded two-coordinate form of quaterbit normalization, repairing the missing
`= 1` in the paper's Equation (44).
-/
theorem normalization (ψ : Quaterbit) :
    quaternionBasisWeight ψ false + quaternionBasisWeight ψ true = 1 := by
  simpa [totalWeight, basisWeight, quaternionBasisWeight, Fintype.univ_bool, add_comm]
    using ψ.property

end Quaterbit

namespace RealState

variable [Fintype ι]

theorem basisWeight_nonneg (ψ : RealState ι) (i : ι) :
    0 ≤ realBasisWeight ψ i :=
  realWeight_nonneg (ψ i)

@[simp]
theorem totalWeight_eq_one (ψ : RealState ι) :
    realTotalWeight ψ = 1 :=
  ψ.property

theorem sum_basisWeight (ψ : RealState ι) :
    (∑ i, realBasisWeight ψ i) = 1 :=
  ψ.property

end RealState

namespace ComplexState

variable [Fintype ι]

theorem basisWeight_nonneg (ψ : ComplexState ι) (i : ι) :
    0 ≤ complexBasisWeight ψ i :=
  complexWeight_nonneg (ψ i)

@[simp]
theorem totalWeight_eq_one (ψ : ComplexState ι) :
    complexTotalWeight ψ = 1 :=
  ψ.property

theorem sum_basisWeight (ψ : ComplexState ι) :
    (∑ i, complexBasisWeight ψ i) = 1 :=
  ψ.property

end ComplexState

namespace QuaternionState

variable [Fintype ι]

theorem basisWeight_nonneg (ψ : QuaternionState ι) (i : ι) :
    0 ≤ quaternionBasisWeight ψ i :=
  quaternionWeight_nonneg (ψ i)

@[simp]
theorem totalWeight_eq_one (ψ : QuaternionState ι) :
    quaternionTotalWeight ψ = 1 :=
  ψ.property

theorem sum_basisWeight (ψ : QuaternionState ι) :
    (∑ i, quaternionBasisWeight ψ i) = 1 :=
  ψ.property

end QuaternionState

/-! ## Quaternionic right phase -/

/-- Right multiplication scales a quaternionic basis weight by the scalar norm square. -/
theorem quaternionBasisWeight_right_smul (ψ : ι → ℍ[ℝ]) (η : ℍ[ℝ]) (i : ι) :
    quaternionBasisWeight (ψ <• η) i =
      quaternionBasisWeight ψ i * _root_.Quaternion.normSq η := by
  simp [quaternionBasisWeight, basisWeight, quaternionWeight, map_mul]

/-- A unit quaternion on the right preserves every computational-basis weight. -/
theorem quaternionBasisWeight_right_smul_of_normSq_eq_one
    (ψ : ι → ℍ[ℝ]) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) (i : ι) :
    quaternionBasisWeight (ψ <• η) i = quaternionBasisWeight ψ i := by
  rw [quaternionBasisWeight_right_smul, hη, mul_one]

/-- Right multiplication scales the total quaternionic weight by the scalar norm square. -/
theorem quaternionTotalWeight_right_smul [Fintype ι]
    (ψ : ι → ℍ[ℝ]) (η : ℍ[ℝ]) :
    quaternionTotalWeight (ψ <• η) =
      quaternionTotalWeight ψ * _root_.Quaternion.normSq η := by
  change (∑ i, quaternionBasisWeight (ψ <• η) i) =
    (∑ i, quaternionBasisWeight ψ i) * _root_.Quaternion.normSq η
  simp_rw [quaternionBasisWeight_right_smul]
  exact (Finset.sum_mul Finset.univ
    (fun i ↦ quaternionBasisWeight ψ i) (_root_.Quaternion.normSq η)).symm

/-- A unit quaternion on the right preserves total weight. -/
theorem quaternionTotalWeight_right_smul_of_normSq_eq_one [Fintype ι]
    (ψ : ι → ℍ[ℝ]) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) :
    quaternionTotalWeight (ψ <• η) = quaternionTotalWeight ψ := by
  rw [quaternionTotalWeight_right_smul, hη, mul_one]

namespace QuaternionState

variable [Fintype ι]

/-- Apply a norm-one quaternionic phase on the physically coherent right side. -/
def rightPhase (ψ : QuaternionState ι) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) : QuaternionState ι :=
  ⟨ψ.1 <• η, by
    calc
      totalWeight quaternionWeight (ψ.1 <• η) =
          totalWeight quaternionWeight ψ.1 :=
        quaternionTotalWeight_right_smul_of_normSq_eq_one ψ.1 η hη
      _ = 1 := ψ.property⟩

@[simp]
theorem rightPhase_apply (ψ : QuaternionState ι) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) (i : ι) :
    rightPhase ψ η hη i = ψ i * η :=
  rfl

@[simp]
theorem rightPhase_basisWeight (ψ : QuaternionState ι) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) (i : ι) :
    quaternionBasisWeight (rightPhase ψ η hη) i =
      quaternionBasisWeight ψ i :=
  by
    change quaternionBasisWeight (ψ.1 <• η) i = quaternionBasisWeight ψ.1 i
    exact quaternionBasisWeight_right_smul_of_normSq_eq_one ψ.1 η hη i

@[simp]
theorem rightPhase_totalWeight (ψ : QuaternionState ι) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) :
    quaternionTotalWeight (rightPhase ψ η hη) = quaternionTotalWeight ψ :=
  by
    change quaternionTotalWeight (ψ.1 <• η) = quaternionTotalWeight ψ.1
    exact quaternionTotalWeight_right_smul_of_normSq_eq_one ψ.1 η hη

/-- A normalized state and its explicit right phase represent the same corrected ray. -/
theorem rightPhaseEquivalent_rightPhase (ψ : QuaternionState ι) (η : ℍ[ℝ])
    (hη : _root_.Quaternion.normSq η = 1) :
    QuaternionicComputing.Quaternion.RightPhaseEquivalent
      (rightPhase ψ η hη : ι → ℍ[ℝ]) ψ :=
  ⟨η, hη, rfl⟩

end QuaternionState

/-- Corrected right-phase rays have identical computational-basis weights. -/
theorem rightPhaseEquivalent_quaternionBasisWeight {x y : ι → ℍ[ℝ]}
    (hxy : QuaternionicComputing.Quaternion.RightPhaseEquivalent x y) (i : ι) :
    quaternionBasisWeight x i = quaternionBasisWeight y i := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact quaternionBasisWeight_right_smul_of_normSq_eq_one y η hη i

/-- Corrected right-phase rays have identical total weight. -/
theorem rightPhaseEquivalent_quaternionTotalWeight [Fintype ι]
    {x y : ι → ℍ[ℝ]}
    (hxy : QuaternionicComputing.Quaternion.RightPhaseEquivalent x y) :
    quaternionTotalWeight x = quaternionTotalWeight y := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact quaternionTotalWeight_right_smul_of_normSq_eq_one y η hη

/-! ## Compatibility of arbitrary quaternionic matrix evolution with right phase -/

/-- Left matrix evolution commutes with every pointwise quaternionic right scalar action. -/
theorem quaternion_mulVec_right_smul {m n : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (ψ : n → ℍ[ℝ]) (η : ℍ[ℝ]) :
    A *ᵥ (ψ <• η) = (A *ᵥ ψ) <• η := by
  simpa only [Matrix.mulVecBilin_apply] using
    ((Matrix.mulVecBilin ℍ[ℝ] ℍ[ℝ]ᵐᵒᵖ) A).map_smul (MulOpposite.op η) ψ

/-- Every compatible quaternionic matrix evolution preserves corrected right-phase rays. -/
theorem rightPhaseEquivalent_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℍ[ℝ]) {x y : n → ℍ[ℝ]}
    (hxy : QuaternionicComputing.Quaternion.RightPhaseEquivalent x y) :
    QuaternionicComputing.Quaternion.RightPhaseEquivalent (A *ᵥ x) (A *ᵥ y) := by
  rcases hxy with ⟨η, hη, rfl⟩
  exact ⟨η, hη, quaternion_mulVec_right_smul A y η⟩

end QuaternionicComputing.State
