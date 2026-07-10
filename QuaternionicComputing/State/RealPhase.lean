module

public import QuaternionicComputing.State.Basic

/-!
# Unit real sign for finite states

Real pure states are identified only up to the two unit real scalars `1` and
`-1`.  This leaf records that relation on arbitrary real columns, its exact
`±1` characterization, its basis- and total-weight invariance, and its
compatibility with arbitrary real matrix evolution.

The scalar is written on the right to match the complex and corrected
quaternionic state-phase APIs.  Over `ℝ` it is central, so this choice carries
no left-versus-right ambiguity.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicComputing.Real

universe u

/-- Two real columns differ by a unit real sign on the right. -/
def SignEquivalent {ι : Type u} (x y : ι → ℝ) : Prop :=
  ∃ s : ℝ, s * s = 1 ∧ x = fun i => y i * s

/-- Real sign equivalence is reflexive. -/
theorem signEquivalent_refl {ι : Type u} (x : ι → ℝ) :
    SignEquivalent x x := by
  refine ⟨1, by norm_num, ?_⟩
  funext i
  simp

/-- Real sign equivalence is symmetric. -/
theorem signEquivalent_symm {ι : Type u} {x y : ι → ℝ}
    (hxy : SignEquivalent x y) : SignEquivalent y x := by
  rcases hxy with ⟨s, hs, rfl⟩
  refine ⟨s, hs, ?_⟩
  funext i
  rw [mul_assoc, hs, mul_one]

/-- Real sign equivalence is transitive. -/
theorem signEquivalent_trans {ι : Type u} {x y z : ι → ℝ}
    (hxy : SignEquivalent x y) (hyz : SignEquivalent y z) :
    SignEquivalent x z := by
  rcases hxy with ⟨s, hs, rfl⟩
  rcases hyz with ⟨t, ht, rfl⟩
  refine ⟨t * s, ?_, ?_⟩
  · calc
      (t * s) * (t * s) = (t * t) * (s * s) := by ring
      _ = 1 := by rw [ht, hs, one_mul]
  · funext i
    ring

/-- Real sign equivalence is an equivalence relation on arbitrary columns. -/
theorem signEquivalent_equivalence {ι : Type u} :
    Equivalence (@SignEquivalent ι) :=
  ⟨signEquivalent_refl, signEquivalent_symm, signEquivalent_trans⟩

/-- A real scalar has square one exactly when it is `1` or `-1`. -/
theorem sign_sq_eq_one_iff {s : ℝ} :
    s * s = 1 ↔ s = 1 ∨ s = -1 := by
  simpa [pow_two] using (sq_eq_one_iff : s ^ 2 = 1 ↔ s = 1 ∨ s = -1)

/-- Real sign equivalence is literal equality or equality with the negated column. -/
theorem signEquivalent_iff_eq_or_eq_neg {ι : Type u} (x y : ι → ℝ) :
    SignEquivalent x y ↔ x = y ∨ x = -y := by
  constructor
  · rintro ⟨s, hs, hxy⟩
    rcases sign_sq_eq_one_iff.mp hs with rfl | rfl
    · exact Or.inl (by simpa using hxy)
    · right
      rw [hxy]
      funext i
      simp
  · intro h
    rcases h with rfl | h
    · exact signEquivalent_refl x
    · refine ⟨-1, by norm_num, ?_⟩
      rw [h]
      funext i
      simp

end QuaternionicComputing.Real

namespace QuaternionicComputing.State

universe u

variable {ι : Type u}

/-- Right multiplication scales a real basis weight by the square of the scalar. -/
theorem realBasisWeight_right_mul (ψ : ι → ℝ) (s : ℝ) (i : ι) :
    realBasisWeight (fun j => ψ j * s) i =
      realBasisWeight ψ i * (s * s) := by
  simp [realBasisWeight, basisWeight, realWeight]
  ring

/-- Multiplication by a unit real sign preserves every basis weight. -/
theorem realBasisWeight_right_mul_of_sq_eq_one
    (ψ : ι → ℝ) (s : ℝ) (hs : s * s = 1) (i : ι) :
    realBasisWeight (fun j => ψ j * s) i = realBasisWeight ψ i := by
  rw [realBasisWeight_right_mul, hs, mul_one]

/-- Right multiplication scales total real weight by the square of the scalar. -/
theorem realTotalWeight_right_mul [Fintype ι] (ψ : ι → ℝ) (s : ℝ) :
    realTotalWeight (fun j => ψ j * s) = realTotalWeight ψ * (s * s) := by
  change (∑ i, realBasisWeight (fun j => ψ j * s) i) =
    (∑ i, realBasisWeight ψ i) * (s * s)
  simp_rw [realBasisWeight_right_mul]
  exact (Finset.sum_mul Finset.univ (fun i => realBasisWeight ψ i) (s * s)).symm

/-- Multiplication by a unit real sign preserves total weight. -/
theorem realTotalWeight_right_mul_of_sq_eq_one [Fintype ι]
    (ψ : ι → ℝ) (s : ℝ) (hs : s * s = 1) :
    realTotalWeight (fun j => ψ j * s) = realTotalWeight ψ := by
  rw [realTotalWeight_right_mul, hs, mul_one]

namespace RealState

variable [Fintype ι]

/-- Apply a unit real sign on the right to a normalized state. -/
def rightSign (ψ : RealState ι) (s : ℝ) (hs : s * s = 1) : RealState ι :=
  ⟨fun i => ψ i * s, by
    exact realTotalWeight_right_mul_of_sq_eq_one ψ s hs |>.trans ψ.property⟩

@[simp]
theorem rightSign_apply (ψ : RealState ι) (s : ℝ) (hs : s * s = 1)
    (i : ι) :
    rightSign ψ s hs i = ψ i * s :=
  rfl

@[simp]
theorem rightSign_basisWeight (ψ : RealState ι) (s : ℝ)
    (hs : s * s = 1) (i : ι) :
    realBasisWeight (rightSign ψ s hs) i = realBasisWeight ψ i :=
  realBasisWeight_right_mul_of_sq_eq_one ψ s hs i

@[simp]
theorem rightSign_totalWeight (ψ : RealState ι) (s : ℝ)
    (hs : s * s = 1) :
    realTotalWeight (rightSign ψ s hs) = realTotalWeight ψ := by
  exact realTotalWeight_right_mul_of_sq_eq_one ψ s hs

/-- A normalized state and its explicit unit sign represent the same real ray. -/
theorem signEquivalent_rightSign (ψ : RealState ι) (s : ℝ)
    (hs : s * s = 1) :
    QuaternionicComputing.Real.SignEquivalent
      (rightSign ψ s hs : ι → ℝ) ψ :=
  ⟨s, hs, rfl⟩

end RealState

/-- Sign-equivalent real columns have identical computational-basis weights. -/
theorem signEquivalent_realBasisWeight {x y : ι → ℝ}
    (hxy : QuaternionicComputing.Real.SignEquivalent x y) (i : ι) :
    realBasisWeight x i = realBasisWeight y i := by
  rcases hxy with ⟨s, hs, rfl⟩
  exact realBasisWeight_right_mul_of_sq_eq_one y s hs i

/-- Sign-equivalent finite real columns have identical total weight. -/
theorem signEquivalent_realTotalWeight [Fintype ι] {x y : ι → ℝ}
    (hxy : QuaternionicComputing.Real.SignEquivalent x y) :
    realTotalWeight x = realTotalWeight y := by
  rcases hxy with ⟨s, hs, rfl⟩
  exact realTotalWeight_right_mul_of_sq_eq_one y s hs

/-- Arbitrary compatible real matrix evolution commutes with right scaling. -/
theorem real_mulVec_right_mul {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (ψ : n → ℝ) (s : ℝ) :
    A *ᵥ (fun j => ψ j * s) = fun i => (A *ᵥ ψ) i * s := by
  ext i
  simp [Matrix.mulVec, dotProduct, mul_assoc, Finset.sum_mul]

/-- Every compatible real matrix evolution preserves real sign equivalence. -/
theorem signEquivalent_real_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) {x y : n → ℝ}
    (hxy : QuaternionicComputing.Real.SignEquivalent x y) :
    QuaternionicComputing.Real.SignEquivalent (A *ᵥ x) (A *ᵥ y) := by
  rcases hxy with ⟨s, hs, rfl⟩
  exact ⟨s, hs, real_mulVec_right_mul A y s⟩

end QuaternionicComputing.State
