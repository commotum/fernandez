module

public import QuaternionicComputing.State.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary evolution of finite normalized states

This module proves norm preservation directly from finite matrix algebra.  Its
generic theorem is valid over a possibly noncommutative star semiring: the
star-dot norm of a column is unchanged by a unitary matrix.  Real, complex,
and quaternionic total-weight preservation are then exact specializations of
that identity.

The quaternionic proof deliberately projects the resulting central quaternion
sum to its real coordinate.  It never commutes quaternionic factors: their
order remains `star q * q`, exactly as required by the right-module state
convention used elsewhere in the library.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix Quaternion

namespace QuaternionicComputing.State

/-! ## Generic star-dot preservation -/

/--
A unitary square matrix preserves the finite star-dot norm of every column.

The proof uses the `star U * U = 1` half of unitarity.  No coefficient
commutativity is assumed, so the result applies directly to quaternionic
matrices.
-/
theorem star_dotProduct_mulVec_of_mem_unitary
    {R n : Type*} [Semiring R] [StarRing R] [Fintype n] [DecidableEq n]
    {U : Matrix n n R}
    (hU : U ∈ unitary (Matrix n n R)) (ψ : n → R) :
    star (U *ᵥ ψ) ⬝ᵥ (U *ᵥ ψ) = star ψ ⬝ᵥ ψ := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hstar : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem hU
  rw [hstar, Matrix.one_mulVec]

/-! ## Scalar-specific total weights -/

/-- Complex unitary matrix evolution preserves the exact complex total weight. -/
theorem complexTotalWeight_mulVec_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitary (Matrix n n ℂ)) (ψ : n → ℂ) :
    complexTotalWeight (U *ᵥ ψ) = complexTotalWeight ψ := by
  have h := star_dotProduct_mulVec_of_mem_unitary hU ψ
  have hre := congrArg Complex.re h
  simpa [complexTotalWeight, totalWeight, basisWeight, complexWeight,
    dotProduct, Complex.normSq_apply] using hre

/-- Quaternionic unitary matrix evolution preserves the exact quaternionic total weight. -/
theorem quaternionTotalWeight_mulVec_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℍ[ℝ]}
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) (ψ : n → ℍ[ℝ]) :
    quaternionTotalWeight (U *ᵥ ψ) = quaternionTotalWeight ψ := by
  have h := star_dotProduct_mulVec_of_mem_unitary hU ψ
  let reMap : ℍ[ℝ] →ₗ[ℝ] ℝ :=
    QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)
  have reMap_coe (x : ℝ) : reMap (x : ℍ[ℝ]) = x := rfl
  have hre := congrArg reMap h
  change reMap (∑ i, star ((U *ᵥ ψ) i) * (U *ᵥ ψ) i) =
    reMap (∑ i, star (ψ i) * ψ i) at hre
  rw [map_sum, map_sum] at hre
  simpa [quaternionTotalWeight, totalWeight, basisWeight, quaternionWeight,
    reMap_coe, reMap, QuaternionAlgebra.reₗ_apply, _root_.Quaternion.re_coe,
    _root_.Quaternion.star_mul_self] using hre

/-- Real orthogonal/unitary matrix evolution preserves the exact real total weight. -/
theorem realTotalWeight_mulVec_of_mem_unitary
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℝ}
    (hU : U ∈ unitary (Matrix n n ℝ)) (ψ : n → ℝ) :
    realTotalWeight (U *ᵥ ψ) = realTotalWeight ψ := by
  simpa [realTotalWeight, totalWeight, basisWeight, realWeight, dotProduct]
    using star_dotProduct_mulVec_of_mem_unitary hU ψ

/-! ## Normalized-state evolution -/

namespace RealState

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evolve a normalized real state by a real unitary matrix. -/
def evolveUnitary (ψ : RealState n) (U : Matrix n n ℝ)
    (hU : U ∈ unitary (Matrix n n ℝ)) : RealState n :=
  ⟨U *ᵥ ψ, by
    calc
      realTotalWeight (U *ᵥ (ψ : n → ℝ)) = realTotalWeight ψ :=
        realTotalWeight_mulVec_of_mem_unitary hU ψ
      _ = 1 := ψ.property⟩

@[simp]
theorem evolveUnitary_apply (ψ : RealState n) (U : Matrix n n ℝ)
    (hU : U ∈ unitary (Matrix n n ℝ)) (i : n) :
    evolveUnitary ψ U hU i = (U *ᵥ (ψ : n → ℝ)) i :=
  rfl

/-- The evolved real state retains its defining normalization equation. -/
@[simp]
theorem evolveUnitary_normalization (ψ : RealState n) (U : Matrix n n ℝ)
    (hU : U ∈ unitary (Matrix n n ℝ)) :
    realTotalWeight (evolveUnitary ψ U hU) = 1 :=
  (evolveUnitary ψ U hU).property

end RealState

namespace ComplexState

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evolve a normalized complex state by a complex unitary matrix. -/
def evolveUnitary (ψ : ComplexState n) (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) : ComplexState n :=
  ⟨U *ᵥ ψ, by
    calc
      complexTotalWeight (U *ᵥ (ψ : n → ℂ)) = complexTotalWeight ψ :=
        complexTotalWeight_mulVec_of_mem_unitary hU ψ
      _ = 1 := ψ.property⟩

@[simp]
theorem evolveUnitary_apply (ψ : ComplexState n) (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (i : n) :
    evolveUnitary ψ U hU i = (U *ᵥ (ψ : n → ℂ)) i :=
  rfl

/-- The evolved complex state retains its defining normalization equation. -/
@[simp]
theorem evolveUnitary_normalization (ψ : ComplexState n) (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) :
    complexTotalWeight (evolveUnitary ψ U hU) = 1 :=
  (evolveUnitary ψ U hU).property

end ComplexState

namespace QuaternionState

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evolve a normalized quaternionic state by a quaternionic unitary matrix. -/
def evolveUnitary (ψ : QuaternionState n) (U : Matrix n n ℍ[ℝ])
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) : QuaternionState n :=
  ⟨U *ᵥ ψ, by
    calc
      quaternionTotalWeight (U *ᵥ (ψ : n → ℍ[ℝ])) =
          quaternionTotalWeight ψ :=
        quaternionTotalWeight_mulVec_of_mem_unitary hU ψ
      _ = 1 := ψ.property⟩

@[simp]
theorem evolveUnitary_apply (ψ : QuaternionState n) (U : Matrix n n ℍ[ℝ])
    (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) (i : n) :
    evolveUnitary ψ U hU i = (U *ᵥ (ψ : n → ℍ[ℝ])) i :=
  rfl

/-- The evolved quaternionic state retains its defining normalization equation. -/
@[simp]
theorem evolveUnitary_normalization (ψ : QuaternionState n)
    (U : Matrix n n ℍ[ℝ]) (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) :
    quaternionTotalWeight (evolveUnitary ψ U hU) = 1 :=
  (evolveUnitary ψ U hU).property

end QuaternionState

end QuaternionicComputing.State
