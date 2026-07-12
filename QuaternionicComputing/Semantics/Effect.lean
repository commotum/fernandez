module

public import QuaternionicComputing.Semantics.Density
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Finite real and complex physical effects

This leaf defines genuine finite-dimensional quantum effects as matrices in
the Loewner interval `0 ≤ E ≤ 1`.  It then defines the Born trace pairing
with a density matrix and proves, rather than assumes, that its real value lies
in `[0,1]`.

The implementation is uniform over `RCLike` scalars, with explicit real and
complex aliases.  Rank-one effects are constructed from normalized Euclidean
vectors, and computational-basis effects recover the existing real and
complex basis weights on pure densities.

This module contains no effect-separation theorem, channel relation,
arbitrary trace-test interface, or quaternionic density semantics.  The
heavier rank-one polarization argument belongs in `EffectSeparation`.
-/

@[expose] public noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Physical effects and their invariants -/

/--
A finite physical effect over an `RCLike` scalar field.

The two fields are exactly the Loewner interval conditions `0 ≤ E` and
`E ≤ 1`; arbitrary matrices do not inhabit this structure.
-/
structure Effect (𝕜 : Type u) (I : Type v) [RCLike 𝕜]
    [Fintype I] [DecidableEq I] where
  /-- The underlying square matrix. -/
  matrix : Matrix I I 𝕜
  /-- Positivity in the Loewner order. -/
  nonneg : 0 ≤ matrix
  /-- The effect is bounded above by the identity. -/
  le_one : matrix ≤ 1

/-- A finite real physical effect. -/
abbrev RealEffect (I : Type v) [Fintype I] [DecidableEq I] :=
  Effect ℝ I

/-- A finite complex physical effect. -/
abbrev ComplexEffect (I : Type v) [Fintype I] [DecidableEq I] :=
  Effect ℂ I

namespace Effect

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜]
variable [Fintype I] [DecidableEq I]

/-- Use a physical effect as its underlying matrix. -/
instance : Coe (Effect 𝕜 I) (Matrix I I 𝕜) where
  coe E := E.matrix

/-- Coercion exposes the stored matrix definitionally. -/
@[simp]
theorem coe_matrix (E : Effect 𝕜 I) :
    ((E : Matrix I I 𝕜)) = E.matrix :=
  rfl

/-- Two effects are equal when their underlying matrices are equal. -/
theorem ext_matrix {E F : Effect 𝕜 I}
    (h : (E : Matrix I I 𝕜) = (F : Matrix I I 𝕜)) : E = F := by
  cases E
  cases F
  simpa using h

/-- Physical effects are extensional in their matrix entries. -/
@[ext]
theorem ext {E F : Effect 𝕜 I}
    (h : ∀ i j, (E : Matrix I I 𝕜) i j = (F : Matrix I I 𝕜) i j) :
    E = F :=
  ext_matrix (Matrix.ext fun i j ↦ h i j)

/-- Equality of effects is equivalent to entrywise matrix equality. -/
theorem eq_iff_entries {E F : Effect 𝕜 I} :
    E = F ↔
      ∀ i j, (E : Matrix I I 𝕜) i j = (F : Matrix I I 𝕜) i j := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · exact ext

/-- Every physical effect is positive semidefinite. -/
theorem posSemidef (E : Effect 𝕜 I) :
    (E : Matrix I I 𝕜).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp E.nonneg

/-- Every physical effect is Hermitian. -/
theorem isHermitian (E : Effect 𝕜 I) :
    (E : Matrix I I 𝕜).IsHermitian :=
  E.posSemidef.isHermitian

/-- The complement `1 - E` of a physical effect is positive semidefinite. -/
theorem complement_posSemidef (E : Effect 𝕜 I) :
    (1 - (E : Matrix I I 𝕜)).PosSemidef :=
  Matrix.le_iff.mp E.le_one

/-! ## Zero, identity, and complement effects -/

/-- The effect which never occurs. -/
def zero : Effect 𝕜 I where
  matrix := 0
  nonneg := le_rfl
  le_one := by simp

/-- The effect which always occurs. -/
def one : Effect 𝕜 I where
  matrix := 1
  nonneg := by simp
  le_one := le_rfl

/-- The underlying matrix of the zero effect is zero. -/
@[simp]
theorem zero_coe : ((zero : Effect 𝕜 I) : Matrix I I 𝕜) = 0 :=
  rfl

/-- The underlying matrix of the identity effect is the identity. -/
@[simp]
theorem one_coe : ((one : Effect 𝕜 I) : Matrix I I 𝕜) = 1 :=
  rfl

/-- The complementary physical effect `1 - E`. -/
def complement (E : Effect 𝕜 I) : Effect 𝕜 I where
  matrix := 1 - (E : Matrix I I 𝕜)
  nonneg := sub_nonneg.mpr E.le_one
  le_one := by
    simpa only [sub_le_self_iff] using E.nonneg

/-- Complementation computes as matrix subtraction from the identity. -/
@[simp]
theorem complement_coe (E : Effect 𝕜 I) :
    ((complement E : Effect 𝕜 I) : Matrix I I 𝕜) =
      1 - (E : Matrix I I 𝕜) :=
  rfl

/-- Taking the complement twice returns the original effect. -/
@[simp]
theorem complement_complement (E : Effect 𝕜 I) :
    complement (complement E) = E := by
  apply ext_matrix
  simp

/-- The complement of the zero effect is the identity effect. -/
@[simp]
theorem complement_zero : complement (zero : Effect 𝕜 I) = one := by
  apply ext_matrix
  simp

/-- The complement of the identity effect is the zero effect. -/
@[simp]
theorem complement_one : complement (one : Effect 𝕜 I) = zero := by
  apply ext_matrix
  simp

/-! ## Normalized rank-one and computational-basis effects -/

/-- The matrix of the rank-one projector onto a Euclidean vector. -/
def rankOneProjector (x : EuclideanSpace 𝕜 I) : Matrix I I 𝕜 :=
  Matrix.toEuclideanLin.symm (InnerProductSpace.rankOne 𝕜 x x)

/-- A rank-one projector is the expected ket--bra matrix. -/
theorem rankOneProjector_eq_vecMulVec (x : EuclideanSpace 𝕜 I) :
    rankOneProjector x = Matrix.vecMulVec x.ofLp (star x.ofLp) := by
  rw [rankOneProjector, InnerProductSpace.symm_toEuclideanLin_rankOne]

/-- Entries of a rank-one projector have ket--bra multiplication order. -/
@[simp]
theorem rankOneProjector_apply (x : EuclideanSpace 𝕜 I) (i j : I) :
    rankOneProjector x i j = x i * star (x j) := by
  rw [rankOneProjector_eq_vecMulVec]
  rfl

/-- The projector onto a normalized Euclidean vector is positive semidefinite. -/
theorem rankOneProjector_posSemidef (x : EuclideanSpace 𝕜 I)
    (hx : ‖x‖ = 1) :
    (rankOneProjector x).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  simp only [rankOneProjector, LinearEquiv.apply_symm_apply]
  exact (InnerProductSpace.isSymmetricProjection_rankOne_self hx).isPositive

/-- The projector onto a normalized Euclidean vector is bounded by the identity. -/
theorem rankOneProjector_le_one (x : EuclideanSpace 𝕜 I)
    (hx : ‖x‖ = 1) :
    rankOneProjector x ≤ (1 : Matrix I I 𝕜) := by
  rw [Matrix.le_iff]
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  simp only [map_sub, Matrix.toLpLin_one, rankOneProjector,
    LinearEquiv.apply_symm_apply]
  have hp := InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := 𝕜) hx
  have hq :
      (LinearMap.id : EuclideanSpace 𝕜 I →ₗ[𝕜] EuclideanSpace 𝕜 I).IsSymmetricProjection :=
    { isIdempotentElem := IsIdempotentElem.one
      isSymmetric := LinearMap.IsSymmetric.id }
  exact (hp.sub_of_range_le_range hq (by simp)).isPositive

/-- A normalized rank-one projector bundled as a physical effect. -/
def projector (x : EuclideanSpace 𝕜 I) (hx : ‖x‖ = 1) : Effect 𝕜 I where
  matrix := rankOneProjector x
  nonneg := (rankOneProjector_posSemidef x hx).nonneg
  le_one := rankOneProjector_le_one x hx

/-- The underlying matrix of a normalized projector effect. -/
@[simp]
theorem projector_coe (x : EuclideanSpace 𝕜 I) (hx : ‖x‖ = 1) :
    ((projector x hx : Effect 𝕜 I) : Matrix I I 𝕜) =
      rankOneProjector x :=
  rfl

/-- The computational-basis projector at `x`, bundled as a physical effect. -/
def basis (x : I) : Effect 𝕜 I :=
  projector (EuclideanSpace.basisFun I 𝕜 x)
    (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun I 𝕜) x)

/-- A basis effect has a single `1` at `(x,x)` and zero elsewhere. -/
@[simp]
theorem basis_apply (x i j : I) :
    ((basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) i j =
      if i = x ∧ j = x then 1 else 0 := by
  by_cases hi : i = x <;> by_cases hj : j = x <;>
    simp [basis, projector, rankOneProjector_apply,
      EuclideanSpace.basisFun_apply, hi, hj]

/-- The matrix of a basis effect is the corresponding matrix unit. -/
theorem basis_coe_eq_single (x : I) :
    ((basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) =
      Matrix.single x x 1 := by
  ext i j
  rw [basis_apply, Matrix.single_apply]
  by_cases h : i = x ∧ j = x
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨hxi, hxj⟩
    exact h ⟨hxi.symm, hxj.symm⟩

/-- The basis effect and basis density at the same index have the same matrix. -/
theorem basis_coe_eq_density_basis (x : I) :
    ((basis (𝕜 := 𝕜) x : Effect 𝕜 I) : Matrix I I 𝕜) =
      ((DensityMatrix.basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) :
        Matrix I I 𝕜) := by
  ext i j
  rw [basis_apply, DensityMatrix.basis_apply]

/-! ## Born values and probability bounds -/

omit [DecidableEq I] in
/--
The trace pairing of two positive-semidefinite matrices is nonnegative.

The product itself need not be Hermitian.  The proof factors the second
matrix, rotates the trace cyclically, and takes the trace of a positive
conjugation sandwich.
-/
theorem trace_mul_nonneg_of_posSemidef
    {A B : Matrix I I 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  classical
  obtain ⟨X, hX⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hX, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simpa only [Matrix.star_eq_conjTranspose] using
    (hA.mul_mul_conjTranspose_same X).trace_nonneg

/-- The scalar trace pairing underlying the Born value. -/
def bornScalar (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) : 𝕜 :=
  Matrix.trace ((E : Matrix I I 𝕜) * (rho : Matrix I I 𝕜))

/-- The real Born value of a physical effect on a density matrix. -/
def bornValue (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) : ℝ :=
  RCLike.re (bornScalar E rho)

/-- The Born trace pairing is nonnegative in the `RCLike` order. -/
theorem bornScalar_nonneg (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    0 ≤ bornScalar E rho :=
  trace_mul_nonneg_of_posSemidef E.posSemidef rho.posSemidef

/-- The Born trace pairing is real. -/
theorem bornScalar_im_eq_zero (E : Effect 𝕜 I)
    (rho : DensityMatrix 𝕜 I) :
    RCLike.im (bornScalar E rho) = 0 :=
  (RCLike.nonneg_iff.mp (bornScalar_nonneg E rho)).2

/-- Coercing the real Born value back to the scalar recovers the trace pairing. -/
theorem ofReal_bornValue (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    (bornValue E rho : 𝕜) = bornScalar E rho := by
  apply RCLike.ext
  · simp [bornValue]
  · simp [bornScalar_im_eq_zero]

/-- Every physical Born value is nonnegative. -/
theorem bornValue_nonneg (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    0 ≤ bornValue E rho :=
  (RCLike.nonneg_iff.mp (bornScalar_nonneg E rho)).1

/-- The scalar Born pairing is bounded above by one. -/
theorem bornScalar_le_one (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    bornScalar E rho ≤ 1 := by
  have h := trace_mul_nonneg_of_posSemidef E.complement_posSemidef rho.posSemidef
  simpa [bornScalar, Matrix.sub_mul, rho.trace_one] using h

/-- Every physical Born value is at most one. -/
theorem bornValue_le_one (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    bornValue E rho ≤ 1 := by
  have h := bornScalar_le_one E rho
  have hre := (RCLike.nonneg_iff.mp (sub_nonneg.mpr h)).1
  simpa [bornValue] using hre

/-- Every physical Born value lies in the closed unit interval. -/
theorem bornValue_mem_Icc (E : Effect 𝕜 I) (rho : DensityMatrix 𝕜 I) :
    bornValue E rho ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨bornValue_nonneg E rho, bornValue_le_one E rho⟩

/-! ## Zero, identity, and complement laws -/

/-- The zero effect has scalar Born pairing zero. -/
@[simp]
theorem bornScalar_zero (rho : DensityMatrix 𝕜 I) :
    bornScalar (zero : Effect 𝕜 I) rho = 0 := by
  simp [bornScalar]

/-- The zero effect has Born value zero. -/
@[simp]
theorem bornValue_zero (rho : DensityMatrix 𝕜 I) :
    bornValue (zero : Effect 𝕜 I) rho = 0 := by
  simp [bornValue]

/-- The identity effect has scalar Born pairing one. -/
@[simp]
theorem bornScalar_one (rho : DensityMatrix 𝕜 I) :
    bornScalar (one : Effect 𝕜 I) rho = 1 := by
  simp [bornScalar, rho.trace_one]

/-- The identity effect has Born value one. -/
@[simp]
theorem bornValue_one (rho : DensityMatrix 𝕜 I) :
    bornValue (one : Effect 𝕜 I) rho = 1 := by
  simp [bornValue]

/-- Complementation subtracts the scalar Born pairing from one. -/
theorem bornScalar_complement (E : Effect 𝕜 I)
    (rho : DensityMatrix 𝕜 I) :
    bornScalar (complement E) rho = 1 - bornScalar E rho := by
  simp [bornScalar, Matrix.sub_mul, rho.trace_one]

/-- Complementation subtracts the real Born value from one. -/
theorem bornValue_complement (E : Effect 𝕜 I)
    (rho : DensityMatrix 𝕜 I) :
    bornValue (complement E) rho = 1 - bornValue E rho := by
  simp [bornValue, bornScalar_complement]

/-! ## Computational-basis and pure-state formulas -/

/-- A basis effect reads the corresponding diagonal matrix entry. -/
theorem bornScalar_basis (x : I) (rho : DensityMatrix 𝕜 I) :
    bornScalar (basis (𝕜 := 𝕜) x) rho =
      (rho : Matrix I I 𝕜) x x := by
  rw [bornScalar, basis_coe_eq_single, Matrix.trace_single_mul]
  simp

/-- The real Born value of a basis effect is the real part of the diagonal entry. -/
theorem bornValue_basis (x : I) (rho : DensityMatrix 𝕜 I) :
    bornValue (basis (𝕜 := 𝕜) x) rho =
      RCLike.re ((rho : Matrix I I 𝕜) x x) := by
  rw [bornValue, bornScalar_basis]

/-- A basis effect on a pure density returns the ket's squared modulus. -/
theorem bornValue_basis_pure (x : I) (psi : I → 𝕜)
    (hpsi : star psi ⬝ᵥ psi = 1) :
    bornValue (basis (𝕜 := 𝕜) x) (DensityMatrix.pure psi hpsi) =
      RCLike.normSq (psi x) := by
  rw [bornValue_basis]
  simp only [DensityMatrix.pure_apply, RCLike.star_def]
  rw [RCLike.mul_conj, RCLike.normSq_eq_def']
  simp

/-- Basis effects distinguish basis densities by the Kronecker delta. -/
theorem bornValue_basis_basis (x y : I) :
    bornValue (basis (𝕜 := 𝕜) y) (DensityMatrix.basis (𝕜 := 𝕜) x) =
      if y = x then 1 else 0 := by
  rw [bornValue_basis]
  by_cases h : y = x
  · subst y
    simp
  · simp [DensityMatrix.basis_apply, h]

end Effect

/-! ## Existing normalized-state compatibility -/

namespace RealEffect

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Real basis effects recover the existing real computational-basis weight. -/
theorem bornValue_basis_ofState (x : I) (psi : State.RealState I) :
    Effect.bornValue (Effect.basis (𝕜 := ℝ) x)
        (RealDensityMatrix.ofState psi) =
      State.realBasisWeight psi x := by
  simpa [RealDensityMatrix.ofState, State.realBasisWeight,
    State.basisWeight, State.realWeight, RCLike.normSq_to_real] using
    Effect.bornValue_basis_pure (𝕜 := ℝ) x (psi : I → ℝ) (by
      simpa [State.realTotalWeight, State.totalWeight, State.basisWeight,
        State.realWeight, dotProduct] using psi.property)

end RealEffect

namespace ComplexEffect

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Complex basis effects recover the existing complex computational-basis weight. -/
theorem bornValue_basis_ofState (x : I) (psi : State.ComplexState I) :
    Effect.bornValue (Effect.basis (𝕜 := ℂ) x)
        (ComplexDensityMatrix.ofState psi) =
      State.complexBasisWeight psi x := by
  have hnorm : star (psi : I → ℂ) ⬝ᵥ (psi : I → ℂ) = 1 := by
    have h := congrArg (fun r : ℝ ↦ (r : ℂ)) psi.property
    simpa [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, dotProduct, ← Complex.normSq_eq_conj_mul_self] using h
  simpa [ComplexDensityMatrix.ofState, State.complexBasisWeight,
    State.basisWeight, State.complexWeight] using
    Effect.bornValue_basis_pure (𝕜 := ℂ) x (psi : I → ℂ) hnorm

end ComplexEffect

end QuaternionicComputing.Semantics
