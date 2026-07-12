module

public import QuaternionicComputing.State.Unitary
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic

/-!
# Finite real and complex density matrices

This leaf supplies the finite-dimensional mixed-state core used by the later
physical-effect and channel semantics.  A density matrix stores exactly the
two physical invariants needed here: positive semidefiniteness and trace one.
Hermiticity is derived from positivity rather than duplicated as structure
data.

The implementation is uniform over `RCLike` scalars, and explicit real and
complex aliases keep the two intended models visible at API boundaries.  It
does not define quaternionic density matrices: mathlib's ordered-star matrix
positivity used below is the commutative real/complex theory.

Pure states use the ket--bra convention
`Matrix.vecMulVec psi (star psi)`, so their `(i,j)` entry is
`psi i * star (psi j)`.  Unitary evolution is chronological left action,
`U * rho * Uᴴ`.  In particular, applying `U` and then `V` is conjugation by
`V * U`.

A trace-one matrix cannot exist on an empty index type.  This obstruction is
proved explicitly; no global `Nonempty` instance is introduced.
-/

@[expose] public noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace QuaternionicComputing.Semantics

universe u v

/-! ## Density matrices and their basic invariants -/

/--
A finite density matrix over an `RCLike` scalar field.

The matrix is positive semidefinite and has trace exactly `1`.  Hermiticity is
a theorem because it follows from `Matrix.PosSemidef`.
-/
structure DensityMatrix (𝕜 : Type u) (I : Type v) [RCLike 𝕜] [Fintype I] where
  /-- The underlying square matrix. -/
  matrix : Matrix I I 𝕜
  /-- Positivity of the underlying matrix. -/
  posSemidef : matrix.PosSemidef
  /-- Normalization of the underlying matrix. -/
  trace_one : matrix.trace = 1

/-- A finite real density matrix. -/
abbrev RealDensityMatrix (I : Type v) [Fintype I] :=
  DensityMatrix ℝ I

/-- A finite complex density matrix. -/
abbrev ComplexDensityMatrix (I : Type v) [Fintype I] :=
  DensityMatrix ℂ I

namespace DensityMatrix

variable {𝕜 : Type u} {I : Type v} [RCLike 𝕜] [Fintype I]

/-- Use a density matrix as its underlying matrix. -/
instance : Coe (DensityMatrix 𝕜 I) (Matrix I I 𝕜) where
  coe ρ := ρ.matrix

/-- Coercion exposes the stored underlying matrix definitionally. -/
@[simp]
theorem coe_matrix (ρ : DensityMatrix 𝕜 I) :
    ((ρ : Matrix I I 𝕜)) = ρ.matrix :=
  rfl

/-- Two density matrices are equal when their underlying matrices are equal. -/
theorem ext_matrix {ρ σ : DensityMatrix 𝕜 I}
    (h : (ρ : Matrix I I 𝕜) = (σ : Matrix I I 𝕜)) : ρ = σ := by
  cases ρ
  cases σ
  simpa using h

/-- Density matrices are extensional in their entries. -/
@[ext]
theorem ext {ρ σ : DensityMatrix 𝕜 I}
    (h : ∀ i j, (ρ : Matrix I I 𝕜) i j = (σ : Matrix I I 𝕜) i j) :
    ρ = σ :=
  ext_matrix (Matrix.ext fun i j ↦ h i j)

/-- Equality of density matrices is equivalent to entrywise matrix equality. -/
theorem eq_iff_entries {ρ σ : DensityMatrix 𝕜 I} :
    ρ = σ ↔
      ∀ i j, (ρ : Matrix I I 𝕜) i j = (σ : Matrix I I 𝕜) i j := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · exact ext

/-- Every density matrix is Hermitian, as a consequence of positivity. -/
theorem isHermitian (ρ : DensityMatrix 𝕜 I) :
    (ρ : Matrix I I 𝕜).IsHermitian :=
  ρ.posSemidef.isHermitian

/-- The conjugate transpose of a density matrix's underlying matrix is itself. -/
@[simp]
theorem conjTranspose_eq (ρ : DensityMatrix 𝕜 I) :
    (ρ : Matrix I I 𝕜)ᴴ = (ρ : Matrix I I 𝕜) :=
  ρ.isHermitian.eq

/-- The coerced underlying matrix has trace one. -/
@[simp]
theorem trace_eq_one (ρ : DensityMatrix 𝕜 I) :
    Matrix.trace (ρ : Matrix I I 𝕜) = 1 :=
  ρ.trace_one

/-! ## The empty-index obstruction -/

/--
There is no density matrix on an empty finite index type: its trace would be
both `0` and `1`.
-/
theorem isEmpty_of_index_isEmpty [IsEmpty I] : IsEmpty (DensityMatrix 𝕜 I) :=
  ⟨fun ρ ↦ (zero_ne_one : (0 : 𝕜) ≠ 1)
    (by simpa [Matrix.trace] using ρ.trace_one)⟩

/-- The existence of a density matrix forces the index type to be nonempty. -/
theorem index_nonempty (ρ : DensityMatrix 𝕜 I) : Nonempty I := by
  classical
  by_contra hI
  letI : IsEmpty I := not_nonempty_iff.mp hI
  exact isEmpty_of_index_isEmpty.false ρ

/-! ## Normalized rank-one states -/

/-- The ket--bra matrix `|psi><psi|` of a finite scalar column. -/
def pureMatrix (psi : I → 𝕜) : Matrix I I 𝕜 :=
  Matrix.vecMulVec psi (star psi)

omit [Fintype I] in
/-- Entries of a ket--bra matrix have the expected multiplication order. -/
@[simp] theorem pureMatrix_apply (psi : I → 𝕜) (i j : I) :
    pureMatrix psi i j = psi i * star (psi j) :=
  rfl

omit [Fintype I] in variable [Finite I] in
/-- Every ket--bra matrix is positive semidefinite. -/
theorem pureMatrix_posSemidef (psi : I → 𝕜) :
    (pureMatrix psi).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star psi

/-- The trace of a ket--bra is the star-dot squared norm of its ket. -/
@[simp]
theorem trace_pureMatrix (psi : I → 𝕜) :
    Matrix.trace (pureMatrix psi) = star psi ⬝ᵥ psi := by
  simp [pureMatrix, dotProduct, mul_comm]

/-- Bundle a star-dot normalized column as its rank-one pure density matrix. -/
def pure (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) : DensityMatrix 𝕜 I where
  matrix := pureMatrix psi
  posSemidef := pureMatrix_posSemidef psi
  trace_one := by simpa using hpsi

/-- The underlying matrix of a pure density is its ket--bra. -/
@[simp]
theorem pure_coe (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) :
    ((pure psi hpsi : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = pureMatrix psi :=
  rfl

/-- Entries of a pure density are ket amplitudes times bra amplitudes. -/
@[simp]
theorem pure_apply (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1)
    (i j : I) :
    ((pure psi hpsi : DensityMatrix 𝕜 I) : Matrix I I 𝕜) i j =
      psi i * star (psi j) :=
  rfl

/-- The positivity proof for a pure density is the ket--bra positivity theorem. -/
theorem pure_posSemidef (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) :
    (((pure psi hpsi : DensityMatrix 𝕜 I) : Matrix I I 𝕜)).PosSemidef :=
  (pure psi hpsi).posSemidef

/-- A pure density has trace one. -/
@[simp]
theorem trace_pure (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) :
    Matrix.trace ((pure psi hpsi : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = 1 :=
  (pure psi hpsi).trace_one

/-! ## Computational-basis densities -/

/--
The density of the computational-basis ket at `x`.

The ket is written directly as `Pi.single x 1`, the same representation used
by `Semantics.basisKet`, without importing the higher-level basis-behavior
classification leaf into this low-dependency physical-state core.
-/
def basis (x : I) [DecidableEq I] : DensityMatrix 𝕜 I :=
  pure (Pi.single x (1 : 𝕜) : I → 𝕜) (by
    rw [dotProduct, Finset.sum_eq_single x]
    · simp
    · intro i _ hix
      simp [hix]
    · simp)

/-- The underlying basis density is the ket--bra of `Pi.single x 1`. -/
@[simp]
theorem basis_coe (x : I) [DecidableEq I] :
    ((basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
      pureMatrix (Pi.single x 1) :=
  rfl

/-- A basis density has a single `1` at `(x,x)` and zero elsewhere. -/
@[simp]
theorem basis_apply (x i j : I) [DecidableEq I] :
    ((basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜) i j =
      if i = x ∧ j = x then 1 else 0 := by
  change Matrix.vecMulVec (Pi.single x (1 : 𝕜))
      (star (Pi.single x (1 : 𝕜))) i j =
        if i = x ∧ j = x then 1 else 0
  by_cases hi : i = x <;> by_cases hj : j = x <;>
    simp [Matrix.vecMulVec_apply, hi, hj]

/-- A basis density is positive semidefinite. -/
theorem basis_posSemidef (x : I) [DecidableEq I] :
    (((basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜)).PosSemidef :=
  (basis (𝕜 := 𝕜) x).posSemidef

/-- A basis density has trace one. -/
@[simp]
theorem trace_basis (x : I) [DecidableEq I] :
    Matrix.trace ((basis (𝕜 := 𝕜) x : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = 1 :=
  (basis (𝕜 := 𝕜) x).trace_one

/-- A finite index type carries a density matrix exactly when it is nonempty. -/
theorem nonempty_iff : Nonempty (DensityMatrix 𝕜 I) ↔ Nonempty I := by
  constructor
  · rintro ⟨ρ⟩
    exact ρ.index_nonempty
  · rintro ⟨i⟩
    classical
    exact ⟨basis (𝕜 := 𝕜) i⟩

/-! ## Unitary conjugation -/

/--
Evolve a density matrix by unitary conjugation `U * rho * Uᴴ`.

The multiplication order matches left action on state columns.  The unitary
certificate proves trace preservation; positivity is preserved by matrix
conjugation.
-/
def unitaryConjugate [DecidableEq I] (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    DensityMatrix 𝕜 I where
  matrix := U * (ρ : Matrix I I 𝕜) * Uᴴ
  posSemidef := ρ.posSemidef.mul_mul_conjTranspose_same U
  trace_one := by
    have hstar : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Unitary.star_mul_self_of_mem hU
    rw [Matrix.trace_mul_cycle U (ρ : Matrix I I 𝕜) Uᴴ, hstar,
      Matrix.one_mul, ρ.trace_one]

/-- Unitary conjugation computes as `U * rho * Uᴴ`. -/
@[simp]
theorem unitaryConjugate_coe [DecidableEq I] (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    ((unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
      U * (ρ : Matrix I I 𝕜) * Uᴴ :=
  rfl

/-- Unitary conjugation preserves positive semidefiniteness. -/
theorem unitaryConjugate_posSemidef [DecidableEq I] (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    (((unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) : Matrix I I 𝕜)).PosSemidef :=
  (unitaryConjugate U hU ρ).posSemidef

/-- Unitary conjugation preserves Hermiticity. -/
theorem unitaryConjugate_isHermitian [DecidableEq I] (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    (((unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) : Matrix I I 𝕜)).IsHermitian :=
  (unitaryConjugate U hU ρ).isHermitian

/-- Unitary conjugation preserves trace one. -/
@[simp]
theorem trace_unitaryConjugate [DecidableEq I] (U : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    Matrix.trace
      ((unitaryConjugate U hU ρ : DensityMatrix 𝕜 I) : Matrix I I 𝕜) = 1 :=
  (unitaryConjugate U hU ρ).trace_one

/-- Conjugation by the identity unitary fixes every density matrix. -/
@[simp]
theorem unitaryConjugate_one [DecidableEq I] (ρ : DensityMatrix 𝕜 I) :
    unitaryConjugate 1 (unitary (Matrix I I 𝕜)).one_mem ρ = ρ := by
  apply ext_matrix
  simp

/--
Successive conjugation by `U` and then `V` is conjugation by `V * U`.

This equation records chronological multiplication order explicitly.
-/
theorem unitaryConjugate_comp [DecidableEq I]
    (U V : Matrix I I 𝕜)
    (hU : U ∈ unitary (Matrix I I 𝕜))
    (hV : V ∈ unitary (Matrix I I 𝕜)) (ρ : DensityMatrix 𝕜 I) :
    unitaryConjugate V hV (unitaryConjugate U hU ρ) =
      unitaryConjugate (V * U) ((unitary (Matrix I I 𝕜)).mul_mem hV hU) ρ := by
  apply ext_matrix
  simp only [unitaryConjugate_coe, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Unitary conjugation of a pure density is the ket--bra of the evolved ket. -/
theorem unitaryConjugate_pure_coe [DecidableEq I]
    (U : Matrix I I 𝕜) (hU : U ∈ unitary (Matrix I I 𝕜))
    (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) :
    ((unitaryConjugate U hU (pure psi hpsi) : DensityMatrix 𝕜 I) : Matrix I I 𝕜) =
      pureMatrix (U *ᵥ psi) := by
  simp only [unitaryConjugate_coe, pure_coe, pureMatrix, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]

/-- Unitary conjugation commutes with the normalized pure-state constructor. -/
theorem unitaryConjugate_pure [DecidableEq I]
    (U : Matrix I I 𝕜) (hU : U ∈ unitary (Matrix I I 𝕜))
    (psi : I → 𝕜) (hpsi : star psi ⬝ᵥ psi = 1) :
    unitaryConjugate U hU (pure psi hpsi) =
      pure (U *ᵥ psi) (by
        calc
          star (U *ᵥ psi) ⬝ᵥ (U *ᵥ psi) = star psi ⬝ᵥ psi :=
            State.star_dotProduct_mulVec_of_mem_unitary hU psi
          _ = 1 := hpsi) := by
  apply ext_matrix
  exact unitaryConjugate_pure_coe U hU psi hpsi

end DensityMatrix

/-! ## Existing normalized-state compatibility -/

namespace RealDensityMatrix

variable {I : Type v} [Fintype I]

/-- Turn an existing normalized real state into its rank-one density matrix. -/
def ofState (psi : State.RealState I) : RealDensityMatrix I :=
  DensityMatrix.pure (psi : I → ℝ) (by
    simpa [State.realTotalWeight, State.totalWeight, State.basisWeight,
      State.realWeight, dotProduct] using psi.property)

/-- The real state constructor has entries `psi i * psi j`. -/
@[simp]
theorem ofState_apply (psi : State.RealState I) (i j : I) :
    ((ofState psi : RealDensityMatrix I) : Matrix I I ℝ) i j = psi i * psi j :=
  rfl

end RealDensityMatrix

namespace ComplexDensityMatrix

variable {I : Type v} [Fintype I]

/-- Turn an existing normalized complex state into its rank-one density matrix. -/
def ofState (psi : State.ComplexState I) : ComplexDensityMatrix I :=
  DensityMatrix.pure (psi : I → ℂ) (by
    have h := congrArg (fun r : ℝ ↦ (r : ℂ)) psi.property
    simpa [State.complexTotalWeight, State.totalWeight, State.basisWeight,
      State.complexWeight, dotProduct, ← Complex.normSq_eq_conj_mul_self] using h)

/-- The complex state constructor has ket--bra entries. -/
@[simp]
theorem ofState_apply (psi : State.ComplexState I) (i j : I) :
    ((ofState psi : ComplexDensityMatrix I) : Matrix I I ℂ) i j =
      psi i * star (psi j) :=
  rfl

end ComplexDensityMatrix

end QuaternionicComputing.Semantics
