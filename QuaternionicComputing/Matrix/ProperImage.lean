module

public import QuaternionicComputing.Matrix.Determinant
public import QuaternionicComputing.Matrix.QuaternionRealificationUnitary

/-!
# Explicit proper-image witnesses in doubled dimension four

This file gives checked low-dimensional non-surjectivity witnesses for all
three matrix embeddings used by the library.  For the two doubled embeddings,
the source index is `Bool`, and the target index `Bool ⊕ Bool` has four
elements.  In both target scalar fields the witness is diagonal, with `-1` on
the first sum sector and `1` on the second.

The real witness belongs to `SO(4)` but violates realification's equality of
the two diagonal blocks.  The complex witness belongs to `SU(4)` but violates
complexification's conjugate-diagonal-block constraint.  Thus the second
codomain is a complex special-unitary/unitary group, not `Sp(2N)` as named in
the paper's converse sentence.

Only the two doubled-map failures displayed above use `N = 2`.  The intended
`N = 1` exceptions—realification from `U(1)` versus `SO(2)`, and quaternionic
complexification from `Sp(1)` versus `SU(2)`—are noted only to exclude them:
no equality or surjectivity theorem about those cases is asserted here.
Matrix non-surjectivity here implies no circuit-width, communication,
signaling, or other operational lower bound.

For Equation 63's direct quaternion-to-real embedding, an analogous diagonal
matrix already gives an `SO(4)` witness at quaternionic rank one.  Its four
diagonal entries are not all equal, whereas every direct realification of a
`1 × 1` quaternion matrix has the same real component in all four diagonal
sectors.  This formally rules out the paper's claimed surjectivity onto the
whole `SO(4N)` target.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Matrix.ProperImage

open QuaternionicComputing.Matrix
open QuaternionicComputing.Quaternion

/-! ## The real special-orthogonal witness -/

/-- Sector signs for the real four-dimensional diagonal witness. -/
def realSectorSign : Bool ⊕ Bool → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

/-- The real diagonal matrix `diag(-1,-1,1,1)` on `Bool ⊕ Bool`. -/
def realWitness : _root_.Matrix (Bool ⊕ Bool) (Bool ⊕ Bool) ℝ :=
  _root_.Matrix.diagonal realSectorSign

@[simp]
theorem realWitness_inl_diag (i : Bool) :
    realWitness (Sum.inl i) (Sum.inl i) = -1 := by
  simp [realWitness, realSectorSign]

@[simp]
theorem realWitness_inr_diag (i : Bool) :
    realWitness (Sum.inr i) (Sum.inr i) = 1 := by
  simp [realWitness, realSectorSign]

/-- The real sign witness is orthogonal. -/
theorem realWitness_mem_orthogonal :
    realWitness ∈ _root_.Matrix.orthogonalGroup (Bool ⊕ Bool) ℝ := by
  rw [_root_.Matrix.mem_orthogonalGroup_iff]
  rw [realWitness, _root_.Matrix.diagonal_transpose,
    _root_.Matrix.diagonal_mul_diagonal]
  ext (i | i) (j | j) <;>
    by_cases h : i = j <;> simp [realSectorSign, h, _root_.Matrix.one_apply]

/-- The real sign witness has determinant one. -/
@[simp]
theorem realWitness_det : realWitness.det = 1 := by
  rw [realWitness, _root_.Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [realSectorSign]

/-- The real witness lies in the four-dimensional special orthogonal group. -/
theorem realWitness_mem_specialOrthogonal :
    realWitness ∈ _root_.Matrix.specialOrthogonalGroup (Bool ⊕ Bool) ℝ := by
  rw [_root_.Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨realWitness_mem_orthogonal, realWitness_det⟩

/-- No complex `2 × 2` matrix realifies to the real witness. -/
theorem realWitness_ne_realify (A : _root_.Matrix Bool Bool ℂ) :
    realWitness ≠ realify A := by
  intro h
  have htop := congrFun (congrFun h (Sum.inl false)) (Sum.inl false)
  have hbottom := congrFun (congrFun h (Sum.inr false)) (Sum.inr false)
  simp only [realWitness_inl_diag, realWitness_inr_diag,
    realify_apply_inl_inl, realify_apply_inr_inr] at htop hbottom
  linarith

/-- The real witness is outside the image of realification, even on all matrices. -/
theorem realWitness_not_exists_realify :
    ¬ ∃ A : _root_.Matrix Bool Bool ℂ, realify A = realWitness := by
  rintro ⟨A, hA⟩
  exact realWitness_ne_realify A hA.symm

/-- A bundled `SO(4)`-but-not-realification witness. -/
theorem realWitness_specialOrthogonal_not_realify :
    realWitness ∈ _root_.Matrix.specialOrthogonalGroup (Bool ⊕ Bool) ℝ ∧
      ¬ ∃ A : _root_.Matrix Bool Bool ℂ, realify A = realWitness :=
  ⟨realWitness_mem_specialOrthogonal, realWitness_not_exists_realify⟩

/-! ## The complex special-unitary witness -/

/-- Sector signs for the complex four-dimensional diagonal witness. -/
def complexSectorSign : Bool ⊕ Bool → ℂ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

/-- The complex diagonal matrix `diag(-1,-1,1,1)` on `Bool ⊕ Bool`. -/
def complexWitness : _root_.Matrix (Bool ⊕ Bool) (Bool ⊕ Bool) ℂ :=
  _root_.Matrix.diagonal complexSectorSign

@[simp]
theorem complexWitness_inl_diag (i : Bool) :
    complexWitness (Sum.inl i) (Sum.inl i) = -1 := by
  simp [complexWitness, complexSectorSign]

@[simp]
theorem complexWitness_inr_diag (i : Bool) :
    complexWitness (Sum.inr i) (Sum.inr i) = 1 := by
  simp [complexWitness, complexSectorSign]

/-- The complex sign witness is unitary. -/
theorem complexWitness_mem_unitary :
    complexWitness ∈ _root_.Matrix.unitaryGroup (Bool ⊕ Bool) ℂ := by
  rw [_root_.Matrix.mem_unitaryGroup_iff]
  change complexWitness * complexWitnessᴴ = 1
  rw [complexWitness, _root_.Matrix.diagonal_conjTranspose,
    _root_.Matrix.diagonal_mul_diagonal]
  ext (i | i) (j | j) <;>
    by_cases h : i = j <;> simp [complexSectorSign, h, _root_.Matrix.one_apply]

/-- The complex sign witness has determinant one. -/
@[simp]
theorem complexWitness_det : complexWitness.det = 1 := by
  rw [complexWitness, _root_.Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [complexSectorSign]

/-- The complex witness lies in `SU(4)`. -/
theorem complexWitness_mem_specialUnitary :
    complexWitness ∈ _root_.Matrix.specialUnitaryGroup (Bool ⊕ Bool) ℂ := by
  rw [_root_.Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨complexWitness_mem_unitary, complexWitness_det⟩

/-- No quaternionic `2 × 2` matrix complexifies to the complex witness. -/
theorem complexWitness_ne_complexify (A : _root_.Matrix Bool Bool ℍ[ℝ]) :
    complexWitness ≠ complexify A := by
  intro h
  have htop : (-1 : ℂ) = complexPart (A false false) := by
    simpa using congrFun (congrFun h (Sum.inl false)) (Sum.inl false)
  have hbottom : (1 : ℂ) = star (complexPart (A false false)) := by
    simpa using congrFun (congrFun h (Sum.inr false)) (Sum.inr false)
  have hstar : (-1 : ℂ) = star (complexPart (A false false)) := by
    calc
      (-1 : ℂ) = star (-1 : ℂ) := by simp
      _ = star (complexPart (A false false)) := congrArg star htop
  have honeNeg : (1 : ℂ) = -1 := hbottom.trans hstar.symm
  norm_num at honeNeg

/-- The complex witness is outside the image of quaternionic complexification. -/
theorem complexWitness_not_exists_complexify :
    ¬ ∃ A : _root_.Matrix Bool Bool ℍ[ℝ], complexify A = complexWitness := by
  rintro ⟨A, hA⟩
  exact complexWitness_ne_complexify A hA.symm

/-- A bundled `SU(4)`-but-not-quaternionic-complexification witness. -/
theorem complexWitness_specialUnitary_not_complexify :
    complexWitness ∈ _root_.Matrix.specialUnitaryGroup (Bool ⊕ Bool) ℂ ∧
      ¬ ∃ A : _root_.Matrix Bool Bool ℍ[ℝ], complexify A = complexWitness :=
  ⟨complexWitness_mem_specialUnitary, complexWitness_not_exists_complexify⟩

/-! ## The direct quaternion-to-real special-orthogonal witness -/

/-- Sector signs for the rank-one direct-realification witness. -/
def directSectorSign : DirectRealIndex Unit → ℝ
  | Sum.inl (Sum.inl _) => -1
  | Sum.inl (Sum.inr _) => -1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- The direct real diagonal witness `diag(-1,-1,1,1)` in paper-sector order. -/
def directWitness :
    _root_.Matrix (DirectRealIndex Unit) (DirectRealIndex Unit) ℝ :=
  _root_.Matrix.diagonal directSectorSign

@[simp]
theorem directWitness_re_diag :
    directWitness (directRealRe ()) (directRealRe ()) = -1 := by
  simp [directWitness, directSectorSign, directRealRe]

@[simp]
theorem directWitness_imK_diag :
    directWitness (directRealImK ()) (directRealImK ()) = 1 := by
  simp [directWitness, directSectorSign, directRealImK]

/-- The rank-one direct-realification witness is orthogonal. -/
theorem directWitness_mem_orthogonal :
    directWitness ∈
      _root_.Matrix.orthogonalGroup (DirectRealIndex Unit) ℝ := by
  rw [_root_.Matrix.mem_orthogonalGroup_iff]
  rw [directWitness, _root_.Matrix.diagonal_transpose,
    _root_.Matrix.diagonal_mul_diagonal]
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    by_cases h : i = j <;> simp [directSectorSign, h]

/-- The rank-one direct-realification witness has determinant one. -/
@[simp]
theorem directWitness_det : directWitness.det = 1 := by
  rw [directWitness, _root_.Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [directSectorSign]

/-- The rank-one direct-realification witness lies in `SO(4)`. -/
theorem directWitness_mem_specialOrthogonal :
    directWitness ∈
      _root_.Matrix.specialOrthogonalGroup (DirectRealIndex Unit) ℝ := by
  rw [_root_.Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨directWitness_mem_orthogonal, directWitness_det⟩

/-- No quaternionic `1 × 1` matrix directly realifies to the witness. -/
theorem directWitness_ne_directRealify
    (A : _root_.Matrix Unit Unit ℍ[ℝ]) :
    directWitness ≠ directRealify A := by
  intro h
  have hre := congrFun (congrFun h (directRealRe ())) (directRealRe ())
  have himK := congrFun (congrFun h (directRealImK ())) (directRealImK ())
  simp only [directWitness_re_diag, directWitness_imK_diag,
    directRealify_re_re, directRealify_imK_imK] at hre himK
  linarith

/-- The `SO(4)` witness is outside every rank-one direct realification. -/
theorem directWitness_not_exists_directRealify :
    ¬ ∃ A : _root_.Matrix Unit Unit ℍ[ℝ],
      directRealify A = directWitness := by
  rintro ⟨A, hA⟩
  exact directWitness_ne_directRealify A hA.symm

/-- A bundled `SO(4)`-but-not-direct-realification witness. -/
theorem directWitness_specialOrthogonal_not_directRealify :
    directWitness ∈
        _root_.Matrix.specialOrthogonalGroup (DirectRealIndex Unit) ℝ ∧
      ¬ ∃ A : _root_.Matrix Unit Unit ℍ[ℝ],
        directRealify A = directWitness :=
  ⟨directWitness_mem_specialOrthogonal,
    directWitness_not_exists_directRealify⟩

end QuaternionicComputing.Matrix.ProperImage
