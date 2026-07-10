module

public import QuaternionicComputing.Semantics.OperatorPhase.Quaternion

/-!
# Quaternionic projective operator kernel

This proof leaf characterizes the all-right-ray kernel of a finite square
quaternionic unitary in dimensions at least two.  The hypothesis
`1 < Fintype.card I` is explicit: in rank one every unit quaternion gives a
projectively trivial scalar operator, while only the real signs are central.

Only the first matrix in the kernel theorem is assumed unitary.  Projective
equality forces the second matrix to be its central `±1` multiple.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion RightActions

namespace QuaternionicComputing.Semantics

universe u

private def FixesEveryQuaternionRightRay {I : Type u} [Fintype I]
    (A : Matrix I I ℍ[ℝ]) : Prop :=
  ∀ psi : I → ℍ[ℝ],
    Quaternion.RightPhaseEquivalent (A *ᵥ psi) psi

private theorem quaternion_central_of_commutes_i_j (eta : ℍ[ℝ])
    (hi : eta * Quaternion.i = Quaternion.i * eta)
    (hj : eta * Quaternion.j = Quaternion.j * eta) :
    eta = (eta.re : ℍ[ℝ]) := by
  apply QuaternionAlgebra.ext
  · rfl
  · have h := congrArg (fun q : ℍ[ℝ] ↦ q.imK) hj
    norm_num [Quaternion.i, Quaternion.j] at h ⊢
    linarith
  · have h := congrArg (fun q : ℍ[ℝ] ↦ q.imK) hi
    norm_num [Quaternion.i, Quaternion.j] at h ⊢
    linarith
  · have h := congrArg (fun q : ℍ[ℝ] ↦ q.imJ) hi
    norm_num [Quaternion.i, Quaternion.j] at h ⊢
    linarith

private theorem fixesEveryQuaternionRightRay_centralSign
    {I : Type u} [Fintype I] [DecidableEq I]
    (hdim : 1 < Fintype.card I)
    (A : Matrix I I ℍ[ℝ]) (hA : FixesEveryQuaternionRightRay A) :
    ∃ s : ℝ, s * s = 1 ∧
      ∀ y x, A y x = (s : ℍ[ℝ]) * (1 : Matrix I I ℍ[ℝ]) y x := by
  classical
  obtain ⟨i0, i1, hi01⟩ := Fintype.exists_pair_of_one_lt_card hdim
  let eta : I → ℍ[ℝ] := fun x ↦ (hA (Pi.single x 1)).choose
  have heta_norm (x : I) : _root_.Quaternion.normSq (eta x) = 1 :=
    (hA (Pi.single x 1)).choose_spec.1
  have hcol (x : I) :
      A *ᵥ Pi.single x 1 = Pi.single x 1 <• eta x :=
    (hA (Pi.single x 1)).choose_spec.2
  have hentry (y x : I) : A y x = if y = x then eta x else 0 := by
    have h := congrFun (hcol x) y
    simpa [Pi.single_apply] using h
  have heta_common (x : I) : eta x = eta i0 := by
    by_cases hxi : x = i0
    · simp [hxi]
    · rcases hA (Pi.single i0 1 + Pi.single x 1) with
        ⟨theta, htheta, hsum⟩
      rw [Matrix.mulVec_add, hcol i0, hcol x] at hsum
      have hs0 := congrFun hsum i0
      have hsx := congrFun hsum x
      simp [hxi, Ne.symm hxi] at hs0 hsx
      exact hsx.trans hs0.symm
  have hcomm (q : ℍ[ℝ]) : eta i0 * q = q * eta i0 := by
    let v : I → ℍ[ℝ] := Pi.single i0 q + Pi.single i1 1
    rcases hA v with ⟨theta, htheta, hv⟩
    have hv0 := congrFun hv i0
    have hv1 := congrFun hv i1
    have hv0' : eta i0 * q = q * theta := by
      simpa [v, Matrix.mulVec, dotProduct, hentry, Pi.single_apply,
        hi01, Ne.symm hi01, heta_common] using hv0
    have hv1' : eta i0 = theta := by
      simpa [v, Matrix.mulVec, dotProduct, hentry, Pi.single_apply,
        hi01, Ne.symm hi01, heta_common] using hv1
    rw [← hv1'] at hv0'
    exact hv0'
  have heta_real := quaternion_central_of_commutes_i_j (eta i0)
    (hcomm Quaternion.i) (hcomm Quaternion.j)
  refine ⟨(eta i0).re, ?_, ?_⟩
  · have hnorm : _root_.Quaternion.normSq ((eta i0).re : ℍ[ℝ]) =
        (eta i0).re * (eta i0).re := by
      rw [_root_.Quaternion.normSq_coe, pow_two]
    have h := heta_norm i0
    rw [heta_real, hnorm] at h
    exact h
  · intro y x
    rw [hentry, heta_common x, heta_real]
    by_cases hyx : y = x
    · subst y
      simp
    · simp [hyx]

namespace QuaternionRawProjectiveActionEq

/--
In finite square dimension at least two, a unitary's raw all-right-ray kernel
contains only central real signs.  No unitarity premise on `V` is needed.
-/
theorem centralSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]}
    (hdim : 1 < Fintype.card I)
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ]))
    (h : QuaternionRawProjectiveActionEq U V) :
    QuaternionCentralSignEq U V := by
  let A : Matrix I I ℍ[ℝ] := V * star U
  have hfix : FixesEveryQuaternionRightRay A := by
    intro psi
    have hp := Quaternion.rightPhaseEquivalent_symm (h (star U *ᵥ psi))
    simpa only [A, Matrix.mulVec_mulVec,
      Unitary.mul_star_self_of_mem hU, Matrix.one_mulVec] using hp
  rcases fixesEveryQuaternionRightRay_centralSign hdim A hfix with
    ⟨s, hs, hA⟩
  have hAeq : A = s • (1 : Matrix I I ℍ[ℝ]) := by
    funext y x
    rw [hA]
    change (s : ℍ[ℝ]) * (1 : Matrix I I ℍ[ℝ]) y x =
      s • (1 : Matrix I I ℍ[ℝ]) y x
    exact (_root_.Quaternion.coe_mul_eq_smul s
      ((1 : Matrix I I ℍ[ℝ]) y x))
  refine ⟨s, hs, ?_⟩
  have hmul := congrArg (fun M : Matrix I I ℍ[ℝ] ↦ M * U) hAeq
  simpa only [A, Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU,
    Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] using hmul

end QuaternionRawProjectiveActionEq

/-- Raw quaternionic all-right-ray action has exactly the central-sign kernel
in unitary square dimension at least two. -/
theorem quaternionRawProjectiveActionEq_iff_centralSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]}
    (hdim : 1 < Fintype.card I)
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ])) :
    QuaternionRawProjectiveActionEq U V ↔ QuaternionCentralSignEq U V :=
  ⟨QuaternionRawProjectiveActionEq.centralSignEq_of_unitary hdim hU,
    QuaternionCentralSignEq.rawProjectiveActionEq⟩

namespace QuaternionProjectiveActionEq

/--
In finite square dimension at least two, equality of projective action on all
normalized pure inputs forces one central real sign.
-/
theorem centralSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]}
    (hdim : 1 < Fintype.card I)
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ]))
    (h : QuaternionProjectiveActionEq U V) :
    QuaternionCentralSignEq U V :=
  h.rawProjectiveActionEq.centralSignEq_of_unitary hdim hU

end QuaternionProjectiveActionEq

/--
Quaternionic projective action on normalized pure inputs has exactly the
central `±1` kernel in unitary square dimension at least two.
-/
theorem quaternionProjectiveActionEq_iff_centralSignEq_of_unitary
    {I : Type u} [Fintype I] [DecidableEq I]
    {U V : Matrix I I ℍ[ℝ]}
    (hdim : 1 < Fintype.card I)
    (hU : U ∈ unitary (Matrix I I ℍ[ℝ])) :
    QuaternionProjectiveActionEq U V ↔ QuaternionCentralSignEq U V :=
  ⟨QuaternionProjectiveActionEq.centralSignEq_of_unitary hdim hU,
    QuaternionCentralSignEq.projectiveActionEq⟩

/-! ## Rank-one exception -/

/-- The one-by-one quaternionic matrix whose sole entry is `q`. -/
def quaternionRankOneScalar (q : ℍ[ℝ]) : Matrix Unit Unit ℍ[ℝ] :=
  fun _ _ ↦ q

/-- A unit quaternion gives a unitary one-by-one scalar matrix. -/
theorem quaternionRankOneScalar_mem_unitary (q : ℍ[ℝ])
    (hq : _root_.Quaternion.normSq q = 1) :
    quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ]) := by
  change star (quaternionRankOneScalar q) * quaternionRankOneScalar q = 1 ∧
    quaternionRankOneScalar q * star (quaternionRankOneScalar q) = 1
  constructor
  · funext y x
    cases y
    cases x
    simp [quaternionRankOneScalar, Matrix.mul_apply,
      _root_.Quaternion.star_mul_self, hq]
  · funext y x
    cases y
    cases x
    simp [quaternionRankOneScalar, Matrix.mul_apply,
      _root_.Quaternion.self_mul_star, hq]

/-- A one-by-one quaternionic scalar matrix is unitary exactly when its scalar
has norm square one. -/
theorem quaternionRankOneScalar_mem_unitary_iff (q : ℍ[ℝ]) :
    quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ]) ↔
      _root_.Quaternion.normSq q = 1 := by
  constructor
  · rintro ⟨h, -⟩
    have he := congrFun (congrFun h ()) ()
    have hre := congrArg (fun x : ℍ[ℝ] ↦ x.re) he
    simpa [quaternionRankOneScalar, Matrix.mul_apply,
      _root_.Quaternion.star_mul_self] using hre
  · exact quaternionRankOneScalar_mem_unitary q

/-- Every unit quaternion is invisible to raw rank-one right-ray action. -/
theorem quaternionRankOneScalar_rawProjectiveActionEq (q : ℍ[ℝ])
    (hq : _root_.Quaternion.normSq q = 1) :
    QuaternionRawProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
      (quaternionRankOneScalar q) := by
  intro psi
  by_cases hx : psi () = 0
  · refine ⟨1, by simp, ?_⟩
    funext u
    cases u
    simp [quaternionRankOneScalar, Matrix.mulVec, dotProduct, hx]
  · let z : ℍ[ℝ] := q * psi ()
    have hq0 : q ≠ 0 :=
      _root_.Quaternion.normSq_ne_zero.mp (by simp [hq])
    have hz : z ≠ 0 := mul_ne_zero hq0 hx
    refine ⟨z⁻¹ * psi (), ?_, ?_⟩
    · rw [map_mul, _root_.Quaternion.normSq_inv, map_mul, hq, one_mul,
        inv_mul_cancel₀ (_root_.Quaternion.normSq_ne_zero.mpr hx)]
    · funext u
      cases u
      simp only [Matrix.one_mulVec, Pi.smul_apply,
        MulOpposite.smul_eq_mul_unop]
      change psi () =
        (quaternionRankOneScalar q *ᵥ psi) () * (z⁻¹ * psi ())
      rw [show (quaternionRankOneScalar q *ᵥ psi) () = z by
        simp [quaternionRankOneScalar, Matrix.mulVec, dotProduct, z],
        ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- Raw rank-one projective action identifies precisely the full family of
unit quaternions. -/
theorem quaternionRankOneScalar_rawProjectiveActionEq_iff_normSq_eq_one
    (q : ℍ[ℝ]) :
    QuaternionRawProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar q) ↔
      _root_.Quaternion.normSq q = 1 := by
  constructor
  · intro h
    rcases h (fun _ ↦ 1) with ⟨eta, heta, heq⟩
    have he := congrFun heq ()
    have hn := congrArg _root_.Quaternion.normSq he
    simpa [quaternionRankOneScalar, Matrix.mulVec, dotProduct, map_mul,
      heta] using hn.symm
  · exact quaternionRankOneScalar_rawProjectiveActionEq q

/-- Every unit quaternion is invisible to normalized rank-one projective action. -/
theorem quaternionRankOneScalar_projectiveActionEq (q : ℍ[ℝ])
    (hq : _root_.Quaternion.normSq q = 1) :
    QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
      (quaternionRankOneScalar q) :=
  (quaternionRankOneScalar_rawProjectiveActionEq q hq).projectiveActionEq

/-- Normalized rank-one projective action identifies precisely the full
family of unit quaternions. -/
theorem quaternionRankOneScalar_projectiveActionEq_iff_normSq_eq_one
    (q : ℍ[ℝ]) :
    QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar q) ↔
      _root_.Quaternion.normSq q = 1 :=
  (quaternionRawProjectiveActionEq_iff_projectiveActionEq
      (U := (1 : Matrix Unit Unit ℍ[ℝ]))
      (V := quaternionRankOneScalar q)).symm.trans
    (quaternionRankOneScalar_rawProjectiveActionEq_iff_normSq_eq_one q)

/-- In rank one, projective triviality of a scalar operator is equivalent to
unitarity, and is strictly broader than central-sign equality. -/
theorem quaternionRankOneScalar_projectiveActionEq_iff_mem_unitary
    (q : ℍ[ℝ]) :
    QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar q) ↔
      quaternionRankOneScalar q ∈ unitary (Matrix Unit Unit ℍ[ℝ]) :=
  (quaternionRankOneScalar_projectiveActionEq_iff_normSq_eq_one q).trans
    (quaternionRankOneScalar_mem_unitary_iff q).symm

/-- The rank-one `j` phase is not a central real sign. -/
theorem quaternionRankOneJ_not_centralSignEq :
    ¬ QuaternionCentralSignEq (1 : Matrix Unit Unit ℍ[ℝ])
      (quaternionRankOneScalar Quaternion.j) := by
  rintro ⟨s, hs, h⟩
  have he := congrFun (congrFun h ()) ()
  have hj := congrArg (fun q : ℍ[ℝ] ↦ q.imJ) he
  norm_num [quaternionRankOneScalar, Quaternion.j] at hj

/--
At rank one, left multiplication by `j` is unitary and projectively trivial,
but it is not a central sign.  This is the explicit exception to the
dimension-at-least-two kernel theorem.
-/
theorem quaternionRankOneJ_exception :
    quaternionRankOneScalar Quaternion.j ∈
        unitary (Matrix Unit Unit ℍ[ℝ]) ∧
      QuaternionProjectiveActionEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar Quaternion.j) ∧
      ¬ QuaternionCentralSignEq (1 : Matrix Unit Unit ℍ[ℝ])
        (quaternionRankOneScalar Quaternion.j) :=
  ⟨quaternionRankOneScalar_mem_unitary Quaternion.j
      QuaternionicComputing.Quaternion.normSq_j,
    quaternionRankOneScalar_projectiveActionEq Quaternion.j
      QuaternionicComputing.Quaternion.normSq_j,
    quaternionRankOneJ_not_centralSignEq⟩

end QuaternionicComputing.Semantics
