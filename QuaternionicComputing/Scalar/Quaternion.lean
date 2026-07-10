module

public import Mathlib.Analysis.Quaternion

/-!
# Complex components of real quaternions

This module packages the decomposition of a real quaternion into two complex
numbers.  With the convention

`q = complexPart q + jPart q * j`,

the first component contains the `1` and `i` coordinates and the second
contains the `j` and `k` coordinates.  The multiplication theorems below keep
the order and complex conjugations explicit; this is the scalar identity used
by the later complex matrix embedding.

The constants `i`, `j`, and `k` are given an explicit type because mathlib's
quaternion implementation exposes coordinates but deliberately does not make
global choices of named basis elements in the analysis module.
-/

@[expose] public noncomputable section

open scoped Quaternion

namespace QuaternionicComputing.Quaternion

/-- The quaternion unit `i = (0, 1, 0, 0)`. -/
def i : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion unit `j = (0, 0, 1, 0)`. -/
def j : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- The quaternion unit `k = (0, 0, 0, 1)`. -/
def k : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

@[simp] theorem re_i : i.re = 0 := rfl
@[simp] theorem imI_i : i.imI = 1 := rfl
@[simp] theorem imJ_i : i.imJ = 0 := rfl
@[simp] theorem imK_i : i.imK = 0 := rfl

@[simp] theorem re_j : j.re = 0 := rfl
@[simp] theorem imI_j : j.imI = 0 := rfl
@[simp] theorem imJ_j : j.imJ = 1 := rfl
@[simp] theorem imK_j : j.imK = 0 := rfl

@[simp] theorem re_k : k.re = 0 := rfl
@[simp] theorem imI_k : k.imI = 0 := rfl
@[simp] theorem imJ_k : k.imJ = 0 := rfl
@[simp] theorem imK_k : k.imK = 1 := rfl

/-- The `1,i` coordinates of a quaternion, bundled as a real-linear map. -/
def complexPart : ℍ[ℝ] →ₗ[ℝ] ℂ where
  toFun q := ⟨q.re, q.imI⟩
  map_add' _ _ := rfl
  map_smul' r q := by
    apply Complex.ext <;> simp

/--
The `j,k` coordinates of a quaternion, bundled as a real-linear map.

This is the component called the “weird part” in the paper.
-/
def jPart : ℍ[ℝ] →ₗ[ℝ] ℂ where
  toFun q := ⟨q.imJ, q.imK⟩
  map_add' _ _ := rfl
  map_smul' r q := by
    apply Complex.ext <;> simp

@[simp]
theorem complexPart_re (q : ℍ[ℝ]) : (complexPart q).re = q.re :=
  by simp [complexPart]

@[simp]
theorem complexPart_im (q : ℍ[ℝ]) : (complexPart q).im = q.imI :=
  by simp [complexPart]

@[simp]
theorem jPart_re (q : ℍ[ℝ]) : (jPart q).re = q.imJ :=
  by simp [jPart]

@[simp]
theorem jPart_im (q : ℍ[ℝ]) : (jPart q).im = q.imK :=
  by simp [jPart]

@[simp]
theorem complexPart_coeComplex (z : ℂ) : complexPart (z : ℍ[ℝ]) = z := by
  apply Complex.ext <;> simp

@[simp]
theorem jPart_coeComplex (z : ℂ) : jPart (z : ℍ[ℝ]) = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem complexPart_i : complexPart i = Complex.I := by
  apply Complex.ext <;> simp

@[simp] theorem jPart_i : jPart i = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem complexPart_j : complexPart j = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem jPart_j : jPart j = 1 := by
  apply Complex.ext <;> simp

@[simp] theorem complexPart_k : complexPart k = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem jPart_k : jPart k = Complex.I := by
  apply Complex.ext <;> simp

/-- Right multiplication by `j` embeds a complex number in the `j,k` plane. -/
@[simp]
theorem coeComplex_mul_j_complexPart (z : ℂ) :
    complexPart ((z : ℍ[ℝ]) * j) = 0 := by
  apply Complex.ext <;> simp

/-- Right multiplication by `j` preserves the complex coordinates as weird coordinates. -/
@[simp]
theorem coeComplex_mul_j_jPart (z : ℂ) :
    jPart ((z : ℍ[ℝ]) * j) = z := by
  apply Complex.ext <;> simp

/-- A quaternion is reconstructed from its two complex components. -/
theorem eq_complexPart_add_jPart_mul_j (q : ℍ[ℝ]) :
    q = (complexPart q : ℍ[ℝ]) + (jPart q : ℍ[ℝ]) * j := by
  apply QuaternionAlgebra.ext <;> simp

/-- Quaternions with equal complex and `j` components are equal. -/
theorem ext_parts {p q : ℍ[ℝ]}
    (hcomplex : complexPart p = complexPart q)
    (hj : jPart p = jPart q) : p = q := by
  rw [eq_complexPart_add_jPart_mul_j p, eq_complexPart_add_jPart_mul_j q, hcomplex, hj]

/-- Equality of quaternions is equivalent to equality of both complex components. -/
theorem eq_iff_parts_eq {p q : ℍ[ℝ]} :
    p = q ↔ complexPart p = complexPart q ∧ jPart p = jPart q := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hcomplex, hweird⟩
    exact ext_parts hcomplex hweird

/-- The pair of complex component maps loses no quaternionic information. -/
theorem components_injective :
    Function.Injective (fun q : ℍ[ℝ] ↦ (complexPart q, jPart q)) := by
  intro p q h
  exact ext_parts (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Moving an embedded complex scalar past `j` conjugates it. -/
theorem j_mul_coeComplex (z : ℂ) :
    j * (z : ℍ[ℝ]) = ((star z : ℂ) : ℍ[ℝ]) * j := by
  apply QuaternionAlgebra.ext <;> simp

/-- Complex component of a quaternion product (Equation 41, first identity). -/
@[simp]
theorem complexPart_mul (p q : ℍ[ℝ]) :
    complexPart (p * q) =
      complexPart p * complexPart q - jPart p * star (jPart q) := by
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- The `j`-component of a quaternion product (Equation 41, second identity). -/
@[simp]
theorem jPart_mul (p q : ℍ[ℝ]) :
    jPart (p * q) =
      complexPart p * jPart q + jPart p * star (complexPart q) := by
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- Quaternion conjugation conjugates the complex component. -/
@[simp]
theorem complexPart_star (q : ℍ[ℝ]) :
    complexPart (star q) = star (complexPart q) := by
  apply Complex.ext <;> simp

/-- Quaternion conjugation negates, but does not complex-conjugate, the `j`-component. -/
@[simp]
theorem jPart_star (q : ℍ[ℝ]) :
    jPart (star q) = -jPart q := by
  apply Complex.ext <;> simp

/-- Quaternion norm square is the sum of the two complex norm squares. -/
theorem normSq_eq_complexPart_add_jPart (q : ℍ[ℝ]) :
    _root_.Quaternion.normSq q =
      Complex.normSq (complexPart q) + Complex.normSq (jPart q) := by
  rw [_root_.Quaternion.normSq_def']
  simp only [Complex.normSq_apply, complexPart_re, complexPart_im, jPart_re,
    jPart_im]
  ring

/-! The following exact identities are executable sanity checks for signs and order. -/

@[simp] theorem i_mul_i : i * i = (-1 : ℍ[ℝ]) := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem j_mul_j : j * j = (-1 : ℍ[ℝ]) := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem k_mul_k : k * k = (-1 : ℍ[ℝ]) := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem i_mul_j : i * j = k := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem j_mul_i : j * i = -k := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem j_mul_k : j * k = i := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem k_mul_j : k * j = -i := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem k_mul_i : k * i = j := by
  apply QuaternionAlgebra.ext <;> norm_num

@[simp] theorem i_mul_k : i * k = -j := by
  apply QuaternionAlgebra.ext <;> norm_num

/-- Hamilton's ordered product `i*j*k` is `-1`. -/
@[simp]
theorem i_mul_j_mul_k : i * j * k = (-1 : ℍ[ℝ]) := by
  rw [i_mul_j, k_mul_k]

end QuaternionicComputing.Quaternion
