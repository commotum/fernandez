module

public import Mathlib.Analysis.Quaternion

/-!
# Baseline smoke theorem

This module checks the pinned mathlib quaternion and star APIs.  Substantive
paper infrastructure is introduced in later modules rather than hidden here.
-/

@[expose] public section

open scoped Quaternion

namespace QuaternionicComputing

/-- Quaternion conjugation is involutive in the scalar type used by the paper. -/
theorem quaternion_star_star (q : ℍ[ℝ]) : star (star q) = q :=
  star_star q

end QuaternionicComputing
