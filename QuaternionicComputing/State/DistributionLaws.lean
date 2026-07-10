module

public import QuaternionicComputing.State.Distribution

/-!
# Functorial laws for finite deterministic postprocessing

This narrow leaf proves the identity and composition laws for deterministic
pushforwards of finite distributions.  Composition is ordered as classical
postprocessing: first apply `f`, then apply `g`, which is the map `g ∘ f`.

These are exact equalities of packaged finite distributions.  They make no
claim about amplitude states, rays, channels, runtime, or approximation.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace QuaternionicComputing.State.FiniteDistribution

universe u v w

variable {I : Type u} {J : Type v} {K : Type w}
variable [Fintype I] [Fintype J] [Fintype K]

/-- Pushing a finite distribution through the identity map changes nothing. -/
@[simp]
theorem pushforward_id (mu : FiniteDistribution I) :
    mu.pushforward id = mu := by
  classical
  apply ext
  intro x
  simp only [pushforward_weight, id_eq]
  change (∑ y ∈ Finset.univ.filter (fun y : I ↦ y = x), mu.weight y) =
    mu.weight x
  have hfilter : Finset.univ.filter (fun y : I ↦ y = x) = {x} := by
    ext y
    simp
  rw [hfilter]
  simp

/--
Deterministic pushforwards compose in chronological order: first `f`, then
`g`, equals one pushforward through `g ∘ f`.
-/
theorem pushforward_comp (mu : FiniteDistribution I)
    (f : I → J) (g : J → K) :
    mu.pushforward (g ∘ f) = (mu.pushforward f).pushforward g := by
  classical
  apply ext
  intro z
  simp only [pushforward_weight]
  let S : Finset I := Finset.univ.filter fun x ↦ g (f x) = z
  calc
    (∑ x with (g ∘ f) x = z, mu.weight x) = ∑ x ∈ S, mu.weight x := by
      simp [S, Function.comp_apply]
    _ = ∑ y, ∑ x ∈ S with f x = y, mu.weight x :=
      (Finset.sum_fiberwise S f mu.weight).symm
    _ = ∑ y with g y = z, ∑ x with f x = y, mu.weight x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z
      · have hfilter : S.filter (fun x ↦ f x = y) =
            Finset.univ.filter (fun x ↦ f x = y) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
          constructor
          · exact fun hx ↦ hx.2
          · intro hxy
            exact ⟨by simpa [hxy] using hy, hxy⟩
        rw [hfilter]
        simp [hy]
      · have hfilter : S.filter (fun x ↦ f x = y) = ∅ := by
          ext x
          constructor
          · intro hx
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have : g y = z := by simpa [hx.2] using hx.1
            exact (hy this).elim
          · intro hx
            simp at hx
        rw [hfilter]
        simp [hy]

end QuaternionicComputing.State.FiniteDistribution
