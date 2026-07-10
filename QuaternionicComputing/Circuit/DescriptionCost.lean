module

public import QuaternionicComputing.Circuit.Cost
public import Mathlib.Data.Nat.Log

/-!
# Dense finite-circuit description costs

This file counts *scalar-entry slots* in explicit dense local gate matrices.
A gate on `d` wires has a `2^d × 2^d` matrix and therefore exactly `4^d`
slots.  This is a structural description measure, not a bit-complexity or
runtime model: encoding one scalar, sharing/compressing matrices, arithmetic,
and synthesis into a primitive gate library remain separate costs.

The final additive-work bound makes the missing runtime premise explicit.  If
translating every occurrence costs at most `K` in a chosen external model,
then translating the chronological list costs at most `gateCount * K`.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

universe u v u' v'

namespace PlacedGate

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/-- Number of scalar-entry slots in the gate's explicit dense local matrix. -/
def denseEntrySlots (g : PlacedGate R W) : ℕ :=
  g.localBasisCard * g.localBasisCard

/-- A `d`-wire dense local matrix has exactly `4^d` scalar-entry slots. -/
theorem denseEntrySlots_eq_four_pow (g : PlacedGate R W) :
    g.denseEntrySlots = 4 ^ g.localArity := by
  rw [denseEntrySlots, g.localBasisCard_eq_two_pow]
  calc
    2 ^ g.localArity * 2 ^ g.localArity =
        (2 * 2) ^ g.localArity := (Nat.mul_pow 2 2 g.localArity).symm
    _ = 4 ^ g.localArity := by norm_num

/-- Exact dense-slot factor for a gate translation that adds one local wire. -/
theorem denseEntrySlots_eq_four_mul_of_arity_eq_add_one
    {S : Type u'} {V : Type v'} [Semiring S] [Fintype V]
    (g : PlacedGate R W) (k : PlacedGate S V)
    (hArity : k.localArity = g.localArity + 1) :
    k.denseEntrySlots = 4 * g.denseEntrySlots := by
  rw [k.denseEntrySlots_eq_four_pow, g.denseEntrySlots_eq_four_pow, hArity,
    pow_succ]
  omega

/-- Exact dense-slot factor for a gate translation that adds two local wires. -/
theorem denseEntrySlots_eq_sixteen_mul_of_arity_eq_add_two
    {S : Type u'} {V : Type v'} [Semiring S] [Fintype V]
    (g : PlacedGate R W) (k : PlacedGate S V)
    (hArity : k.localArity = g.localArity + 2) :
    k.denseEntrySlots = 16 * g.denseEntrySlots := by
  rw [k.denseEntrySlots_eq_four_pow, g.denseEntrySlots_eq_four_pow, hArity]
  simp only [pow_add, pow_two]
  norm_num
  omega

/-- A finite bound on dense slots gives the corresponding exact base-four log bound on arity. -/
theorem localArity_le_log_four_of_denseEntrySlots_le
    (g : PlacedGate R W) {N : ℕ} (h : g.denseEntrySlots ≤ N) :
    g.localArity ≤ Nat.log 4 N := by
  apply Nat.le_log_of_pow_le (by norm_num)
  simpa [g.denseEntrySlots_eq_four_pow] using h

end PlacedGate

namespace OrderedCircuit

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/-- Total scalar-entry slots in all explicit dense local gate matrices. -/
def totalDenseEntrySlots (c : OrderedCircuit R W) : ℕ :=
  (c.map PlacedGate.denseEntrySlots).sum

@[simp]
theorem totalDenseEntrySlots_nil :
    totalDenseEntrySlots ([] : OrderedCircuit R W) = 0 :=
  rfl

@[simp]
theorem totalDenseEntrySlots_cons (g : PlacedGate R W)
    (c : OrderedCircuit R W) :
    totalDenseEntrySlots (g :: c) =
      g.denseEntrySlots + totalDenseEntrySlots c :=
  rfl

/--
Total work for a gatewise list translation in a separately supplied per-gate
cost model.  This definition does not assert how `gateWork` is obtained.
-/
def translationWork (gateWork : PlacedGate R W → ℕ)
    (c : OrderedCircuit R W) : ℕ :=
  (c.map gateWork).sum

/-- Bounded work per occurrence gives the explicit finite linear work bound. -/
theorem translationWork_le_gateCount_mul
    (gateWork : PlacedGate R W → ℕ) (c : OrderedCircuit R W) (K : ℕ)
    (hwork : ∀ g ∈ c, gateWork g ≤ K) :
    translationWork gateWork c ≤ c.gateCount * K := by
  unfold translationWork OrderedCircuit.gateCount
  calc
    (c.map gateWork).sum ≤ (c.map fun _ => K).sum :=
      List.sum_le_sum hwork
    _ = c.length * K := by simp

/-- A `d`-arity bound gives an explicit dense-description slot bound. -/
theorem totalDenseEntrySlots_le_gateCount_mul_four_pow
    {d : ℕ} {c : OrderedCircuit R W} (hc : c.ArityBound d) :
    c.totalDenseEntrySlots ≤ c.gateCount * 4 ^ d := by
  exact translationWork_le_gateCount_mul PlacedGate.denseEntrySlots c (4 ^ d)
    (fun g hg => by
      rw [g.denseEntrySlots_eq_four_pow]
      exact Nat.pow_le_pow_right (by norm_num) (hc g hg))

section Map

variable {S : Type u'} {V : Type v'} [Semiring S] [Fintype V]

/-- Exact factor four in total dense slots for a gatewise `+1` translation. -/
theorem totalDenseEntrySlots_map_eq_four_mul
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    (c : OrderedCircuit R W) :
    totalDenseEntrySlots (c.map f) = 4 * c.totalDenseEntrySlots := by
  induction c with
  | nil => simp
  | cons g c ih =>
      rw [List.map_cons, totalDenseEntrySlots_cons, totalDenseEntrySlots_cons,
        PlacedGate.denseEntrySlots_eq_four_mul_of_arity_eq_add_one
          g (f g) (hArity g), ih, Nat.mul_add]

/-- Exact factor sixteen in total dense slots for a gatewise `+2` translation. -/
theorem totalDenseEntrySlots_map_eq_sixteen_mul
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 2)
    (c : OrderedCircuit R W) :
    totalDenseEntrySlots (c.map f) = 16 * c.totalDenseEntrySlots := by
  induction c with
  | nil => simp
  | cons g c ih =>
      rw [List.map_cons, totalDenseEntrySlots_cons, totalDenseEntrySlots_cons,
        PlacedGate.denseEntrySlots_eq_sixteen_mul_of_arity_eq_add_two
          g (f g) (hArity g), ih, Nat.mul_add]

end Map

end OrderedCircuit

end QuaternionicComputing.Circuit
