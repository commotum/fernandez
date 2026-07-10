module

public import QuaternionicComputing.Circuit.Basic
public import QuaternionicComputing.Circuit.AddedWire

/-!
# Generic finite-circuit width and local-arity costs

This module records resource facts that depend only on the abstract placed
gate and chronological-list APIs.  `ArityBound d c` says that every gate in
`c` acts on at most `d` local wires.  `maxLocalArity c` is the largest local
arity, with the explicit convention `maxLocalArity [] = 0`.

The map theorems are parameterized by an arbitrary gate translation whose
local arity increases by exactly one.  They therefore apply to both central
embeddings without importing either embedding-specific circuit leaf.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

/-- Adding the distinguished wire increases global wire cardinality by exactly one. -/
@[simp]
theorem card_addedWire (W : Type*) [Fintype W] :
    Fintype.card (AddedWire W) = Fintype.card W + 1 := by
  simp [AddedWire, Nat.add_comm]

namespace OrderedCircuit

universe u v u' v'

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/-- Every gate in `c` acts on at most `d` local wires. -/
def ArityBound (d : ℕ) (c : OrderedCircuit R W) : Prop :=
  ∀ g ∈ c, g.localArity ≤ d

/-- The membership formulation of a circuit arity bound. -/
theorem arityBound_iff {d : ℕ} {c : OrderedCircuit R W} :
    ArityBound d c ↔ ∀ g ∈ c, g.localArity ≤ d :=
  Iff.rfl

@[simp]
theorem arityBound_nil (d : ℕ) :
    ArityBound d ([] : OrderedCircuit R W) := by
  simp [ArityBound]

@[simp]
theorem arityBound_cons {d : ℕ} {g : PlacedGate R W}
    {c : OrderedCircuit R W} :
    ArityBound d (g :: c) ↔ g.localArity ≤ d ∧ ArityBound d c := by
  simp [ArityBound]

/-- An arity bound remains valid after increasing its numerical bound. -/
theorem ArityBound.mono {d e : ℕ} {c : OrderedCircuit R W}
    (hc : ArityBound d c) (hde : d ≤ e) : ArityBound e c := by
  intro g hg
  exact (hc g hg).trans hde

/--
The largest local arity in a circuit.  The empty circuit has maximum zero.
-/
def maxLocalArity : OrderedCircuit R W → ℕ
  | [] => 0
  | g :: c => max g.localArity (maxLocalArity c)

@[simp]
theorem maxLocalArity_nil :
    maxLocalArity ([] : OrderedCircuit R W) = 0 :=
  rfl

@[simp]
theorem maxLocalArity_cons (g : PlacedGate R W) (c : OrderedCircuit R W) :
    maxLocalArity (g :: c) = max g.localArity (maxLocalArity c) :=
  rfl

/-- A numerical upper bound on the maximum is exactly a gatewise arity bound. -/
@[simp]
theorem maxLocalArity_le_iff {d : ℕ} {c : OrderedCircuit R W} :
    maxLocalArity c ≤ d ↔ ArityBound d c := by
  induction c with
  | nil => simp
  | cons g c ih => simp [ih]

/-- Gatewise boundedness can equivalently be read from the maximum. -/
theorem arityBound_iff_maxLocalArity_le {d : ℕ} {c : OrderedCircuit R W} :
    ArityBound d c ↔ maxLocalArity c ≤ d :=
  maxLocalArity_le_iff.symm

/-- Every circuit is bounded by its own maximum local arity. -/
theorem arityBound_maxLocalArity (c : OrderedCircuit R W) :
    ArityBound (maxLocalArity c) c :=
  maxLocalArity_le_iff.mp le_rfl

/-- Every member gate's local arity is at most the circuit maximum. -/
theorem localArity_le_maxLocalArity {g : PlacedGate R W}
    {c : OrderedCircuit R W} (hg : g ∈ c) :
    g.localArity ≤ maxLocalArity c :=
  arityBound_maxLocalArity c g hg

section Map

variable {S : Type u'} {V : Type v'} [Semiring S] [Fintype V]

/--
Exact provenance for a gate in a mapped circuit, including its translated
local arity.
-/
theorem mem_map_arity_provenance
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    (c : OrderedCircuit R W) (k : PlacedGate S V) :
    k ∈ c.map f ↔
      ∃ g, g ∈ c ∧ f g = k ∧ k.localArity = g.localArity + 1 := by
  constructor
  · intro hk
    rcases List.mem_map.mp hk with ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl, hArity g⟩
  · rintro ⟨g, hg, rfl, _⟩
    exact List.mem_map.mpr ⟨g, hg, rfl⟩

/-- An exact per-gate `+1` translation sends an arity bound `d` to `d + 1`. -/
theorem arityBound_map_add_one
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    {d : ℕ} {c : OrderedCircuit R W} (hc : ArityBound d c) :
    ArityBound (d + 1) (c.map f) := by
  intro k hk
  rcases List.mem_map.mp hk with ⟨g, hg, rfl⟩
  rw [hArity]
  exact Nat.add_le_add_right (hc g hg) 1

/-- Exact `+1` translation reflects as well as preserves the corresponding bound. -/
theorem arityBound_map_add_one_iff
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    {d : ℕ} {c : OrderedCircuit R W} :
    ArityBound (d + 1) (c.map f) ↔ ArityBound d c := by
  constructor
  · intro hc g hg
    have hfg := hc (f g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    simpa [hArity g] using hfg
  · exact arityBound_map_add_one f hArity

/-- The translated maximum is always at most the source maximum plus one. -/
theorem maxLocalArity_map_le_add_one
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    (c : OrderedCircuit R W) :
    maxLocalArity (c.map f) ≤ maxLocalArity c + 1 := by
  apply maxLocalArity_le_iff.mpr
  exact arityBound_map_add_one f hArity (arityBound_maxLocalArity c)

/--
For a nonempty circuit, exact per-gate `+1` translation increases the maximum
local arity by exactly one.  The nonempty hypothesis is necessary because
both empty-circuit maxima are zero.
-/
theorem maxLocalArity_map_eq_add_one_of_nonempty
    (f : PlacedGate R W → PlacedGate S V)
    (hArity : ∀ g, (f g).localArity = g.localArity + 1)
    {c : OrderedCircuit R W} (hc : c ≠ []) :
    maxLocalArity (c.map f) = maxLocalArity c + 1 := by
  induction c with
  | nil => exact (hc rfl).elim
  | cons g c ih =>
      cases c with
      | nil => simp [hArity]
      | cons k c =>
          have htail : k :: c ≠ [] := List.cons_ne_nil k c
          change max (f g).localArity (maxLocalArity ((k :: c).map f)) =
            max g.localArity (maxLocalArity (k :: c)) + 1
          rw [hArity g, ih htail, max_add_add_right]

end Map

end OrderedCircuit

end QuaternionicComputing.Circuit
