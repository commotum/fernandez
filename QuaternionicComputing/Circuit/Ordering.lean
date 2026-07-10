module

public import QuaternionicComputing.Circuit.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Data.Finset.Card

/-!
# Legal schedules for finite ordered circuits

This file separates a circuit's finite family of gate occurrences from the
chronological order in which those occurrences are executed.  A
`LegalSchedule` lists every identifier exactly once and carries an explicit
certificate that the list respects a supplied precedence relation.

The relation is deliberately not assumed to be transitive or acyclic.  Those
properties are unnecessary for using a schedule; existence of a
`LegalSchedule` is itself the relevant consistency certificate.

Schedule independence is not true for arbitrary gates.  The theorem below
therefore assumes explicitly that all distinct global gate denotations
commute.  Its proof works with the reversed list used by `OrderedCircuit.eval`,
so the chronological/product-order convention remains visible.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace QuaternionicComputing.Circuit

universe u v w

/--
A chronological enumeration of a finite identifier type that respects a
supplied precedence relation.

`nodup` and `complete` say that every identifier occurs exactly once.
`respects` says that a required predecessor has a strictly smaller
chronological index than its successor.
-/
structure LegalSchedule (ι : Type u) [Fintype ι] [DecidableEq ι]
    (precedes : ι → ι → Prop) where
  /-- Gate-occurrence identifiers in chronological order. -/
  order : List ι
  /-- No gate occurrence is scheduled twice. -/
  nodup : order.Nodup
  /-- Every gate occurrence is scheduled. -/
  complete : ∀ i, i ∈ order
  /-- Every supplied precedence constraint is respected chronologically. -/
  respects : ∀ {i j}, precedes i j → order.idxOf i < order.idxOf j

namespace LegalSchedule

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {precedes : ι → ι → Prop}

/-- Every identifier occurs in the chronological list of a legal schedule. -/
@[simp]
theorem mem_order (s : LegalSchedule ι precedes) (i : ι) :
    i ∈ s.order :=
  s.complete i

/-- A legal schedule's chronological list has the full finite identifier set. -/
@[simp]
theorem order_toFinset (s : LegalSchedule ι precedes) :
    s.order.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  simp [s.complete i]

/-- A legal schedule contains exactly one entry per identifier. -/
@[simp]
theorem length_order (s : LegalSchedule ι precedes) :
    s.order.length = Fintype.card ι := by
  calc
    s.order.length = s.order.toFinset.card :=
      (List.toFinset_card_of_nodup s.nodup).symm
    _ = Finset.univ.card := by rw [s.order_toFinset]
    _ = Fintype.card ι := Finset.card_univ

/-- Any two legal schedules enumerate the same identifiers. -/
theorem order_perm (s t : LegalSchedule ι precedes) :
    s.order.Perm t.order := by
  apply List.perm_of_nodup_nodup_toFinset_eq s.nodup t.nodup
  rw [s.order_toFinset, t.order_toFinset]

/-- The stored precedence certificate, exposed under a descriptive theorem name. -/
theorem index_lt_index_of_precedes (s : LegalSchedule ι precedes)
    {i j : ι} (hij : precedes i j) :
    s.order.idxOf i < s.order.idxOf j :=
  s.respects hij

/--
Instantiate a schedule with a gate occurrence for each identifier.  The result
is an `OrderedCircuit`, still in chronological order.
-/
def scheduledCircuit {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s : LegalSchedule ι precedes) (gates : ι → PlacedGate R W) :
    OrderedCircuit R W :=
  s.order.map gates

/-- Evaluate a scheduled circuit through the public chronological evaluator. -/
def scheduledEval {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s : LegalSchedule ι precedes) (gates : ι → PlacedGate R W) :
    Matrix (BitBasis W) (BitBasis W) R :=
  OrderedCircuit.eval (s.scheduledCircuit gates)

/-- Every indexed gate occurrence appears in the instantiated circuit. -/
@[simp]
theorem gate_mem_scheduledCircuit {R : Type v} {W : Type w}
    [Semiring R] [Fintype W] (s : LegalSchedule ι precedes)
    (gates : ι → PlacedGate R W) (i : ι) :
    gates i ∈ s.scheduledCircuit gates := by
  exact List.mem_map.mpr ⟨i, s.complete i, rfl⟩

/--
The gates in an instantiated circuit are exactly the images of its occurrence
identifiers.  This statement does not require the gate assignment to be
injective.
-/
theorem mem_scheduledCircuit_iff {R : Type v} {W : Type w}
    [Semiring R] [Fintype W] (s : LegalSchedule ι precedes)
    (gates : ι → PlacedGate R W) (g : PlacedGate R W) :
    g ∈ s.scheduledCircuit gates ↔ ∃ i, gates i = g := by
  constructor
  · intro hg
    simpa [scheduledCircuit] using hg
  · rintro ⟨i, rfl⟩
    exact s.gate_mem_scheduledCircuit gates i

/-- Scheduling preserves the number of gate occurrences. -/
@[simp]
theorem gateCount_scheduledCircuit {R : Type v} {W : Type w}
    [Semiring R] [Fintype W] (s : LegalSchedule ι precedes)
    (gates : ι → PlacedGate R W) :
    OrderedCircuit.gateCount (s.scheduledCircuit gates) = Fintype.card ι := by
  simp [scheduledCircuit, OrderedCircuit.gateCount, s.length_order]

/-- Instantiating two legal schedules produces permutation-equivalent circuits. -/
theorem scheduledCircuit_perm {R : Type v} {W : Type w}
    [Semiring R] [Fintype W] (s t : LegalSchedule ι precedes)
    (gates : ι → PlacedGate R W) :
    (s.scheduledCircuit gates).Perm (t.scheduledCircuit gates) := by
  exact (s.order_perm t).map gates

/--
Any two legal schedules evaluate identically when all distinct global gate
denotations commute.

The hypothesis is on occurrence identifiers, rather than gate values, so it
also covers assignments in which two identifiers denote the same placed gate.
The proof transports the schedule permutation to the *reversed* denotation
lists used by `OrderedCircuit.eval`, then applies `List.Perm.prod_eq'`.
-/
theorem scheduledEval_eq_of_pairwise_commute
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s t : LegalSchedule ι precedes) (gates : ι → PlacedGate R W)
    (hcomm : Pairwise fun i j : ι =>
      Commute (gates i).denote (gates j).denote) :
    s.scheduledEval gates = t.scheduledEval gates := by
  let denoteAt := fun i : ι => (gates i).denote
  have hreverse : s.order.reverse.Perm t.order.reverse :=
    s.order.reverse_perm.trans ((s.order_perm t).trans t.order.reverse_perm.symm)
  have hfactorPerm :
      (s.order.reverse.map denoteAt).Perm (t.order.reverse.map denoteAt) :=
    hreverse.map denoteAt
  have hidentifierCommute :
      s.order.reverse.Pairwise
        (fun i j => Commute (denoteAt i) (denoteAt j)) := by
    apply (List.nodup_reverse.mpr s.nodup).pairwise_of_forall_ne
    intro i _ j _ hij
    exact hcomm hij
  have hfactorCommute :
      (s.order.reverse.map denoteAt).Pairwise Commute := by
    rw [List.pairwise_map]
    exact hidentifierCommute
  unfold scheduledEval scheduledCircuit OrderedCircuit.eval
  rw [← List.map_reverse, ← List.map_reverse]
  simpa only [List.map_map, Function.comp_def, denoteAt] using
    hfactorPerm.prod_eq' hfactorCommute

end LegalSchedule

end QuaternionicComputing.Circuit
