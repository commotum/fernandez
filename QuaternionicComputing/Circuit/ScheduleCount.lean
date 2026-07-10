module

public import QuaternionicComputing.Circuit.Ordering
public import Mathlib.Data.List.Permutation

/-!
# Counting unconstrained finite schedules

This file enumerates every chronological order of a finite gate-identifier
type.  The canonical identifier list is `Finset.univ.toList`, and the full
enumeration is its list of permutations.  Because the canonical list has no
duplicates, the enumeration itself has no duplicates and has exactly
`(Fintype.card ι)!` entries.

Every enumerated order is a `LegalSchedule` for the empty precedence relation.
Conversely, the chronological list of a legal schedule for any precedence
relation occurs in the same all-orders enumeration.  Thus the factorial is an
exact count only in the unconstrained case; no claim is made that a general
precedence relation admits that many legal orders.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit

universe u

/-- A canonical duplicate-free list containing every finite identifier. -/
def canonicalIdentifierOrder (ι : Type u) [Fintype ι] : List ι :=
  Finset.univ.toList

/-- Every identifier occurs in the canonical identifier list. -/
@[simp]
theorem mem_canonicalIdentifierOrder {ι : Type u} [Fintype ι]
    (i : ι) :
    i ∈ canonicalIdentifierOrder ι := by
  simp [canonicalIdentifierOrder]

/-- The canonical identifier list contains no duplicate identifiers. -/
theorem nodup_canonicalIdentifierOrder (ι : Type u) [Fintype ι] :
    (canonicalIdentifierOrder ι).Nodup := by
  exact Finset.nodup_toList Finset.univ

/-- Converting the canonical identifier list back to a finset gives `univ`. -/
@[simp]
theorem canonicalIdentifierOrder_toFinset (ι : Type u) [Fintype ι]
    [DecidableEq ι] :
    (canonicalIdentifierOrder ι).toFinset = Finset.univ := by
  simp [canonicalIdentifierOrder]

/-- The canonical identifier list has one entry per element of its type. -/
@[simp]
theorem length_canonicalIdentifierOrder (ι : Type u) [Fintype ι] :
    (canonicalIdentifierOrder ι).length = Fintype.card ι := by
  simp [canonicalIdentifierOrder]

/-- Every chronological order of a finite identifier type, listed once. -/
def allChronologicalOrders (ι : Type u) [Fintype ι] : List (List ι) :=
  (canonicalIdentifierOrder ι).permutations

/-- Membership in `allChronologicalOrders` is exactly permutation of the base list. -/
@[simp]
theorem mem_allChronologicalOrders_iff_perm {ι : Type u} [Fintype ι]
    {order : List ι} :
    order ∈ allChronologicalOrders ι ↔
      order.Perm (canonicalIdentifierOrder ι) := by
  simp [allChronologicalOrders]

/--
Membership in `allChronologicalOrders` is exactly duplicate-free completeness.
-/
theorem mem_allChronologicalOrders_iff {ι : Type u} [Fintype ι]
    {order : List ι} :
    order ∈ allChronologicalOrders ι ↔
      order.Nodup ∧ ∀ i, i ∈ order := by
  classical
  constructor
  · intro horder
    have hperm := mem_allChronologicalOrders_iff_perm.mp horder
    refine ⟨hperm.nodup_iff.mpr (nodup_canonicalIdentifierOrder ι), ?_⟩
    intro i
    exact hperm.mem_iff.mpr (mem_canonicalIdentifierOrder i)
  · rintro ⟨hnodup, hcomplete⟩
    apply mem_allChronologicalOrders_iff_perm.mpr
    apply List.perm_of_nodup_nodup_toFinset_eq hnodup
      (nodup_canonicalIdentifierOrder ι)
    rw [canonicalIdentifierOrder_toFinset]
    exact Finset.eq_univ_of_forall fun i ↦ by
      simpa using hcomplete i

/-- The all-orders enumeration contains no duplicate chronological lists. -/
theorem nodup_allChronologicalOrders (ι : Type u) [Fintype ι] :
    (allChronologicalOrders ι).Nodup := by
  exact List.nodup_permutations _ (nodup_canonicalIdentifierOrder ι)

/-- The number of chronological orders of an unconstrained finite type is factorial. -/
@[simp]
theorem length_allChronologicalOrders (ι : Type u) [Fintype ι] :
    (allChronologicalOrders ι).length = Nat.factorial (Fintype.card ι) := by
  rw [allChronologicalOrders, List.length_permutations,
    length_canonicalIdentifierOrder]

/--
Turn an enumerated order into a legal schedule for the empty precedence
relation.
-/
def emptyLegalScheduleOfMem {ι : Type u} [Fintype ι] [DecidableEq ι]
    {order : List ι} (horder : order ∈ allChronologicalOrders ι) :
    LegalSchedule ι (fun _ _ : ι ↦ False) where
  order := order
  nodup := (mem_allChronologicalOrders_iff.mp horder).1
  complete := (mem_allChronologicalOrders_iff.mp horder).2
  respects := by
    intro i j hij
    exact hij.elim

/-- The empty-precedence schedule constructor retains its supplied order. -/
@[simp]
theorem emptyLegalScheduleOfMem_order {ι : Type u} [Fintype ι]
    [DecidableEq ι] {order : List ι}
    (horder : order ∈ allChronologicalOrders ι) :
    (emptyLegalScheduleOfMem horder).order = order :=
  rfl

namespace LegalSchedule

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {precedes : ι → ι → Prop}

/--
The order list of every legal schedule occurs in the all-orders enumeration.

Together with `length_allChronologicalOrders`, this supplies the general
factorial upper-bound enumeration without counting proof-bearing schedule
structures and without asserting that every enumerated order respects
`precedes`.
-/
theorem order_mem_allChronologicalOrders (s : LegalSchedule ι precedes) :
    s.order ∈ allChronologicalOrders ι := by
  exact mem_allChronologicalOrders_iff.mpr ⟨s.nodup, s.complete⟩

end LegalSchedule

/--
An order is enumerated if and only if it underlies an empty-precedence legal
schedule.
-/
theorem mem_allChronologicalOrders_iff_exists_emptyLegalSchedule
    {ι : Type u} [Fintype ι] [DecidableEq ι] {order : List ι} :
    order ∈ allChronologicalOrders ι ↔
      ∃ s : LegalSchedule ι (fun _ _ : ι ↦ False), s.order = order := by
  constructor
  · intro horder
    exact ⟨emptyLegalScheduleOfMem horder, rfl⟩
  · rintro ⟨s, rfl⟩
    exact s.order_mem_allChronologicalOrders

/-! ## A constrained two-identifier counterexample -/

namespace ScheduleCount.BoolChain

universe v w

/-- The strict Boolean chain with `false` required before `true`. -/
def precedes (i j : Bool) : Prop :=
  i = false ∧ j = true

/-- The nontrivial constraint in the strict Boolean chain. -/
theorem false_precedes_true : precedes false true :=
  ⟨rfl, rfl⟩

/-- The canonical legal schedule for the strict Boolean chain. -/
def schedule : LegalSchedule Bool precedes where
  order := [false, true]
  nodup := by simp
  complete := by
    intro i
    cases i <;> simp
  respects := by
    rintro i j ⟨rfl, rfl⟩
    simp

/-- The canonical Boolean-chain schedule has the expected chronological list. -/
@[simp]
theorem schedule_order : schedule.order = [false, true] :=
  rfl

/-- Every legal schedule for the strict Boolean chain has the canonical order. -/
theorem order_eq_schedule (s : LegalSchedule Bool precedes) :
    s.order = schedule.order := by
  have hperm : s.order.Perm [false, true] := by
    simpa using s.order_perm schedule
  rcases List.perm_pair.mp hperm with hforward | hreverse
  · simpa using hforward
  · have hlt := s.index_lt_index_of_precedes false_precedes_true
    rw [hreverse] at hlt
    simp at hlt

/-- Instantiating the unique Boolean-chain order gives the canonical circuit list. -/
theorem scheduledCircuit_eq_schedule
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s : LegalSchedule Bool precedes) (gates : Bool → PlacedGate R W) :
    s.scheduledCircuit gates = schedule.scheduledCircuit gates := by
  unfold LegalSchedule.scheduledCircuit
  rw [order_eq_schedule s]

/-- Instantiating the unique Boolean-chain order gives the canonical evaluation. -/
theorem scheduledEval_eq_schedule
    {R : Type v} {W : Type w} [Semiring R] [Fintype W]
    (s : LegalSchedule Bool precedes) (gates : Bool → PlacedGate R W) :
    s.scheduledEval gates = schedule.scheduledEval gates := by
  unfold LegalSchedule.scheduledEval
  rw [scheduledCircuit_eq_schedule s gates]

/-- The reverse Boolean order is one of the two unconstrained chronological orders. -/
theorem reverseOrder_mem_allChronologicalOrders :
    [true, false] ∈ allChronologicalOrders Bool := by
  apply mem_allChronologicalOrders_iff.mpr
  constructor
  · simp
  · intro i
    cases i <;> simp

/-- The reverse Boolean order cannot satisfy the strict-chain precedence constraint. -/
theorem reverseOrder_not_legal :
    ¬ ∃ s : LegalSchedule Bool precedes, s.order = [true, false] := by
  rintro ⟨s, hreverse⟩
  have hcanonical := order_eq_schedule s
  rw [hreverse] at hcanonical
  simp at hcanonical

end ScheduleCount.BoolChain

end QuaternionicComputing.Circuit
