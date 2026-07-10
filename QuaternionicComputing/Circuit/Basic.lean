module

public import QuaternionicComputing.Circuit.Placement
public import QuaternionicComputing.Scalar.Quaternion

/-!
# Placed gates and ordered finite circuits

A `PlacedGate R W` stores a finite local wire type, a finite complementary
wire type, an explicit split `Local ⊕ Complement ≃ W`, and only a local
matrix.  Its global matrix is *derived* by `place`; there is no independent
global operator field that could disagree with the support data.

An `OrderedCircuit` is a chronological list.  Thus `[g₁, …, gₛ]` means
that `g₁` acts first, and evaluation is the reverse chronological matrix
product `Gₛ * ⋯ * G₁`.
-/

@[expose] public noncomputable section

open scoped Matrix Quaternion

namespace QuaternionicComputing.Circuit

universe u v

/--
A finite local gate together with the explicit decomposition that places it
inside the global wire type `W`.

The finite structures are stored with the local and complementary types so a
heterogeneous list can contain gates of different arities and supports.
-/
structure PlacedGate (R : Type u) (W : Type v) [Semiring R] [Fintype W] where
  /-- The finite type enumerating wires on which the gate acts. -/
  Local : Type v
  /-- The finite type enumerating all global wires outside the gate. -/
  Complement : Type v
  /-- Finiteness data for the local wire type. -/
  localFintype : Fintype Local
  /-- Finiteness data for the complementary wire type. -/
  complementFintype : Fintype Complement
  /-- The local/complement decomposition of the global wire type. -/
  split : Local ⊕ Complement ≃ W
  /-- The matrix acting on local computational-basis assignments. -/
  localMatrix : Matrix (BitBasis Local) (BitBasis Local) R

namespace PlacedGate

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/-- Construct a placed gate from an explicit finite wire split. -/
def ofSplit {L K : Type v} [Fintype L] [Fintype K]
    (split : L ⊕ K ≃ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    PlacedGate R W where
  Local := L
  Complement := K
  localFintype := inferInstance
  complementFintype := inferInstance
  split := split
  localMatrix := U

/-- Construct a placed gate on the (possibly noncontiguous) range of a support injection. -/
def onSupport {L : Type v} [Fintype L] (support : L ↪ W)
    (U : Matrix (BitBasis L) (BitBasis L) R) : PlacedGate R W := by
  letI : Fintype (SupportComplement support) := Fintype.ofFinite _
  exact ofSplit (supportSplit support) U

/-- The injection of the stored local wires into the global wire type. -/
def localSupport (g : PlacedGate R W) : g.Local ↪ W where
  toFun l := g.split (Sum.inl l)
  inj' := g.split.injective.comp Sum.inl_injective

/-- The injection of the stored complementary wires into the global wire type. -/
def complementSupport (g : PlacedGate R W) : g.Complement ↪ W where
  toFun k := g.split (Sum.inr k)
  inj' := g.split.injective.comp Sum.inr_injective

@[simp]
theorem localSupport_apply (g : PlacedGate R W) (l : g.Local) :
    g.localSupport l = g.split (Sum.inl l) :=
  rfl

@[simp]
theorem complementSupport_apply (g : PlacedGate R W) (k : g.Complement) :
    g.complementSupport k = g.split (Sum.inr k) :=
  rfl

/-- The finite set of global wires on which the gate acts. -/
def support (g : PlacedGate R W) : Finset W := by
  letI := g.localFintype
  exact Finset.univ.map g.localSupport

/-- The gate's number of local wires. -/
def localArity (g : PlacedGate R W) : ℕ :=
  @Fintype.card g.Local g.localFintype

/-- The number of wires outside the gate's support. -/
def complementArity (g : PlacedGate R W) : ℕ :=
  @Fintype.card g.Complement g.complementFintype

/-- The number of local computational-basis labels. -/
def localBasisCard (g : PlacedGate R W) : ℕ := by
  letI := g.localFintype
  exact Fintype.card (BitBasis g.Local)

/-- The placed global matrix, derived from all of the stored locality data. -/
def denote (g : PlacedGate R W) : Matrix (BitBasis W) (BitBasis W) R := by
  letI := g.localFintype
  letI := g.complementFintype
  exact place g.split g.localMatrix

@[simp]
theorem denote_ofSplit {L K : Type v} [Fintype L] [Fintype K]
    (split : L ⊕ K ≃ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    (ofSplit split U).denote = place split U :=
  rfl

@[simp]
theorem localSupport_onSupport {L : Type v} [Fintype L]
    (chosen : L ↪ W) (U : Matrix (BitBasis L) (BitBasis L) R) (l : L) :
    (onSupport chosen U).localSupport l = chosen l := by
  letI : Fintype (SupportComplement chosen) := Fintype.ofFinite _
  change supportSplit chosen (Sum.inl l) = chosen l
  exact supportSplit_apply_inl chosen l

/-- `onSupport` has exactly the contextual semantics built from the supplied injection. -/
@[simp]
theorem denote_onSupport {L : Type v} [Fintype L]
    (chosen : L ↪ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    (onSupport chosen U).denote = placeOnSupport chosen U := by
  letI : Fintype (SupportComplement chosen) := Fintype.ofFinite _
  change (ofSplit (supportSplit chosen) U).denote = place (supportSplit chosen) U
  exact denote_ofSplit (supportSplit chosen) U

@[simp]
theorem localArity_ofSplit {L K : Type v} [Fintype L] [Fintype K]
    (split : L ⊕ K ≃ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    (ofSplit split U).localArity = Fintype.card L :=
  rfl

@[simp]
theorem complementArity_ofSplit {L K : Type v} [Fintype L] [Fintype K]
    (split : L ⊕ K ≃ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    (ofSplit split U).complementArity = Fintype.card K :=
  rfl

/-- Membership in a gate's finite support is characterized by its local-wire injection. -/
theorem mem_support_iff (g : PlacedGate R W) (w : W) :
    w ∈ g.support ↔ ∃ l : g.Local, g.localSupport l = w := by
  letI := g.localFintype
  simp [support]

/-- The support contains exactly `localArity` global wires. -/
@[simp]
theorem card_support (g : PlacedGate R W) :
    g.support.card = g.localArity := by
  letI := g.localFintype
  simp [support, localArity]

@[simp]
theorem support_onSupport {L : Type v} [Fintype L]
    (chosen : L ↪ W) (U : Matrix (BitBasis L) (BitBasis L) R) :
    (onSupport chosen U).support = Finset.univ.map chosen := by
  letI : Fintype (SupportComplement chosen) := Fintype.ofFinite _
  ext w
  rw [mem_support_iff]
  simp only [localSupport_onSupport]
  rfl

/-- Local and complementary arities add up to the global wire count. -/
theorem localArity_add_complementArity (g : PlacedGate R W) :
    g.localArity + g.complementArity = Fintype.card W := by
  letI := g.localFintype
  letI := g.complementFintype
  simpa [localArity, complementArity, Fintype.card_sum] using
    Fintype.card_congr g.split

/-- There are `2 ^ localArity` local computational-basis labels. -/
theorem localBasisCard_eq_two_pow (g : PlacedGate R W) :
    g.localBasisCard = 2 ^ g.localArity := by
  classical
  letI := g.localFintype
  change Fintype.card (g.Local → Bool) = 2 ^ Fintype.card g.Local
  rw [← Nat.card_eq_fintype_card, Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

section Star

variable [StarRing R]

/-- A placed gate is locally unitary when its stored local matrix is unitary. -/
def IsLocallyUnitary (g : PlacedGate R W) : Prop := by
  letI := g.localFintype
  exact g.localMatrix ∈ unitary (Matrix (BitBasis g.Local) (BitBasis g.Local) R)

/-- Local unitarity implies unitarity of the derived global matrix. -/
theorem denote_mem_unitary (g : PlacedGate R W) (hg : g.IsLocallyUnitary) :
    g.denote ∈ unitary (Matrix (BitBasis W) (BitBasis W) R) := by
  letI := g.localFintype
  letI := g.complementFintype
  exact place_mem_unitary g.split hg

end Star

end PlacedGate

/-- A chronological list of gates on the same global wire type. -/
abbrev OrderedCircuit (R : Type u) (W : Type v) [Semiring R] [Fintype W] :=
  List (PlacedGate R W)

namespace OrderedCircuit

variable {R : Type u} {W : Type v} [Semiring R] [Fintype W]

/--
Evaluate a chronological circuit in reverse chronological multiplication
order.  If `g₁` is at the head of the list, it acts first and therefore occurs
at the right of the resulting matrix product.
-/
def eval (c : OrderedCircuit R W) : Matrix (BitBasis W) (BitBasis W) R :=
  (c.reverse.map PlacedGate.denote).prod

/-- The evaluator is definitionally the product of the reversed semantic gate list. -/
theorem eval_eq_reverse_product (c : OrderedCircuit R W) :
    eval c = (c.reverse.map PlacedGate.denote).prod :=
  rfl

@[simp]
theorem eval_nil : eval ([] : OrderedCircuit R W) = 1 :=
  rfl

@[simp]
theorem eval_singleton (g : PlacedGate R W) :
    eval [g] = g.denote := by
  simp [eval]

/-- The head of a chronological circuit acts first, hence multiplies on the right. -/
@[simp]
theorem eval_cons (g : PlacedGate R W) (c : OrderedCircuit R W) :
    eval (g :: c) = eval c * g.denote := by
  simp [eval]

/-- Appending a later circuit places its product on the left. -/
@[simp]
theorem eval_append (c₁ c₂ : OrderedCircuit R W) :
    eval (c₁ ++ c₂) = eval c₂ * eval c₁ := by
  simp [eval]

/-- The number of gates, independent of their semantic placement. -/
def gateCount (c : OrderedCircuit R W) : ℕ :=
  c.length

@[simp]
theorem gateCount_nil : gateCount ([] : OrderedCircuit R W) = 0 :=
  rfl

@[simp]
theorem gateCount_cons (g : PlacedGate R W) (c : OrderedCircuit R W) :
    gateCount (g :: c) = gateCount c + 1 := by
  simp [gateCount, Nat.add_comm]

@[simp]
theorem gateCount_append (c₁ c₂ : OrderedCircuit R W) :
    gateCount (c₁ ++ c₂) = gateCount c₁ + gateCount c₂ := by
  simp [gateCount]

@[simp]
theorem gateCount_map {S : Type*} {V : Type*} [Semiring S] [Fintype V]
    (translate : PlacedGate R W → PlacedGate S V) (c : OrderedCircuit R W) :
    gateCount (c.map translate) = gateCount c := by
  simp [gateCount]

/-- Gatewise equality of denotations implies equality of circuit evaluation. -/
theorem eval_congr {c d : OrderedCircuit R W}
    (h : List.Forall₂ (fun g k ↦ g.denote = k.denote) c d) :
    eval c = eval d := by
  induction h with
  | nil => simp
  | cons hgate _ ih => simp [hgate, ih]

/--
Mapping gates commutes with evaluation whenever their denotations commute with
a supplied matrix monoid homomorphism.  This is the generic induction helper
used by whole-circuit translations in the simulation stage.
-/
theorem eval_map_of_denote_eq
    {S : Type*} {V : Type*} [Semiring S] [Fintype V]
    (F : Matrix (BitBasis W) (BitBasis W) R →*
      Matrix (BitBasis V) (BitBasis V) S)
    (translate : PlacedGate R W → PlacedGate S V)
    (htranslate : ∀ g, (translate g).denote = F g.denote)
    (c : OrderedCircuit R W) :
    eval (c.map translate) = F (eval c) := by
  induction c with
  | nil => simp
  | cons g c ih => simp [ih, htranslate, map_mul]

section Star

variable [StarRing R]

/-- Every gate in the circuit has a unitary stored local matrix. -/
def IsLocallyUnitary (c : OrderedCircuit R W) : Prop :=
  ∀ g ∈ c, g.IsLocallyUnitary

@[simp]
theorem isLocallyUnitary_nil :
    IsLocallyUnitary ([] : OrderedCircuit R W) := by
  simp [IsLocallyUnitary]

@[simp]
theorem isLocallyUnitary_cons {g : PlacedGate R W} {c : OrderedCircuit R W} :
    IsLocallyUnitary (g :: c) ↔ g.IsLocallyUnitary ∧ IsLocallyUnitary c := by
  simp [IsLocallyUnitary]

/-- A circuit of locally unitary gates evaluates to a unitary global matrix. -/
theorem eval_mem_unitary {c : OrderedCircuit R W} (hc : c.IsLocallyUnitary) :
    eval c ∈ unitary (Matrix (BitBasis W) (BitBasis W) R) := by
  induction c with
  | nil => exact (unitary (Matrix (BitBasis W) (BitBasis W) R)).one_mem
  | cons g c ih =>
      have hcTail : IsLocallyUnitary c :=
        fun k hk ↦ hc k (List.mem_cons_of_mem g hk)
      have hg : PlacedGate.IsLocallyUnitary g := hc g (by simp)
      have hTail := ih hcTail
      have hHead := g.denote_mem_unitary hg
      rw [eval_cons]
      exact (unitary (Matrix (BitBasis W) (BitBasis W) R)).mul_mem hTail hHead

end Star

end OrderedCircuit

/-! ## Public order-sensitivity sanity check -/

namespace OrderSanity

open QuaternionicComputing.Quaternion

/-- The unique split of a zero-wire local system and zero-wire complement. -/
def emptySplit : Empty ⊕ Empty ≃ Empty :=
  Equiv.sumEmpty Empty Empty

/-- A zero-wire local matrix whose unique entry is the quaternionic unit `i`. -/
def iLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℍ[ℝ] :=
  fun _ _ ↦ i

/-- A zero-wire local matrix whose unique entry is the quaternionic unit `j`. -/
def jLocal : Matrix (BitBasis Empty) (BitBasis Empty) ℍ[ℝ] :=
  fun _ _ ↦ j

/-- The placed `i` gate used by the order sanity check. -/
def iGate : PlacedGate ℍ[ℝ] Empty :=
  PlacedGate.ofSplit emptySplit iLocal

/-- The placed `j` gate used by the order sanity check. -/
def jGate : PlacedGate ℍ[ℝ] Empty :=
  PlacedGate.ofSplit emptySplit jLocal

/-- The two stored local matrices genuinely fail to commute. -/
theorem jLocal_mul_iLocal_ne_iLocal_mul_jLocal :
    jLocal * iLocal ≠ iLocal * jLocal := by
  intro h
  let z : BitBasis Empty := fun x ↦ nomatch x
  have hz := congrFun (congrFun h z) z
  have hk : (-k : ℍ[ℝ]) = k := by
    simpa [iLocal, jLocal, Matrix.mul_apply] using hz
  have hkCoord := congrArg QuaternionAlgebra.imK hk
  norm_num at hkCoord

/-- The corresponding placed global matrices genuinely fail to commute. -/
theorem jGate_denote_mul_iGate_denote_ne_iGate_denote_mul_jGate_denote :
    jGate.denote * iGate.denote ≠ iGate.denote * jGate.denote := by
  change
    place emptySplit jLocal * place emptySplit iLocal ≠
      place emptySplit iLocal * place emptySplit jLocal
  rw [← place_mul, ← place_mul]
  exact (place_injective emptySplit).ne jLocal_mul_iLocal_ne_iLocal_mul_jLocal

/--
The actual public evaluator distinguishes chronological `[i, j]` from
chronological `[j, i]`: the former denotes `j * i`, the latter `i * j`.
This theorem fails if circuit multiplication order is accidentally reversed.
-/
theorem eval_i_then_j_ne_eval_j_then_i :
    OrderedCircuit.eval [iGate, jGate] ≠ OrderedCircuit.eval [jGate, iGate] := by
  simpa using jGate_denote_mul_iGate_denote_ne_iGate_denote_mul_jGate_denote

end OrderSanity

end QuaternionicComputing.Circuit
