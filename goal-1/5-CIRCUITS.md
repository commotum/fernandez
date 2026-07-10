# 5-CIRCUITS

## Current Facts

- Stages 2–4 supply all scalar, matrix, state, unitary, and pointwise
  measurement identities needed by circuit translation.
- The algebraic embeddings use sum indices; an added circuit wire should be an
  explicit one-wire sum such as `Unit ⊕ W` (or a proved equivalent `Fin (n+1)`),
  not informal dimension arithmetic.
- Mathlib's `Matrix.kronecker_mem_unitary` works over noncommutative
  coefficients, while `Matrix.mul_kronecker_mul` requires commutativity and is
  forbidden for quaternionic semantics.
- A local placement can be defined audibly from an equivalence
  `L ⊕ K ≃ W`: split full basis assignments into local and complement
  assignments, form `U ⊗ₖ 1`, and reindex back.
- The paper's swap expressions are semantic descriptions of contextual
  matrices, not physical gate lists.  No swap overhead may be counted unless a
  later synthesis theorem constructs it.
- Repository-root `BUILD-PLAN.md` is authoritative for the module split,
  focused builds, adjacent consumers, boundary checks, and fold-back.

## Updated Assumptions

- A generic placement API parameterized by an explicit local/complement split
  equivalence is cleaner than baking `Fin` support arithmetic into every
  theorem.  A constructor from an injective finite support can recover the
  paper-facing interface.
- Gate records may existentially store local arity/complement data while all
  gates in an ordered circuit share the same global wire type and scalar ring.
- Chronological circuit lists should evaluate in reverse multiplication order:
  `[g₁,…,gₛ]` denotes `Gₛ * ⋯ * G₁`.
- Embedding/placement naturality is easiest to audit after exporting an exact
  entrywise characterization of `place`; it must still be proved from the
  actual Kronecker/reindex definition.
- Real and quaternionic gate translations should live in separate proof leaves
  so noncommutative assumptions remain visible and rebuilds stay narrow.

## Big Picture Objective

Build a reusable ordered finite-circuit core whose local gates can be placed
on arbitrary noncontiguous wires, whose evaluation order is explicit, and
whose contextual placement commutes with realification and complexification
after adding one distinguished wire.

## Detailed Implementation Plan

- Add `QuaternionicComputing/Circuit/Placement.lean` defining finite bit-basis
  assignments, basis splitting from `L ⊕ K ≃ W`, and local placement as a
  same-index reindexing of `U ⊗ₖ 1`.
- Prove the exact entry formula: the local matrix entry is used when complement
  assignments agree, otherwise the entry is zero.  Prove identity,
  multiplication, adjoint/star, injectivity without a complement-inhabited
  hypothesis, and
  unitarity preservation without coefficient commutativity.
- Provide a finite-support constructor from `L ↪ W` (or a comparably clear
  support abstraction) and prove that it realizes arbitrary noncontiguous
  supports.  Keep semantic permutations internal to placement.
- Add `QuaternionicComputing/Circuit/Basic.lean` with a placed-gate record,
  explicit local arity/support/split data, its global matrix semantics, and an
  ordered circuit as a chronological list of placed gates.
- Define circuit evaluation independently as the reverse chronological product
  with empty identity; prove singleton, cons/append, length/gate-count, and
  unitary preservation when every local gate is unitary.  Add a two-gate
  noncommutative order sanity theorem that detects accidental product reversal.
- Add narrow realification and complexification circuit-placement leaves.
  Define the added distinguished wire, wire-facing reindexings of the sum-index
  matrix embeddings, translated local matrices/support splits, and prove one
  translated placed gate denotes the embedding of its source contextual
  matrix.
- Prove translated local arity/cardinality is source arity plus one, with the
  complement/global bottom wires unchanged.  Do not yet perform list
  translation induction; that belongs to Stage 6.
- Update public imports, audit, traceability, and the swap/padding corrections
  after APIs stabilize.

## Build Structure

- `Circuit/Placement.lean`: lowest public circuit algebra leaf; imports only
  matrix Kronecker/reindex/unitary and finite equivalence APIs.
- `Circuit/AddedWire.lean`: shared scalar-independent public bookkeeping leaf
  above `Placement`; owns `AddedWire`, the block/basis equivalence, the generic
  star-preserving reindex homomorphism, and the extended support split.
- `Circuit/Basic.lean`: public data/ordered-evaluation leaf importing
  `Placement`, not state or embedding modules.
- `Circuit/OrderSanity.lean`: narrow diagnostic/public-example leaf importing
  `Basic` and quaternion scalars; the generic evaluator remains scalar-neutral.
- `Circuit/Realification.lean`: proof/API leaf importing `Circuit/Basic` and
  `Circuit/AddedWire` plus `Matrix/Realification`; it imports no unitary or
  determinant theorem leaf.
- `Circuit/Complexification.lean`: proof/API leaf importing `Circuit/Basic`
  and `Circuit/AddedWire` plus `Matrix/Complexification`; it imports no
  determinant machinery.
- `QuaternionicComputing.lean`: thin high-fanout root changed only after all
  circuit leaves compile.  `AxiomAudit.lean` is the adjacent audit consumer.
- Focused builds target each circuit leaf.  Adjacent builds cover both
  embedding leaves, then the root/audit; the root change requires a full build.

## Boundary Checks

- `Matrix.mul_kronecker_mul` is forbidden in every quaternionic dependency
  cone.  Placement multiplication must come from reindexing and the exact
  identity-complement structure, or from a theorem whose hypotheses visibly
  cover the noncommutative case.
- Circuit evaluation is defined before and independently of translation and
  simulation.  It cannot contain an embedded reference operator or outcome.
- A gate's local arity/support data must determine its global matrix semantics;
  arity metadata may not be attached to an arbitrary global matrix without a
  locality certificate.
- Arbitrary noncontiguous support must be represented by an injection or split
  equivalence and tested; only initial-segment placement is insufficient.
- Semantic reindexing/permutation is not a physical swap-gate list and does not
  contribute to gate count.
- The added top wire must be shared and distinguished by type/equivalence.  It
  may not be duplicated per gate in the target global wire type.
- Embedding/placement compatibility must compare the actual public matrix
  embeddings and actual `place`; defining translated semantics to be the
  desired global embedding is forbidden.
- Quaternionic placement may rely on central `0` and `1` entries in the
  identity complement, but no general commutativity of quaternion entries may
  be assumed.
- A two-gate order test must use genuinely noncommuting matrices and evaluate
  the public ordered semantics.

## Completion Requirements

- Generic local placement, exact entry behavior, one/multiplication/adjoint,
  and unitary preservation compile over the weakest justified coefficient
  assumptions, including quaternions.
- A placed-gate/circuit API represents arbitrary finite noncontiguous support
  and reverse-chronological matrix evaluation with proved append/order laws.
- Circuit unitarity follows from local gate unitarity without a commutative
  shortcut.
- One-gate contextual naturality compiles for both realification and
  complexification with one shared added wire and local arity increased by one.
- A public two-gate example catches reversed evaluation order.
- Traceability rows for padding, swap semantics, circuit soundness, and the
  local prerequisite of Lemmas 3/8 are updated; C-009/C-022 dependent effects
  are explicit.
- Focused leaves, adjacent consumers, root, full build, warning-as-error audit,
  downstream import smoke, forbidden-token/boundary scans, and
  `git diff --check` pass and are recorded below.

## Stage Results

- Completed on 2026-07-09.
- `Circuit/Placement.lean` exports `BitBasis`, exact `basisSplit` restrictions,
  `place`/`place_apply`, its zero/add/one/multiplication/adjoint/star laws,
  injective ring/star homomorphisms, and `place_mem_unitary`.  The key
  `kronecker_one_mul` proof rewrites right-identity Kronecker padding as block
  diagonal multiplication, which is valid over an arbitrary semiring.
- `SupportComplement`, `supportSplit`, and `placeOnSupport` construct the
  contextual semantics of every injective support, including arbitrary
  noncontiguous and reordered local wires.  Reindexing is semantic; no swap
  gate is inserted or counted.
- `Circuit/Basic.lean` exports locality-certified `PlacedGate`: its global
  denotation is derived from its stored local matrix and split, rather than
  being an independent field.  It also exports chronological `OrderedCircuit`,
  reverse-product `eval`, nil/singleton/cons/append laws, `gateCount`, the
  monoid-hom map induction helper, and local-to-global/circuit unitarity.
- `Circuit/OrderSanity.lean` gives a quaternionic `i`/`j` test.  Independent
  review found that the initial symmetric inequality detected
  noncommutativity but would not detect a globally reversed evaluator.  The
  repaired fixed-value checks prove that the unique entry of
  `eval [iGate,jGate]` is `-k` and the swapped entry is `k`; reversing
  evaluation now breaks the stated theorem.
- `Circuit/AddedWire.lean` makes the shared target wire literal:
  `AddedWire W = Unit ⊕ W`.  `addedBasisEquiv` identifies the two block sectors
  with false/true top-bit assignments.  `addTopSplit` puts the same top wire
  into each translated local support and leaves the complement unchanged.
- `Circuit/Realification.lean` and `Circuit/Complexification.lean` export
  `wireRealify`/`wireComplexify`, injectivity, identity, multiplication,
  adjoint, star-monoid, and unitary laws.  `wireRealify_place` and
  `wireComplexify_place` are entrywise proofs against the actual public
  `place`; neither translation is defined to make naturality tautological.
- `realifyPlacedGate` and `complexifyPlacedGate` preserve denotation through
  their respective embeddings.  Their support-map simp theorems prove that
  top maps to top, each old local/complement wire maps to the corresponding
  bottom wire, local arity is exactly source arity plus one, complement arity
  is unchanged, and local unitarity is preserved.
- Declaration classification: placement, added-wire algebra, placed gates,
  evaluation, and one-gate translations are public reusable API;
  `OrderSanity` is the narrow diagnostic/public example; naturality and
  unitary results are proof/API leaves.  No simulation result or future
  reference operator occurs in the circuit core.
- Documentation was updated in `README.md`, `docs/Architecture.md`,
  `docs/Conventions.md`, `docs/Traceability.md`, and `docs/Corrections.md`.
  Padding, semantic swaps, circuit soundness, the fixed-order part of
  Definition 4, and the local prerequisites of Lemmas 3/8 now have explicit
  dispositions.  C-009 records the proved identity-complement law and the
  still-pending general criterion; C-022 records the repaired quaternionic
  placement proof and its Stage 6 consumer.
- Focused evidence passed: `Placement` (1,674 jobs), `AddedWire` (1,675 jobs),
  `Basic` plus `OrderSanity` (2,344 jobs), `Realification` (1,702 jobs), and
  `Complexification` (2,346 jobs).  A combined adjacent root/audit build passed
  2,508 jobs.  A subsequent full `lake build` passed 2,507 jobs.
- Direct `lake env lean ... -DwarningAsError=true` checks passed for all six
  circuit leaves.  `/tmp/Stage5ImportSmoke.lean`, importing only the public
  root and checking placement/evaluation/order/translation APIs, passed under
  warning-as-error.
- The expanded `AxiomAudit.lean` reports only `propext`, `Classical.choice`,
  and `Quot.sound` for the new main circuit results.  Lean-source scans found
  no `sorry`, `admit`, `sorryAx`, project `axiom`, `opaque`, or `unsafe`; the
  circuit cone contains no `Matrix.mul_kronecker_mul`; core files contain no
  translation references; embedding leaves contain no forbidden determinant,
  unitary-leaf, or state imports.  `git diff --check` passed.
- Independent Stage 5 review found no remaining mathematical or API flaw after
  the order-orientation repair.  Stage 6 can now translate lists with
  `OrderedCircuit.eval_map_of_denote_eq` and combine those operator identities
  with the already proved state/measurement lemmas.
