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
  multiplication, adjoint/star, injectivity for inhabited complement, and
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
- `Circuit/Basic.lean`: public data/ordered-evaluation leaf importing
  `Placement`, not state or embedding modules.
- `Circuit/Realification.lean`: proof/API leaf importing `Circuit/Basic` and
  `Matrix/Realification`/unitary APIs as needed.
- `Circuit/Complexification.lean`: proof/API leaf importing `Circuit/Basic`
  and `Matrix/Complexification`; it may not import determinant machinery.
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

- In progress.  Stage opened after verified completion of 4-STATES on
  2026-07-09.
