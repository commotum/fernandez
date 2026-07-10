# 2-SCALARS

## Current Facts

- Stage 1 completed with a pinned, compiling Lean 4.31.0/mathlib v4.31.0
  baseline and a complete paper claim inventory.
- Mathlib supplies `ℍ`, coordinate projections, multiplication/star simp
  lemmas, `Quaternion.normSq`, and the complex inclusion, but no paper-style
  complex/second-component projections or `ℍ ≃ ℂ × ℂ` API.
- Compiling probes show that bundled maps
  `complexPart, jPart : ℍ →ₗ[ℝ] ℂ` make the required finite-sum proofs
  straightforward; `jPart` is the neutral public name for the paper's “weird
  part.”
- Quaternionic column vectors are right modules.  In one dimension, `j*i ≠ i*j`
  shows that the same left phase does not commute through evolution, but a true
  failure of the existential left-ray relation needs at least two coordinates.
  The checked witness uses `diag(1,j)`, state `(1,1)`, and phase `i`.
- `Matrix.fromBlocks` is reserved for Stage 3; this stage establishes every
  scalar identity it will consume.
- Repository-root `BUILD-PLAN.md` is authoritative for this Lean-changing
  stage; the module split and focused/adjacent builds below are completion
  requirements.

## Updated Assumptions

- The coordinate proofs can be kept elementary with `Complex.ext`, quaternion
  projection simp lemmas, and `ring`; no custom quaternion implementation is
  needed.
- Public typed constants for quaternion `i`, `j`, and `k` are useful both for
  sanity checks and later ordering counterexamples.
- Reconstruction through mathlib's complex coercion and right multiplication
  by `j` is preferable to introducing a second quaternion representation type.
- The scalar component pair should be proved injective/extensional, but a full
  `LinearEquiv ℍ (ℂ × ℂ)` is optional unless it simplifies later state proofs.

## Big Picture Objective

Prove the complex real/imaginary and quaternion complex/`j`-component
identities that drive both matrix embeddings, with explicit signs,
multiplication order, conjugation, norm square, and module-side diagnostics.

## Detailed Implementation Plan

- Create `QuaternionicComputing/Scalar/Quaternion.lean` with documented typed
  quaternion units and bundled real-linear `complexPart`/`jPart` maps.
- Prove coordinate simp lemmas, reconstruction `q = z + w*j`, component
  extensionality/injectivity, add/real-scalar laws inherited from bundling, and
  interaction of `j` with embedded complex scalars.
- Prove the two order-sensitive product formulas from Equation (41), the
  conjugation formulas from Equation (43), and the norm-square decomposition
  from Equation (42).
- Add exact sanity theorems for `i²=j²=k²=-1`, `i*j=k`, `j*i=-k`, a
  fixed-phase noncommutation diagnostic, and a genuine two-coordinate witness
  showing that the existential left-ray relation is not preserved, while right
  phase is.
- Add any minimal complex real/imaginary helper lemmas not already provided by
  mathlib, without duplicating existing APIs.
- Replace the baseline smoke import with the new scalar module and expand the
  axiom audit to its principal exported theorems.
- Update traceability and corrections with stable Lean declaration names.

## Build Structure

- `QuaternionicComputing/Scalar/Quaternion.lean` is the low-dependency public
  scalar core: typed units, bundled components, and cheap algebraic theorems.
- `QuaternionicComputing/Scalar/Phase.lean` is a diagnostic/proof leaf for
  phase-side relations, counterexamples, and their norm/right-action checks; it
  does not add runtime state or alter the quaternion core.
- `QuaternionicComputing.lean` is the thin public root and is changed only to
  re-export the completed scalar API.  `QuaternionicComputing/AxiomAudit.lean`
  remains a proof/audit consumer rather than a public dependency.
- High-fanout mathlib files and global instances are untouched.  Existing
  `Complex.reLm`, `Complex.imLm`, and quaternion APIs are reused rather than
  wrapped without a consumer.
- Focused builds: `lake build QuaternionicComputing.Scalar.Quaternion` and
  `lake build QuaternionicComputing.Scalar.Phase`.
- Adjacent consumers: `lake build QuaternionicComputing` and
  `lake env lean QuaternionicComputing/AxiomAudit.lean`.  Because the public
  root import changed, a full `lake build` is required before stage completion.

## Boundary Checks

- Multiplication formulas must be proved from quaternion coordinates with the
  exact source order; no commutativity assumption may be added to `ℍ`.
- The left-ray diagnostic must rule out every possible common output phase; the
  one-dimensional inequality `j*i ≠ i*j` alone is not sufficient evidence.
- The right-phase theorem must use the opposite-ring/right-action semantics or
  explicit pointwise right multiplication; it must not rename left action.
- Reconstruction and injectivity tests prevent component definitions from
  discarding coordinates.
- Norm-square preservation must use the real scalar values on both sides and
  cannot be made true by defining a new norm to equal the target expression.
- `Phase.lean` is explicitly diagnostic/proof-side; its counterexample cannot
  substitute for the positive scalar identities required by the matrix stage.
- No new global instance or broad simp rule may be added merely to shorten the
  coordinate proofs; simp attributes are limited to stable unit/component laws
  with known downstream consumers.

## Completion Requirements

- All scalar source rows `FER03-Q-ALGEBRA`, `FER03-Q-CONJUGATE-NORM`, and
  `FER03-Q-CO-WD-*` map to compiled public declarations.
- Product, star, reconstruction, extensionality, and norm-square identities are
  proved for arbitrary real quaternions.
- Concrete unit and phase-side sanity checks compile and exercise
  noncommutativity.
- The public root imports the scalar module; focused and full builds pass.
- The main scalar declarations are included in `AxiomAudit.lean` with explained
  output.
- Lean-source scans find no `sorry`, `admit`, `sorryAx`, or project axiom, and
  `git diff --check` passes.
- Traceability/correction documents and this stage's results contain exact Lean
  names, commands, outcomes, and implications for Stage 3.
- `BUILD-PLAN.md` module ownership, focused/adjacent build, boundary, scan, and
  fold-back requirements are satisfied and recorded below.

## Stage Results

- Completed on 2026-07-09.

### Public scalar core

- Added `QuaternionicComputing/Scalar/Quaternion.lean` as the low-dependency
  public scalar module.
- Exported typed `i`, `j`, and `k`, their complete ordered multiplication table,
  and `i_mul_j_mul_k` as executable sign/order checks.
- Exported bundled real-linear `complexPart` and `jPart`; the latter is the
  reusable name for the paper's “weird part.”
- Proved `eq_complexPart_add_jPart_mul_j`, `ext_parts`,
  `eq_iff_parts_eq`, and `components_injective`, so the component maps cannot
  hide or discard coordinates.
- Proved `complexPart_mul`, `jPart_mul`, `complexPart_star`, `jPart_star`,
  `j_mul_coeComplex`, and `normSq_eq_complexPart_add_jPart`, covering the
  paper's Equations (40)–(43).
- Reused mathlib's `Complex.mul_re`, `Complex.mul_im`, `Complex.reLm`, and
  `Complex.imLm`; no redundant complex wrapper API was added.

### Phase correction leaf

- Added `QuaternionicComputing/Scalar/Phase.lean`.  It is intentionally
  promoted as stable public proof API because it is the machine-checked
  evidence for material correction C-006, not temporary scaffolding.
- Defined sided `LeftPhaseEquivalent` and `RightPhaseEquivalent` relations and
  proved unit-right-phase norm-square preservation.
- `fixed_left_phase_not_natural` records only the honest one-dimensional
  noncommutation fact.
- `phaseWitnessGate` is the two-coordinate `diag(1,j)` evolution;
  `phaseWitnessGate_normSq` proves it preserves total coordinate norm square.
  `leftPhaseEquivalent_i_input` supplies the initial unit left phase, while
  `not_leftPhaseEquivalent_gate_i_input` rules out every output left phase.
  This is the genuine failure of the paper's existential left-ray relation.
- `phaseWitnessGate_right_smul` and `rightPhaseEquivalent_gate` prove that the
  repaired right-side relation is respected by the same evolution.

### Traceability and architecture

- Marked `FER03-Q-ALGEBRA`, `FER03-Q-CONJUGATE-NORM`, and every
  `FER03-Q-CO-WD-*` row **proved as stated**, with exact declaration names.
- Updated C-006 with its counterexample, repaired relation, declarations, and
  remaining generic normalized-state work for Stage 4.
- Incorporated repository-root `BUILD-PLAN.md` into the goal, loop, prompt,
  stage templates, global completion requirements, and Stage 1/2 reports.

### Verification evidence

- Focused leaf build:
  `lake build QuaternionicComputing.Scalar.Quaternion QuaternionicComputing.Scalar.Phase`
  — passed (`2342` jobs).
- Adjacent public consumer: `lake build QuaternionicComputing` — passed
  (`2344` jobs).
- Full build: `lake build` — passed (`2344` jobs).
- Warning-as-error audit:
  `lake env lean -DwarningAsError=true QuaternionicComputing/AxiomAudit.lean`
  — passed for ten main scalar/phase exports.
- Every audited theorem reports only the expected mathlib/Lean foundations
  `[propext, Classical.choice, Quot.sound]`; no project-specific axiom appears.
- Lean-only scans for `sorry`, `admit`, `sorryAx`, declaration-level `axiom`,
  and `opaque` returned no matches.
- `git diff --check` passed.

### Fold-back for Stage 3

- Matrix embeddings should consume the bundled `complexPart`/`jPart` maps so
  finite sums use `map_sum` rather than coordinate expansion at every entry.
- Canonical algebraic targets remain sum-indexed `ι ⊕ ι` block matrices;
  wire-facing `Bool × ι` reindexing remains outside the matrix core.
- The phase counterexample stays in its proof leaf and is not a substitute for
  positive matrix embedding/unitarity theorems.
- Determinant-one refinements remain isolated from the multiplicative,
  adjoint, injective, and unitary results needed by the main simulation.
