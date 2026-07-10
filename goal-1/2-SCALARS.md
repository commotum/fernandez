# 2-SCALARS

## Current Facts

- Stage 1 completed with a pinned, compiling Lean 4.31.0/mathlib v4.31.0
  baseline and a complete paper claim inventory.
- Mathlib supplies `ℍ`, coordinate projections, multiplication/star simp
  lemmas, `Quaternion.normSq`, and the complex inclusion, but no paper-style
  complex/weird projections or `ℍ ≃ ℂ × ℂ` API.
- Compiling probes show that bundled maps
  `complexPart, weirdPart : ℍ →ₗ[ℝ] ℂ` make the required finite-sum proofs
  straightforward.
- Quaternionic column vectors are right modules.  The paper's left-phase
  Equation (45) fails already for the one-dimensional gate `j` and phase `i`.
- `Matrix.fromBlocks` is reserved for Stage 3; this stage establishes every
  scalar identity it will consume.

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

Prove the complex real/imaginary and quaternion complex/weird component
identities that drive both matrix embeddings, with explicit signs,
multiplication order, conjugation, norm square, and module-side diagnostics.

## Detailed Implementation Plan

- Create `QuaternionicComputing/Scalar/Quaternion.lean` with documented typed
  quaternion units and bundled real-linear `complexPart`/`weirdPart` maps.
- Prove coordinate simp lemmas, reconstruction `q = z + w*j`, component
  extensionality/injectivity, add/real-scalar laws inherited from bundling, and
  interaction of `j` with embedded complex scalars.
- Prove the two order-sensitive product formulas from Equation (41), the
  conjugation formulas from Equation (43), and the norm-square decomposition
  from Equation (42).
- Add exact sanity theorems for `i²=j²=k²=-1`, `i*j=k`, `j*i=-k`, and a formal
  witness showing left phase is not respected by left multiplication while
  right phase is.
- Add any minimal complex real/imaginary helper lemmas not already provided by
  mathlib, without duplicating existing APIs.
- Replace the baseline smoke import with the new scalar module and expand the
  axiom audit to its principal exported theorems.
- Update traceability and corrections with stable Lean declaration names.

## No-Cheating Checks

- Multiplication formulas must be proved from quaternion coordinates with the
  exact source order; no commutativity assumption may be added to `ℍ`.
- The left-phase diagnostic must prove an actual inequality/non-equality, not
  merely fail to typecheck or cite prose.
- The right-phase theorem must use the opposite-ring/right-action semantics or
  explicit pointwise right multiplication; it must not rename left action.
- Reconstruction and injectivity tests prevent component definitions from
  discarding coordinates.
- Norm-square preservation must use the real scalar values on both sides and
  cannot be made true by defining a new norm to equal the target expression.

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

## Stage Results

- In progress.  Stage opened after the verified completion of 1-INVENTORY on
  2026-07-09.

