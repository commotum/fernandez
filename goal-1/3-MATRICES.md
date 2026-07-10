# 3-MATRICES

## Current Facts

- Stage 2 provides compiled bundled `complexPart` and `jPart` maps with all
  product/star/norm identities required by quaternion complexification.
- Mathlib already provides bundled real/imaginary maps for `ℂ`, block matrices,
  conjugate transpose, noncommutative matrix multiplication, reindexing, and
  generic `unitary` submonoids.
- `Matrix.fromBlocks_multiply` and `Matrix.fromBlocks_conjTranspose` work over
  quaternion coefficients; algebraic embeddings can stay on `ι ⊕ ι`.
- `Matrix.unitaryGroup` and `Matrix.det` require commutative coefficients.
  Quaternionic unitaries must use `unitary (Matrix ι ι ℍ)`, and determinant one
  can only be discussed after mapping to complex matrices.
- The paper's Theorems 3 and 5 have target-dimension errors and both omit a
  determinant-one argument.  The main simulations need unitary/orthogonal
  preservation, not determinant one.
- `BUILD-PLAN.md` is authoritative for module ownership, focused builds,
  adjacent consumers, boundary checks, and fold-back.

## Updated Assumptions

- Separate `Realification` and `Complexification` leaves will keep imports and
  rebuilds narrower than one combined embedding module.
- `Matrix.fromBlocks` should be the readable canonical definition; square
  versions may be bundled as ring/real-algebra homomorphisms after the basic
  rectangular lemmas compile.
- A small higher proof leaf can package unitarity/group-image consequences
  without forcing determinant machinery into consumers of the embeddings.
- The realification determinant identity is likely approachable in mathlib but
  must be probed independently.  Quaternionic special-unitary membership may
  remain a precisely isolated obligation if its positivity/topology argument
  is unavailable.

## Big Picture Objective

Construct dimension-safe, injective, multiplicative, adjoint-preserving finite-
matrix embeddings from complex matrices to real block matrices and quaternionic
matrices to complex block matrices, then prove the orthogonal/unitary image
results needed by the paper's simulations.

## Detailed Implementation Plan

- Add `QuaternionicComputing/Matrix/Realification.lean` defining pointwise real
  and imaginary component matrices and the paper-sign block map on sum indices.
- Prove rectangular application/block characterizations, additivity, zero/one,
  injectivity, compatible-shape multiplication, and
  `realify(Aᴴ) = realify(A)ᵀ`; package the square map if useful.
- Add `QuaternionicComputing/Matrix/Complexification.lean` defining component
  matrices from `complexPart`/`jPart` and
  `[[Co,W],[-conj W,conj Co]]` with entrywise—not transposing—conjugation.
- Prove the analogous additivity, zero/one, injectivity, multiplication, and
  conjugate-transpose laws for arbitrary compatible finite shapes.
- Add a narrow `QuaternionicComputing/Matrix/Unitary.lean` proof/API leaf that
  maps complex unitaries to real orthogonals and quaternionic unitaries to
  complex unitaries, and exposes injective homomorphisms/isomorphisms onto their
  ranges where useful.
- Probe determinant identities in a separate
  `QuaternionicComputing/Matrix/Determinant.lean` leaf.  Prove justified SO/SU
  refinements or record the exact remaining obstruction without weakening the
  unitary image results.
- Add low-dimensional exact examples that detect the block signs and index
  ordering for a non-real complex scalar and quaternion `j`.
- Update the public root only after stable matrix API names are fixed; expand
  the axiom audit and source traceability/correction map.

## Build Structure

- `Matrix/Realification.lean`: low-dependency public definition/basic proof leaf
  importing only the narrow complex/matrix APIs it consumes.
- `Matrix/Complexification.lean`: public definition/basic proof leaf importing
  `Scalar/Quaternion.lean`, not the diagnostic `Scalar/Phase.lean`.
- `Matrix/Unitary.lean`: higher proof/public API leaf importing both embeddings
  and generic unitary machinery.
- `Matrix/Determinant.lean`: optional heavy proof leaf isolated from the main
  embedding/unitarity dependency cone.
- `QuaternionicComputing.lean`: thin high-fanout public root changed only after
  the leaf APIs compile.  `AxiomAudit.lean` is an adjacent audit consumer.
- Focused builds are the exact `lake build` targets for each touched leaf.
- Adjacent builds are `lake build QuaternionicComputing.Matrix.Unitary`, then
  the public root and explicit warning-as-error axiom audit.  A root import
  change requires a final full `lake build`.

## Boundary Checks

- Never use `Matrix.unitaryGroup` or ordinary `Matrix.det` on quaternion
  coefficients; both require commutativity.
- Never encode the paper's operator-valued “formal tensor” as an ordinary
  Kronecker product.  The canonical definitions are explicit block matrices.
- For the lower-left/right quaternion blocks, `M.map star` means entrywise
  complex conjugation; square-matrix `star M` would silently transpose and is
  forbidden there.
- Do not assume determinant one from unitarity.  SO/SU refinements live in the
  determinant leaf and cannot block the O/U results required downstream.
- Multiplication theorems must retain compatible shape/index assumptions and
  may not add commutativity of quaternion coefficients.
- Low-dimensional examples must evaluate the actual public definitions, not a
  parallel reference implementation.
- Diagnostics or determinant probes are not completion evidence for Lemmas 1,
  2, 6, or 7; the exported embedding theorems themselves must compile.

## Completion Requirements

- Correct, compiled generalizations of paper Lemmas 1, 2, 6, and 7 have stable
  public names and source mappings.
- Both embeddings preserve zero, one, multiplication, and the appropriate
  adjoint and are proved injective with dimensions represented by sum indices.
- Complex unitary images are proved orthogonal; quaternionic unitary images are
  proved complex unitary, without project axioms or commutativity shortcuts.
- Corrected image/group consequences of Theorems 3 and 5 needed by simulation
  are proved.  Each determinant-one refinement is either proved in its isolated
  leaf or recorded as an exact unresolved refinement with no effect on the main
  dependency cone.
- Concrete `1×1`/two-sector examples check signs and component ordering.
- `BUILD-PLAN.md` focused leaf, adjacent consumer, import/boundary, warning,
  scan, diff, audit, and fold-back evidence is recorded below.
- Public root, full build, forbidden-token/project-axiom scans, warning-as-error
  audit, and `git diff --check` pass.
- Traceability and correction logs identify exact declarations, repaired
  dimensions, determinant status, and dependent effects.

## Stage Results

- In progress.  Stage opened after verified completion of 2-SCALARS on
  2026-07-09.

