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

- Completed on 2026-07-09.

### Complex-to-real embedding

- Added `QuaternionicComputing/Matrix/Realification.lean` as a low-dependency
  public algebra leaf.  It exports rectangular `realPart`, `imagPart`, and the
  paper-sign block map `realify : Matrix m n ℂ → Matrix (m ⊕ m) (n ⊕ n) ℝ`.
- The four `realify_apply_*` theorems expose the exact block order and signs;
  `eq_iff_realPart_eq_and_imagPart_eq`, `realify_injective`, and
  `realify_inj` prove that no complex data is lost.
- `realPart_mul`, `imagPart_mul`, and `realify_mul` prove paper Lemma 1 for
  arbitrary compatible rectangular shapes.  Zero, one, addition, negation,
  subtraction, and real scaling are also preserved.
- `realPart_conjTranspose`, `imagPart_conjTranspose`, and
  `realify_conjTranspose` prove paper Lemma 2, again rectangularly.
- `realifyVec = (re, -im)` and `realify_mulVec` already prove the correctly
  typed first state-column intertwining identity.  They are classified as
  low-level vector/sign API; Stage 4 will add the second column, normalization,
  and measurements.
- `realify_map_ofReal` proves the paper's real-gate block-diagonal optimization.
  `realify_I_scalar` is a named exact sign/order check using the public map.

### Quaternion-to-complex embedding

- Added `QuaternionicComputing/Matrix/Complexification.lean`, importing only
  the scalar quaternion core and block matrices.
- It exports rectangular `complexPartMatrix`, `jPartMatrix`, and
  `complexify : Matrix m n ℍ → Matrix (m ⊕ m) (n ⊕ n) ℂ` with blocks
  `[[Co,W],[-conj W,conj Co]]`.  The lower conjugations are explicitly
  entrywise `Matrix.map star`, never square-matrix `star`.
- Four `complexify_apply_*` lemmas, `complexify_eq_iff_parts`,
  `complexify_injective`, and `complexify_eq_iff` fix the representation and
  prove injectivity.
- `complexPartMatrix_mul`, `jPartMatrix_mul`, and `complexify_mul` prove paper
  Lemma 6 for compatible rectangular quaternion matrices without a
  commutativity assumption.  `complexify_conjTranspose` and its component
  lemmas prove paper Lemma 7.
- `complexifyRingHom` bundles the finite square map.  The structural theorem
  `complexify_mul_complexificationJ` proves the exact intertwining with the
  skew block matrix while keeping symplectic imports out of the basic leaf.
- `complexify_map_coeComplex` records the complex-subfield block form, and
  `complexify_j_scalar` checks the genuinely quaternionic sign pattern.

### Unitary and group images

- Added `QuaternionicComputing/Matrix/Unitary.lean` as the higher proof/API
  leaf.  `realifyStarMonoidHom` and `complexifyStarMonoidHom` package the proved
  one/multiplication/adjoint laws without duplicating them.
- `realifyUnitary`, `realifyUnitary_injective`, and
  `realifyUnitaryEquivImage` give the corrected injective group embedding of
  complex unitaries into their doubled real image;
  `realify_mem_orthogonal` proves the `O(2N)` result used downstream.
- `complexifyUnitary`, `complexifyUnitary_injective`, and
  `complexifyUnitaryEquivImage` give the corresponding quaternionic-to-complex
  group embedding.  `complexify_mem_unitary` proves the required `U(2N)` image,
  and `complexify_mem_symplectic` proves preservation of mathlib's canonical
  symplectic form.
- An independent read-only review checked every sign, multiplication order,
  star/entrywise-conjugation distinction, dimension, typeclass assumption, and
  the symplectic calculation.  It found no mathematical or Lean defect and no
  determinant-one claim leaking into this leaf.

### Isolated determinant results and obstruction

- Added `QuaternionicComputing/Matrix/Determinant.lean` as the deliberately
  heavy proof leaf.  Its restricted-scalar proof uses the real basis
  `[1, -I]`, `LinearMap.det_restrictScalars`, and same-index reindexing to prove
  `realify_det : det (realify A) = Complex.normSq (det A)` for every finite
  index type, including the empty type.
- `realify_det_eq_one_of_mem_unitary` and
  `realify_mem_specialOrthogonal` repair the paper's missing determinant
  argument and prove the stronger corrected embedding `U(N) → SO(2N)`.
- For quaternionic complexification, `complexify_det_star_fixed` and
  `complexify_det_im_eq_zero` prove that the complex determinant is real.
  Unitarity gives `complexify_det_sq_eq_one_of_mem_unitary` and the strongest
  currently justified alternative
  `complexify_det_eq_one_or_neg_one_of_mem_unitary`.
- The paper's claimed `SU(2N)` refinement is not inferred.  Selecting the
  positive sign requires a Pfaffian congruence theorem, connectedness of the
  finite compact symplectic group, or nonnegativity of the Study determinant.
  None exists in the pinned mathlib; its own `SymplecticGroup` module lists
  determinant one as a TODO and proves only determinant invertibility.  This
  exact obstruction is recorded in C-004 and does not affect simulation.

### Traceability and corrections

- `FER03-L01`, `L02`, `L06`, and `L07` are now **proved as stated**, with
  rectangular generalizations and exact declarations.
- Corrected `FER03-T03` is **corrected and proved**, including the dimension,
  full-`U(N)` domain, determinant identity, and `SO(2N)` conclusion.
- `FER03-T05` is **partially formalized**: the corrected doubled unitary and
  symplectic image/group isomorphism is proved, while only its special-unitary
  sign refinement remains unresolved.
- C-002, C-003, C-004, C-011, and C-020 now record the proved repairs,
  declarations, remaining obstruction, and effects on dependent results.
- `docs/Architecture.md`, `docs/Conventions.md`, and `docs/MathlibAPI.md` now
  describe the actual four-leaf matrix architecture and determinant boundary.

### BUILD-PLAN verification evidence

- Focused strict checks passed for `Realification.lean`,
  `Complexification.lean`, `Unitary.lean`, and `Determinant.lean` with
  `lake env lean -DwarningAsError=true`.
- Focused/adjacent builds passed: all three embedding/unitary leaves (`2345`
  jobs), the determinant leaf (`2495` jobs), and the public root (`2498` jobs).
- Because the high-fanout root changed, final `lake build` passed (`2498`
  jobs).
- `/tmp/Stage3ImportSmoke.lean`, importing only `QuaternionicComputing`,
  passed with warnings as errors and checked both public scalar-matrix sign
  theorems plus the main group/determinant declarations.
- The expanded `AxiomAudit.lean` passed with warnings as errors.  All 28
  audited scalar, phase, embedding, group, symplectic, and determinant results
  report only `[propext, Classical.choice, Quot.sound]`; no project axiom is
  used.
- Lean-only scans found no `sorry`, `admit`, `sorryAx`, declaration-level
  `axiom`/`opaque`, unsafe declaration, quaternion ordinary determinant,
  quaternion `Matrix.unitaryGroup`, or `mul_kronecker_mul` shortcut.
- `git diff --check` passed.  Basic definitions remain in narrow leaves,
  symplectic/group consequences in `Unitary`, determinant machinery in
  `Determinant`, the public root remains import-only, and the audit remains an
  adjacent consumer, satisfying the recorded build structure and boundaries.

### Fold-back for Stage 4

- Reuse `realifyVec`/`realify_mulVec` as the first complex-state column; add
  the second column without duplicating the matrix proof surface.
- Define the two quaternionic state columns from `complexPart`/`jPart` and
  prove their evolution laws from the public block-entry or `mulVec` APIs.
- Keep state maps explicitly real-linear or action-specific; do not call them
  complex/quaternion-linear without the documented scalar action.
- Measurement preservation needs only the proved norm-square decompositions
  and unitary image results.  It must not depend on the unresolved quaternion
  determinant sign.
