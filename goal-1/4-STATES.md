# 4-STATES

## Current Facts

- Stage 3 exports injective, multiplicative, adjoint-preserving matrix
  embeddings on sum indices, together with the unitary/orthogonal image facts
  needed for state evolution.
- `Matrix.realifyVec` already implements the paper's first complex-to-real
  state column `(re ψ, -im ψ)`, and `realify_mulVec` proves its correctly
  typed evolution law for arbitrary compatible matrices.
- Scalar Stage 2 proves
  `Quaternion.normSq q = Complex.normSq (complexPart q) +
  Complex.normSq (jPart q)` and fixes right quaternionic phase.
- The paper's displayed state-intertwining derivations are ill-typed (C-021),
  its quaternionic phase is on the wrong side (C-006), and Equation (44) omits
  the normalization equality (C-005).  Corrected typed statements remain
  mathematically viable.
- Direct computational-basis weights are sufficient for the central
  simulations.  Density matrices and partial trace are optional corollaries,
  not prerequisites.
- Repository-root `BUILD-PLAN.md` remains authoritative for module ownership,
  focused builds, adjacent consumers, boundary checks, and fold-back.

## Updated Assumptions

- A small generic `NormalizedState` subtype parameterized by an explicit
  real-valued scalar weight can share normalization infrastructure without
  introducing global squared-norm instances.
- Public specializations for real, complex, and quaternion amplitudes should
  expose basis weights and normalized `Rebit`, `Qubit`, and corrected
  `Quaterbit` aliases on `Bool`.
- The second complex-to-real column is `(im ψ, re ψ)`.  The two
  quaternion-to-complex columns are
  `(Co ψ, -conj(W ψ))` and `(W ψ, conj(Co ψ))`.
- Each pair of columns is pointwise orthogonal with equal squared norm.  This
  should prove bottom-basis weight preservation for either canonical top
  state and for every normalized real/complex superposition of the two top
  sectors.
- Generic quaternion matrix evolution respects right phase by associativity;
  the corrected ray theorem can be proved independently of normalization.

## Big Picture Objective

Define reusable finite pure-state and computational-basis weight APIs, then
prove that both representation-column pairs preserve norm, intertwine the
matrix embeddings with evolution, and preserve every bottom computational-
basis outcome weight after summing over the added two-level coordinate.

## Detailed Implementation Plan

- Add `QuaternionicComputing/State/Basic.lean` with explicit scalar weight
  functions, generic total weight/normalization, specialized finite real,
  complex, and quaternion state aliases, basis-weight nonnegativity/sum laws,
  and `Rebit`/`Qubit`/`Quaterbit` definitions.
- In the same low state leaf or a narrow quaternion phase leaf, prove finite
  quaternion matrix action commutes with pointwise right scalar action, unit
  right phase preserves basis/total weights, and `RightPhaseEquivalent` is
  preserved by arbitrary matrix evolution.
- Add `QuaternionicComputing/State/Realification.lean`.  Reuse `realifyVec` as
  the first column, define the second column, prove both sector formulas,
  additivity/real scaling, injectivity/reconstruction as useful, equal norm,
  mutual real orthogonality, and both typed matrix-action identities.
- Prove pointwise bottom-weight preservation for each column and for an
  arbitrary normalized top rebit combination.  Derive total norm and
  normalized-state constructors without assuming the source matrix is unitary.
- Add `QuaternionicComputing/State/Complexification.lean` with the two
  quaternion representation columns.  Prove their sector formulas,
  real-linearity laws, injectivity/reconstruction, equal norm, mutual complex
  orthogonality, and both typed complexified-matrix action identities.
- Prove pointwise bottom-weight preservation for each column and for every
  normalized top qubit combination; derive total norm and normalized-state
  constructors.
- Map paper Lemmas 4, 5, 9, and 10 to the corrected typed declarations.  Keep
  equality of state evolution distinct from equality of bottom outcome
  weights and document any density/partial-trace material left for coverage.
- Update the public root and axiom audit only after the leaf APIs stabilize;
  add concrete non-real and genuinely quaternionic state examples.

## Build Structure

- `State/Basic.lean`: low-dependency public data/weight leaf.  It may import
  `Scalar/Phase.lean` for the already-public sided phase relation, but it must
  not import matrix embeddings, determinant machinery, or paper wrappers.
- `State/Realification.lean`: public proof/API leaf importing `State/Basic` and
  `Matrix/Realification`, not the quaternion complexification or determinant
  leaf.
- `State/Complexification.lean`: public proof/API leaf importing
  `State/Basic` and `Matrix/Complexification`, not realification or determinant.
- `QuaternionicComputing.lean`: thin high-fanout root updated only after both
  state leaves compile.  `AxiomAudit.lean` remains an adjacent audit consumer.
- Focused builds are the exact targets for each touched state leaf.  Adjacent
  builds cover both state embedding leaves, then the public root/audit.  The
  root change requires a final full `lake build`.

## Boundary Checks

- Normalization must be an actual equation `totalWeight = 1`; do not repeat
  the paper's incomplete norm display.
- Quaternionic phase and matrix linearity must act on the right.  No theorem
  may silently replace `<•` by ordinary left scalar action.
- State embedding equality, embedded evolution equality, and bottom outcome
  equality are distinct declarations.  No definition of “simulation” may make
  the target theorem tautological.
- Complex/quaternion state maps may be called real-linear only when an
  explicit real action is proved or bundled.  They are not complex- or
  quaternion-linear by default.
- Bottom outcome weight is the sum of the two target sector weights over the
  same bottom index.  Total norm preservation alone cannot substitute for the
  pointwise theorem.
- Arbitrary-top-state theorems require an explicit normalization equation for
  the top amplitudes; cross-term cancellation must be proved, not assumed.
- Matrix action identities must use the actual public `realify`/`complexify`
  maps and source `mulVec`; parallel reference implementations are forbidden.
- Density-matrix or partial-trace diagnostics cannot replace Lemmas 5/10's
  direct observable statement.
- The unresolved quaternion determinant sign is irrelevant here and must not
  appear as a state or measurement hypothesis.

## Completion Requirements

- Corrected normalized `Rebit`, `Qubit`, and `Quaterbit` APIs compile with
  nonnegative computational-basis weights summing to one.
- Generic quaternion right phase preserves normalization, every basis weight,
  and arbitrary matrix evolution.
- Both column pairs have stable public definitions, exact sector lemmas,
  injectivity/reconstruction as appropriate, norm preservation, and mutual
  orthogonality.
- Corrected, typed versions of paper Lemmas 4 and 9 prove evolution
  intertwining for both columns and compatible rectangular matrices.
- Corrected versions of Lemmas 5 and 10 prove pointwise bottom-basis weight
  preservation for both canonical columns and arbitrary normalized top states.
- Non-real complex and genuinely quaternionic examples exercise the public
  maps and observable theorems.
- Traceability and C-005/C-006/C-007/C-008/C-012/C-021 record exact declaration
  names and dependent effects.
- Focused leaves, adjacent consumers, public root, full build,
  warning-as-error audit, import smoke test, forbidden-token/boundary scans,
  and `git diff --check` pass and are recorded below.

## Stage Results

- In progress.  Stage opened after verified completion of 3-MATRICES on
  2026-07-09.
