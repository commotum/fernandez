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

- Completed on 2026-07-09.

### Normalized finite states and corrected phase

- Added `QuaternionicComputing/State/Basic.lean` as the low-dependency public
  state core.  `basisWeight`, `totalWeight`, and
  `NormalizedState ι α weight` keep the real-valued scalar weight explicit and
  make normalization the actual equation `totalWeight = 1`.
- Exported `realWeight`, `complexWeight`, and `quaternionWeight`; their basis
  and total specializations; and nonnegativity/sum-to-one theorems.  Public
  `RealState`, `ComplexState`, and `QuaternionState` aliases use these exact
  conventions.
- `Rebit`, `Qubit`, and `Quaterbit` specialize to the `Bool` basis.
  `Quaterbit.normalization` supplies the missing `= 1` from paper Equation
  (44), while the analogous rebit/qubit expansion theorems aid downstream use.
- Unit quaternion right multiplication is proved to preserve each basis
  weight, total weight, and normalized state.  `QuaternionState.rightPhase`
  packages the normalized operation and proves the repaired ray relation.
- `quaternion_mulVec_right_smul` is derived from
  `Matrix.mulVecBilin ℍ ℍᵐᵒᵖ`, and `rightPhaseEquivalent_mulVec` proves that
  every compatible quaternionic matrix evolution respects the corrected right
  ray.  The State directory contains no use of `LeftPhaseEquivalent`.

### Complex states represented over the reals

- Added `QuaternionicComputing/State/Realification.lean`.  `realColumn0`
  reuses the matrix leaf's `(re, -im)` vector map; `realColumn1` implements
  `(im, re)`.  Four sector lemmas expose the exact signs.
- `realColumn0Linear` and `realColumn1Linear` prove the paper's state maps are
  specifically `ℝ`-linear.  Explicit left inverses and
  `realColumn0_injective`/`realColumn1_injective` prove both encodings lose no
  amplitudes.
- `realColumn0_single` and `realColumn1_single` prove paper Equations (20) and
  (21) using the actual public encodings.
- `realify_mulVec_realColumn0` and `realify_mulVec_realColumn1` prove the two
  corrected, well-typed forms of Lemma 4 for arbitrary compatible rectangular
  matrices.  `realify_mulVec_realTopCombination` extends this to every real
  top-sector combination.
- `realColumn0_dot_self`, `realColumn1_dot_self`,
  `realColumns_orthogonal`, and `realColumns_equal_norm` establish norm
  preservation and mutual orthogonality.
- `bottomRealWeight`, `realColumn0_bottomWeight`, and
  `realColumn1_bottomWeight` prove pointwise bottom computational-basis weight
  preservation.  The exact scaling formula for `realTopCombination` yields
  `realTopCombination_bottomWeight_of_rebit` for every normalized pure top
  rebit; `realTopState` packages the normalized target.
- `reducedRealOuter` is the minimal explicit rank-one reduced matrix.
  `reducedRealOuter_realColumns` proves both canonical columns give the same
  reduced matrix, `reducedRealOuter_realColumn0` identifies its entries with
  the real part of the complex outer product, and
  `reducedRealOuter_diagonal` connects its diagonal to `bottomRealWeight`.
  This proves the useful content of Lemma 5 without a density hierarchy.
- `realColumns_I_sanity` exercises the non-real amplitude `I` and fixes both
  state-column signs.

### Quaternionic states represented over the complexes

- Added `QuaternionicComputing/State/Complexification.lean` with
  `complexColumn0 = (Co, -conj W)` and
  `complexColumn1 = (W, conj Co)`, matching paper Equations (52)–(53).
- Both maps are bundled as `ℝ`-linear maps; reconstruction, left-inverse,
  injectivity, and canonical-basis theorems establish their exact semantics.
- `complexify_mulVec_complexColumn0` and
  `complexify_mulVec_complexColumn1` prove the two corrected typed forms of
  Lemma 9 for arbitrary compatible rectangular quaternion matrices.
  `complexify_mulVec_complexTopCombination` extends the identity to every
  complex top-sector combination.
- `complexColumn0_bottomWeight` and `complexColumn1_bottomWeight` prove Lemma
  10's observable conclusion pointwise from the scalar quaternion norm
  decomposition.  Total-weight preservation, mutual complex orthogonality,
  and equal norms are also proved.
- `complexTopCombination_bottomWeight` is the exact unnormalized scaling law;
  `complexTopCombination_bottomWeight_of_qubit` covers every normalized pure
  top qubit, and `complexTopState` packages the normalized target.
- `quaternionicJExampleState` is a normalized genuinely quaternionic example;
  its four sector theorems and bottom-weight theorem guard all conjugation and
  sign choices.

### Source corrections and coverage

- `FER03-D03-QUATERBIT` is now **corrected and proved** with explicit
  normalization and right phase.  C-005 and the generic portion of C-006 are
  closed by public state declarations.
- Paper Lemmas 4 and 9 are **corrected and proved** with dimensions and source/
  target vectors enforced by types; C-012 and C-021 record the replacements.
- Lemmas 5 and 10 are proved at their direct finite observable level.  The real
  canonical reduced-matrix equality is also formalized.
- C-007 is closed by four bundled real-linear state maps, and C-008 is closed
  by the sum-index doubled codomain plus reconstruction/injectivity.
- The paper's prose claim about arbitrary normalized pure top rebits/qubits is
  proved.  Its mixed-top-state extension remains **partially formalized** until
  a density-state API has an independent consumer; it is not used by the
  central pure-state simulation.
- Traceability, corrections, architecture, conventions, mathlib API notes, and
  README imports were updated with the exact stable declarations.

### BUILD-PLAN verification evidence

- Focused strict checks passed for `State/Basic.lean`,
  `State/Realification.lean`, and `State/Complexification.lean` with
  `lake env lean -DwarningAsError=true`.
- The focused Basic build passed (`2343` jobs); the three-state-leaf adjacent
  build passed (`2347` jobs); the state leaves plus public root passed (`2501`
  jobs).
- Because the high-fanout root changed, final `lake build` passed (`2501`
  jobs).
- `/tmp/Stage4ImportSmoke.lean`, importing only `QuaternionicComputing`,
  passed with warnings as errors and checked normalized states, right phase,
  all four action identities, reduced-real equality, both arbitrary-top
  observable theorems, and the quaternionic `j` sign example.
- The expanded warning-as-error axiom audit passed for 51 main scalar, matrix,
  state, phase, measurement, group, and determinant declarations.  Every
  result reports only `[propext, Classical.choice, Quot.sound]`; no project
  axiom appears.
- Lean-only scans found no `sorry`, `admit`, `sorryAx`, declaration-level
  `axiom`/`opaque`, unsafe declaration, quaternion ordinary determinant,
  quaternion `Matrix.unitaryGroup`, noncommutative Kronecker shortcut, or state
  use of the rejected left-phase relation.
- `git diff --check` passed.  Basic normalization/phase data remain in the
  low leaf, the two embedding proof surfaces are separate, determinant
  machinery is not imported by state leaves, and the public root remains a
  thin importer, satisfying the stage's build structure and boundaries.

### Fold-back for Stage 5

- Circuit semantics should use arbitrary amplitude columns for algebraic
  evaluation and attach `NormalizedState` only at the measurement boundary.
- Local gate placement over quaternions must preserve the right-module action;
  `quaternion_mulVec_right_smul` is the state-level compatibility theorem.
- The translated top coordinate is sum-indexed in the core.  Circuit-facing
  wrappers should reindex it to a distinguished `Bool` wire without changing
  the proved column or bottom-weight theorems.
- Later simulation theorems should compose the matrix embedding identities
  with the four state action theorems and conclude via pointwise bottom weights,
  not by equating differently typed source and target states.
- A mixed-state/partial-trace hierarchy remains optional and cannot block the
  ordered pure-state simulation.
