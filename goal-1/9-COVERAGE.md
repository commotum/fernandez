# 9-COVERAGE

## Current Facts

- Stages 1–8 establish the central scalar, matrix, normalized-state, placed
  circuit, fixed/scheduled simulation, ordering, resource, compiler-bound, and
  deterministic-postprocessing results.  The public root, full build, and
  axiom audit are green.
- Stage 9 has closed the former temporary traceability rows.  The direct `4×4`
  real quaternion representation, corrected proper-image statements, concrete
  non-product encoding, phase and basis-preparation APIs, and product-input
  ordering diagnostic are implemented; every remaining interpretive claim has
  an explicit terminal disposition.
- Equation (63)'s specific coordinate matrix is proved equal to
  `Matrix.realify (Quaternion.complexify A)` after the pure simultaneous sector
  permutation `[3,1,0,2]`; all sixteen signs are checked entrywise.
- The paper calls the direct map an “isomorphism from `Sp(N)` to `SO(4N)`.”
  The checked corrected statement is an injective star-preserving homomorphism
  *into* `SO(4N)`, and an explicit `SO(4)` nonimage witness disproves
  surjectivity onto the whole special orthogonal group at rank one.
- The paper's converse sentence names `Sp(2N)` as the codomain of
  quaternionic complexification, although the target is complex unitary/
  special-unitary space and the proved image lies in the symplectic-preserving
  subgroup.
  Properness also needs dimension qualifications: `Sp(1) ≅ SU(2)`, while the
  analogous `U(1) → SO(2)` realification is onto.
- A normalized complex state with amplitudes `3/5` and `(4/5)i` is now the
  rational, square-root-free witness that the added top wire need not factor
  from the bottom wire.
- Mixed-top claims require a density/operator API and are not prerequisites of
  any pure-state or observable theorem.  A known basis input now has an exact
  unitary preparation gate, while arbitrary-state synthesis and a uniform
  generator remain outside scope.  Physical causality, entanglement analogy, bit-commitment
  security, and BQP/open-question prose lack formal models in the source.
- Repository-root `BUILD-PLAN.md` remains authoritative for ownership,
  focused/adjacent builds, boundary scans, and fold-back.

## Updated Assumptions

- The direct real representation is defined in the paper's coordinate order
  and proved equal to a reindexing of the verified matrix composition.
  Multiplication, adjoint, injectivity, unitarity/orthogonality, and determinant
  one are inherited rather than reproved by a fragile 16-block calculation.
  The existing two-wire circuit translation remains canonical; no direct
  placement or wire-facing bridge is inferred from the matrix theorem.
- Proper-image claims are best repaired with explicit low-dimensional target
  matrices: prove target group membership and non-membership in the embedding
  image by checked block/component constraints.  Do not infer operational
  simulation lower bounds from matrix non-surjectivity.
- The rational non-product example should use an explicit definition of pure
  top/bottom factorization and prove failure from its four coordinates.  It
  should not be described as a general mixed-state or signaling theorem.
- A quotient construction for complex rays is not needed by later users.  A
  light phase-equivalence/weight-invariance API may be added if it closes the
  source row cleanly; otherwise the vector-level representation and deliberate
  quotient exclusion must be terminally documented.

## Big Picture Objective

Close all remaining important paper claims with either reusable checked
mathematics or an exact terminal disposition.  Formalize the direct real
quaternion representation, correct the converse/proper-image story with
dimension-safe witnesses, and add the promised non-product encoded-state
example.  Explicitly separate these algebraic facts from physical,
cryptographic, mixed-state, uniformity, and complexity interpretations.

## Detailed Implementation Plan

- Add a direct-realification matrix leaf.  Define the four quaternion
  coordinate matrices and the displayed `4×4` block map on a transparent index
  type.  Prove every block entry, the explicit basis reindexing to
  `realify (complexify A)`, and rectangular injectivity/additivity.
- For square matrices, derive identity, compatible multiplication, adjoint,
  a star-monoid embedding, unitary-to-orthogonal/special-orthogonal
  preservation, and the exact relationship to the existing two-step matrix
  embedding.  Correct “isomorphism to `SO`” to an injective image statement;
  retain the established compositional circuit operator separately.
- Add a proper-image witness leaf.  Exhibit a concrete special-orthogonal
  real matrix in dimension four outside realification of `2×2` complex
  matrices, and a concrete complex special-unitary/unitary matrix in dimension
  four outside quaternionic complexification/symplectic image.  Record the
  `N=1` exception rather than asserting universal properness.
- Add a narrow state example defining pure top/bottom factorization and a
  normalized rational complex source state whose canonical real encoding is
  proved nonfactorable.  Keep the general definition reusable and the heavy
  coordinate proof in the example leaf.
- Add a narrow product-input ordering diagnostic reusing the Stage 7 disjoint
  mixers.  On the normalized ground basis input, prove the two legal orders
  yield right-phase-inequivalent normalized columns with exact opposite `11`
  amplitudes, while every computational-basis weight agrees.  Do not infer
  signaling, entanglement, or bit-commitment security from that ray-level
  state inequality.
- Add a basis-preparation leaf for the paper's ground-state convention.  A
  classically known computational-basis assignment should induce an XOR
  permutation/unitary placed gate that maps the all-zero basis column to that
  assignment; prepending it absorbs that known basis input.  Do not generalize
  this to an unknown arbitrary quantum state or uniform runtime claim.
- Close the complex-ray row with a light unit-phase API: unit right phase is an
  equivalence relation, preserves basis/total weights, and commutes with
  arbitrary compatible matrices.  Do not introduce a projective quotient that
  no theorem consumes.
- Revisit every remaining temporary traceability row.  Assign terminal statuses
  to the norm-preserver background fact, ground-state preparation, real-gate
  interpretation, mixed-top extensions, physical/nonlocal-time prose,
  bit-commitment claim, converse implications, and explicit open questions.
  Record Equation (63)'s isomorphism repair as correction C-025.
- Promote stable leaves to the root/audit only after focused and adjacent
  consumers compile; update README, architecture, conventions, API notes,
  traceability, and corrections.

## Build Structure

- `Matrix/QuaternionRealification.lean`: algebraic proof leaf importing the two
  existing embedding definitions; owns the direct coordinate map, checked
  reindex equivalence, sixteen entries, and inherited rectangular algebra.
- `Matrix/QuaternionRealificationUnitary.lean`: heavier group/determinant leaf;
  owns the star embedding, `SO(4N)` consequence, and equivalence with the exact
  image.  Neither matrix leaf imports circuits or simulations.
- `Matrix/ProperImage.lean`: diagnostic/public correction leaf importing
  `Matrix/Determinant` and direct/complexification group facts; explicit
  finite-dimensional witnesses stay out of high-fanout embedding cores.
- `Simulation/NonProductWitness.lean`: high-level pure-state example importing
  the wire-facing real simulator; owns factorization terminology and the
  rational witness without reversing the low-level state dependency or
  introducing a density-matrix hierarchy.  Its neutral name avoids claiming an
  entanglement theorem.
- `Circuit/ProductInputOrderingWitness.lean`: diagnostic leaf importing the
  existing ordering witness; owns only the ground-product-input state
  inequality and its exact coordinate checks.
- `State/ComplexPhase.lean`: low-dependency public phase-equivalence and
  invariance leaf; normalized columns remain the concrete state representation
  and no quotient is introduced.
- `Circuit/BasisPreparation.lean`: finite permutation/preparation proof leaf
  importing the ordered core and permutation-matrix APIs; owns only the known
  computational-basis input correction.
- No `Simulation/DirectQuaternionToReal.lean` file was created.  The checked
  matrix reindexing has no current consumer requiring a second placed-gate or
  wire-facing translation, while the established compositional simulator
  already proves the full circuit/state/measurement result.
- `QuaternionicComputing.lean` and `AxiomAudit.lean`: touched only after all
  selected leaves and adjacent consumers compile; root changes require a full
  build.

## Boundary Checks

- Equation (63)'s coordinate order and signs must be checked entrywise.  A
  type-compatible `4N` dimension alone is not evidence that the displayed map
  equals the established composition.
- “Group isomorphism” may mean an isomorphism onto the map's image; the library
  must not claim surjectivity onto `SO(4N)` unless proved.  Public theorem names
  should say embedding/image when that is what is established.
- Proper-image witnesses must prove both target membership and nonimage with
  exact dimensions.  They cannot use an informal dimension count, and they do
  not prove circuit-width or communication lower bounds.
- Do not state quaternionic complexification is proper inside `SU(2)`; the
  low-dimensional `Sp(1) ≅ SU(2)` exception must remain visible.  Likewise do
  not state `U(1) → SO(2)` realification is proper.
- Nonfactorability of one pure encoded state is not entanglement generation by
  local gates, nonlocal signaling, mixed-state behavior, or cryptographic
  security.
- Ground-state preparation, mixed top states, routing costs, uniformity,
  finite precision, BQP, bit commitment, and physical causality require models
  absent here.  Terminal documentation is preferable to vacuous structures or
  unjustified axioms.
- No future theorem, reference implementation, commutative Kronecker shortcut,
  or source prose may replace a checked proof obligation.

## Completion Requirements

- The paper's direct `4×4` quaternion-to-real formula has a checked coordinate
  disposition and a reusable injective multiplicative/star-preserving real
  matrix map, with its relation to the proven composition explicit.
- Correct proper-image/non-surjectivity witnesses compile in qualified
  dimensions, and C-016 records the source codomain error and exceptions.
- A normalized non-real source state has a proved non-product canonical real
  encoding, without overclaiming physical consequences.
- The disjoint-gate orders have a proved state-level difference on a normalized
  product basis input, with explicit documentation that its displayed basis
  weights need not distinguish the orders.
- A known computational-basis input can be absorbed by a certified unitary
  preparation gate, and complex unit phase has a reusable ray-level invariance
  API; neither result claims a uniform input compiler or quotient semantics.
- Every traceability row has an allowed terminal status; every new material
  issue and dependent effect appears in the correction log.
- Focused leaves, adjacent consumers, strict warnings, root, full build,
  downstream smoke, axiom audit, hole/shortcut scans, and `git diff --check`
  pass and are recorded below.

## Stage Results

- Completed 2026-07-10 after verified completion of 8-RESOURCES on 2026-07-09.
- The selected leaves are implemented and pass strict focused builds:
  `Matrix/QuaternionRealification.lean`,
  `Matrix/QuaternionRealificationUnitary.lean`, `Matrix/ProperImage.lean`,
  `State/ComplexPhase.lean`, `Circuit/BasisPreparation.lean`,
  `Circuit/ProductInputOrderingWitness.lean`, and
  `Simulation/NonProductWitness.lean`.
- Equation 63 is exactly the established composition after the pure sector
  permutation `[3,1,0,2]`; all sixteen entries, `4N` cardinality,
  multiplicativity, adjoint preservation, injectivity, determinant one on
  unitaries, and the corrected embedding into `SO(4N)` compile.
- Explicit matrices prove qualified non-surjectivity for complex-to-real in
  `SO(4)`, quaternion-to-complex relative to `SU(4)`, and direct rank-one
  quaternion-to-real in `SO(4)`.  No operational lower bound is inferred.
- A normalized rational complex state has a proved non-product real encoding.
  A separate normalized ground product input gives two output rays that are
  not right-phase equivalent even though every computational-basis weight is
  equal.  This closes the state/observable distinction without a signaling,
  entanglement, or security claim.
- Known computational-basis preparation is a certified XOR permutation gate;
  complex unit right phase is an equivalence preserving basis/total weight and
  arbitrary matrix evolution.
- All paper inventory rows now have an allowed terminal status.  Corrections
  C-025 and C-026 record the direct-map isomorphism overstatement and the
  ground-state preparation ambiguity.  All 101 `FER03-*` rows have exactly one
  terminal status: 21 proved as stated, 33 corrected and proved, 28 partially
  formalized, 16 intentionally excluded, and 3 unresolved.
- Independent statement/edge-case review checked the seven selected leaves,
  all sixteen Equation 63 signs, empty and rank-one dimensions, the direct
  `SO(4)` witness, complex phase, empty-wire basis preparation, product-input
  right-phase inequivalence and all-weight equality, import layering, root
  exports, and audit coverage.  It found no Lean/code blocker; its one
  low-rank documentation qualification was applied to the root module.
- Final warning-as-error checks passed for `QuaternionicComputing.lean` and
  `Simulation/QuaternionToReal.lean`.  The final `lake build` completed all
  2,553 jobs successfully after the public-root change.
- `lake build QuaternionicComputing.AxiomAudit` completed all 2,553 jobs.  Every
  audited Stage 9 endpoint reports only the standard foundations `propext`,
  `Classical.choice`, and `Quot.sound`; no project-specific axiom appears.
- `/tmp/Stage9ImportSmoke.lean` imported only `QuaternionicComputing`, checked
  each new public family, proved `card (DirectRealIndex Bool) = 8`, and compiled
  with warnings as errors.
- Lean-only hole/project-axiom/opaque/unsafe scans and forbidden
  noncommutative-shortcut scans had no matches.  `git diff --check` passed, and
  no `.lake`, object, or Lean build artifact is tracked.
- README, architecture, conventions, mathlib API notes, traceability,
  corrections, public-root documentation, and this stage file now distinguish
  the matrix-only direct map from the canonical two-wire circuit composition.
