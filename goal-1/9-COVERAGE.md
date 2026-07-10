# 9-COVERAGE

## Current Facts

- Stages 1–8 establish the central scalar, matrix, normalized-state, placed
  circuit, fixed/scheduled simulation, ordering, resource, compiler-bound, and
  deterministic-postprocessing results.  The public root, full build, and
  axiom audit are green.
- The remaining temporary traceability rows are narrow.  The main mathematical
  items are the paper's direct `4×4` real quaternion representation, corrected
  non-surjectivity/proper-image statements, and a concrete non-product encoded
  state.  Several foundational or interpretive rows need terminal scope
  decisions rather than large new frameworks.
- Equation (63) gives a specific signed coordinate matrix using quaternion
  components `Re`, `Im`, `Jm`, and `Km`.  The library already has a verified
  composition `Matrix.realify (Quaternion.complexify A)`, but its nested sum
  basis order is not visibly the paper's displayed coordinate order.  The two
  maps must be compared by an explicit reindexing, not identified by prose.
- The paper calls the direct map an “isomorphism from `Sp(N)` to `SO(4N)`.”
  Dimension and image considerations show that the useful corrected statement
  is an injective star-preserving homomorphism *into* `SO(4N)`, not
  surjectivity onto the whole special orthogonal group.
- The paper's converse sentence names `Sp(2N)` as the codomain of
  quaternionic complexification, although the target is complex unitary/
  special-unitary space and the image is the symplectic-preserving subgroup.
  Properness also needs dimension qualifications: `Sp(1) ≅ SU(2)`, while the
  analogous `U(1) → SO(2)` realification is onto.
- A simple normalized complex state with amplitudes `3/5` and `(4/5)i`
  realifies to a two-sector column with two nonzero diagonal coordinates and
  zero cross coordinates.  It is a rational, square-root-free witness that the
  added top wire need not factor from the bottom wire.
- Mixed-top claims require a density/operator API and are not prerequisites of
  any pure-state or observable theorem.  Ground-state “without loss of
  generality” requires an input-preparation gate library and a uniform
  generator.  Physical causality, entanglement analogy, bit-commitment
  security, and BQP/open-question prose lack formal models in the source.
- Repository-root `BUILD-PLAN.md` remains authoritative for ownership,
  focused/adjacent builds, boundary scans, and fold-back.

## Updated Assumptions

- The direct real representation should be defined in the paper's coordinate
  order and proved equal to a reindexing of the already verified composition.
  Multiplication, adjoint, injectivity, unitarity/orthogonality, determinant
  one, and circuit compatibility should then be inherited rather than
  reproved by a fragile 16-block calculation.
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
  preservation, and the exact relationship to the existing two-step circuit
  operator.  Correct “isomorphism to `SO`” to an injective image statement.
- Add a proper-image witness leaf.  Exhibit a concrete special-orthogonal
  real matrix in dimension four outside realification of `2×2` complex
  matrices, and a concrete complex special-unitary/unitary matrix in dimension
  four outside quaternionic complexification/symplectic image.  Record the
  `N=1` exception rather than asserting universal properness.
- Add a narrow state example defining pure top/bottom factorization and a
  normalized rational complex source state whose canonical real encoding is
  proved nonfactorable.  Keep the general definition reusable and the heavy
  coordinate proof in the example leaf.
- Decide the complex-ray row with the minimum sound API: prove unit-complex
  phase preserves finite basis distributions if not already available, but do
  not introduce a quotient that no theorem consumes.
- Revisit every remaining temporary traceability row.  Assign terminal statuses
  to the norm-preserver background fact, ground-state preparation, real-gate
  interpretation, mixed-top extensions, physical/nonlocal-time prose,
  bit-commitment claim, converse implications, and explicit open questions.
  Add correction C-025 if Equation (63)'s isomorphism wording or coordinate
  formula requires a material repair.
- Promote stable leaves to the root/audit only after focused and adjacent
  consumers compile; update README, architecture, conventions, API notes,
  traceability, and corrections.

## Build Structure

- `Matrix/DirectRealification.lean`: proof leaf importing the two existing
  embedding definitions plus their unitary/determinant consequences; owns the
  direct coordinate map, reindex equivalence, and inherited algebra.  It does
  not import circuits or simulations.
- `Matrix/ProperImage.lean`: diagnostic/public correction leaf importing
  `Matrix/Determinant` and direct/complexification group facts; explicit
  finite-dimensional witnesses stay out of high-fanout embedding cores.
- `State/EntanglementWitness.lean`: narrow pure-state example importing the
  real state encoding; owns factorization terminology and rational witness,
  without a density-matrix hierarchy.
- Optional `State/ComplexPhase.lean`: low-dependency public phase-invariance
  leaf only if the source ray row benefits from a reusable consumed theorem.
- A circuit direct-map bridge, if needed, belongs in a thin
  `Simulation/DirectQuaternionToReal.lean` consumer rather than the matrix
  leaf; it must visibly agree with the established compositional simulator.
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
- Every traceability row has an allowed terminal status; every new material
  issue and dependent effect appears in the correction log.
- Focused leaves, adjacent consumers, strict warnings, root, full build,
  downstream smoke, axiom audit, hole/shortcut scans, and `git diff --check`
  pass and are recorded below.

## Stage Results

- In progress.  Stage opened after verified completion of 8-RESOURCES on
  2026-07-09.
