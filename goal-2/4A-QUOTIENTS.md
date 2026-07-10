# 4A-QUOTIENTS

## Current Facts

- Goal 2 Stages 1--3 are complete. The public tree has 57 Lean sources, the
  root axiom audit has 264 endpoints, and the semantic API manifest has 384
  exact source declarations with 46 resolving consumers and 78 direct audit
  targets. The frozen 936-declaration Goal 1 cohort checksum is unchanged.
- `State.RealState I`, `State.ComplexState I`, and `State.QuaternionState I`
  are subtypes of finite columns carrying an exact total-weight-one proof.
  They are concrete representatives, not quotient values.
- `Real.SignEquivalent`, `Complex.RightPhaseEquivalent`, and
  `Quaternion.RightPhaseEquivalent` are already proved equivalence relations
  on raw columns. The quaternionic relation acts strictly on the right.
- `Semantics.RealStatePhaseEq`, `ComplexStatePhaseEq`, and
  `QuaternionStatePhaseEq` restrict those same relations to normalized state
  representatives and have complete equivalence, distribution, raw-action,
  and normalized-unitary-evolution APIs.
- There is currently no public normalized ray quotient. Consequently
  `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` remain only partially
  formalized and Goal 3 may not yet mark them `closedByGoal2`.
- Strict probes at `/tmp/Stage4ARayProbe.lean` and
  `/tmp/Stage4RayScratch.lean` validate plain explicit `Setoid`/`Quotient`
  representations, constructor equality iff the intended phase relation,
  representative induction/lifting, and the exact boundary
  `Nonempty (Ray I) ↔ Nonempty I` under only `[Fintype I]`.
- A normalized state cannot exist on an empty index type because its empty
  total-weight sum is zero, not one. Conversely, a nonempty finite index has a
  normalized computational-basis representative over all three scalar types.
  The quotient types therefore admit sound `Nonempty` and `IsEmpty` instances
  with explicit index hypotheses.

## Updated Assumptions

- Use ordinary Lean `Quotient` over three explicit state-specific setoids.
  A group-orbit quotient adds unnecessary algebraic infrastructure and does
  not improve the required equality or lift principles.
- Put the low-dependency data layer in `State/Ray.lean` under
  `QuaternionicComputing.State`. It should import the existing real and
  complex phase leaves, which already expose the quaternionic raw relation
  through `State.Basic`, and should not import circuits, operator phase,
  diagnostics, or the public root.
- Define each setoid relation directly with the corresponding raw-column phase
  predicate. Its `iseqv` proof must lift reflexivity, symmetry, and
  transitivity componentwise to normalized subtypes; a raw-function
  `Equivalence` theorem is not itself definitionally the required subtype
  `Equivalence` value.
- Constructor equality must be an iff with real sign, complex unit right
  phase, or quaternion unit right phase. Do not quotient by arbitrary nonzero
  scalars, all equal basis distributions, left quaternion phase, or operator
  projective action.
- Stage 4A supplies quotient data and faithful elimination interfaces only.
  Descended unitary/circuit evolution, basis weights, distributions, events,
  and deterministic postprocessing belong to 4B; the realification top-sector
  rotation boundary belongs to 4C.
- The two transferred paper rows remain open after 4A alone. They close only
  after 4B supplies evolution and outcome operations and 4C records the
  embedding-orbit boundary and all dependent documentation.

## Big Picture Objective

Introduce reusable normalized real, complex, and quaternionic ray types whose
Lean equality is exactly the already-audited physical phase relation, with
faithful constructors and eliminators and honest empty-index behavior.

## Detailed Implementation Plan

- Add `State/Ray.lean` with public `realRaySetoid`, `complexRaySetoid`, and
  `quaternionRaySetoid`, followed by `RealRay I`, `ComplexRay I`, and
  `QuaternionRay I`.
- Add `RebitRay`, `QubitRay`, and `QuaterbitRay` aliases for the paper's
  two-level state spaces without introducing separate relations.
- In each ray namespace, expose a minimal reusable interface:
  - `mk` from an already-normalized representative;
  - `mk_eq_mk_iff` with exactly the scalar-correct raw phase relation;
  - `exists_rep` showing every quotient value has a normalized
    representative;
  - `inductionOn` for representative-independent propositions;
  - `lift` for representative-independent data;
  - the definitional `lift_mk` beta theorem.
- Use private normalized basis representatives to provide named
  `realRayNonempty`, `complexRayNonempty`, and `quaternionRayNonempty`
  instances under `[Nonempty I]`, and named `realRayIsEmpty`,
  `complexRayIsEmpty`, and `quaternionRayIsEmpty` instances under `[IsEmpty I]`.
  Export the three exact `*_nonempty_iff` theorems.
- Add `State/RayAudit.lean` outside the public root. Give every stable
  declaration a named aggregate consumer. Include concrete rebit `-1`, qubit
  `I`, and quaterbit right-`j` constructor equalities; explicit `Bool`
  nonemptiness and `Empty` emptiness checks; and representative axiom prints.
- Promote only `State/Ray.lean` through `QuaternionicComputing.lean`. Add every
  stable declaration exactly once to `Goal2SemanticAPIManifest.json`, with all
  seven axes, resolving audit consumers, and representative root axiom targets.
  Preserve the first 384 entries and the frozen Goal 1 checksum.
- Fold the new quotient meanings and the still-pending 4B/4C obligations into
  conventions, architecture, equivalence classification, traceability,
  release, axiom, and Goal 3 prerequisite documentation. Do not close either
  transferred source row prematurely.

## Build Structure

- `State/Ray.lean`: low-dependency public quotient types, constructors,
  eliminators, beta laws, and index-inhabitation facts.
- `State/RayAudit.lean`: non-root consumers and scalar/empty-index examples.
- `QuaternionicComputing.lean`: imports only the stable ray leaf.
- `QuaternionicComputing/AxiomAudit.lean`: representative equality,
  elimination, and inhabitation endpoints; it never imports `RayAudit`.
- Focused builds target `State.Ray` and `State.RayAudit`. Adjacent checks target
  `StatePhase`, `Measurement`, the Stage 4B descent probe, the public root, and
  the explicit axiom audit.

## Boundary Checks

- A quotient value contains a normalized representative by construction. It
  is not a quotient of arbitrary raw columns and cannot exist on an empty
  finite index type.
- Real quotient equality permits only a square-one real sign; complex equality
  permits one unit complex right phase; quaternion equality permits one unit
  quaternion strictly on the right.
- Equality of basis distributions is weaker than ray equality and is not used
  as the quotient relation.
- Ray equality is state equality modulo phase, not operator global phase,
  projective operator action, channel equality, or all-effect equality.
- No cross-model map is asserted. In particular, complex phase under
  realification is not silently identified with ordinary real sign.
- `lift` requires an actual proof that the supplied function respects the
  corresponding phase relation; metadata or proof irrelevance alone is not a
  descent certificate.

## No-Cheating Checks

- Do not define a quotient relation by the desired quotient equality theorem.
- Do not use all nonzero scalars, left quaternion phase, equal weights, or an
  impossible normalized-state premise to collapse representatives.
- Do not add a canonical representative choice or pretend `Quotient.out` is a
  phase-invariant observable.
- Do not add `Nonempty (Ray I)` without an explicit `Nonempty I` premise, or
  erase the `IsEmpty I` boundary.
- Do not count the existence of the quotient type as descended dynamics or
  outcomes; those are separate 4B proofs.
- No `sorry`, `admit`, `sorryAx`, project axiom, unsafe/opaque shortcut,
  heartbeat override, diagnostic root import, or metadata-only proof.

## Completion Requirements

- All three public quotient types compile with transparent setoid meanings and
  constructor equality iff the correct phase relation.
- Every quotient value supports representative induction and a proof-checked
  lift; all beta rules compile without choosing a representative.
- Nonempty finite indices yield normalized rays and empty indices yield empty
  ray types, with exact iff theorems and concrete `Bool`/`Empty` consumers.
- Rebit sign, qubit complex phase, and quaterbit right-phase examples compile;
  no left quaternion or distribution quotient appears.
- A non-root audit consumes every stable declaration and the public root
  imports no diagnostic leaf.
- Manifest exact-set, seven-axis, public-name, consumer-resolution,
  direct-audit, preserved-prefix, and frozen-checksum checks pass.
- Focused, adjacent, public-root, explicit-audit, warning-as-error, forbidden-
  token, diagnostic-boundary, artifact, whitespace, and `git diff --check`
  verification passes under `BUILD-PLAN.md`.
- Documentation states what 4A proves and leaves the two paper rows and all
  descended operations explicitly pending for 4B/4C.

## Stage Results

- Milestone active. Strict probes establish the representation and API route;
  no tracked Stage 4A implementation has yet been promoted.
