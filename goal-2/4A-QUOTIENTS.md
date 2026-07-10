# 4A-QUOTIENTS

## Current Facts

- Goal 2 Stages 1--3 and milestone 4A are complete. The tree has 59 Lean
  sources, the root axiom audit has 272 endpoints, and the semantic API
  manifest has 424 exact source declarations with 50 resolving consumers and
  86 direct audit targets. The frozen 936-declaration Goal 1 cohort checksum
  is unchanged.
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
- `State/Ray.lean` now supplies all three public normalized ray quotients.
  `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` nevertheless remain only
  partially formalized because descended evolution/outcomes and the checked
  embedding-orbit boundary are still 4B/4C obligations; Goal 3 may not yet mark
  them `closedByGoal2`.
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
  - the definitional `lift_mk` beta theorem;
  - `function_ext`, proving equality of functions out of the quotient from
    agreement on every normalized constructor.
- Add `RealRay.mk_eq_mk_iff_eq_or_eq_neg` as the paper-facing specialization
  showing that real-ray equality is exactly literal column equality or
  equality with the negated column.
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

- `State/Ray.lean` is a low-dependency public leaf with exactly 40 stable
  declarations. It defines three explicit normalized-state setoids, the
  `RealRay`, `ComplexRay`, and `QuaternionRay` quotient types, and the
  `RebitRay`, `QubitRay`, and `QuaterbitRay` aliases.
- Each quotient exposes `mk`, exact `mk_eq_mk_iff`, `exists_rep`,
  representative `inductionOn`, proof-checked `lift`, the `lift_mk` beta law,
  and `function_ext`. The real specialization additionally proves
  `mk_eq_mk_iff_eq_or_eq_neg`, so real-ray equality is exactly literal column
  equality or equality with the negated column.
- The state layer imports only `State.RealPhase` and `State.ComplexPhase`; it
  does not reverse the dependency into `Semantics.StatePhase`. The raw phase
  relations used by the setoids are exactly those underlying the semantic
  normalized-state wrappers. `/tmp/Stage4BDescentProbe.lean` strictly compiles
  all three distribution and unitary-evolution descents through this API.
- Named `realRayNonempty`, `complexRayNonempty`, and
  `quaternionRayNonempty` instances construct private normalized basis
  representatives from `[Nonempty I]`. Named `*RayIsEmpty` instances eliminate
  alleged rays under `[IsEmpty I]`, and the three `*_nonempty_iff` theorems
  prove the exact boundary using only `[Fintype I]`.
- `State/RayAudit.lean` remains non-root. Four aggregate theorems consume all
  40 stable declarations. Concrete diagnostics identify a rebit with its
  right `-1` sign, a qubit with its right `I` phase, and a quaterbit with its
  right `j` phase; they also exercise all `Bool` nonempty and `Empty` is-empty
  instances. Seven local axiom prints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The public root imports `State.Ray`, not `State.RayAudit`. The root axiom
  file adds eight direct quotient/inhabitation endpoints and now has 272
  commands, all reporting only the same three standard axioms.
- `docs/Goal2SemanticAPIManifest.json` now contains exactly 424 entries. The
  first 384 are structurally unchanged; all 40 Stage 4A declarations have
  seven axes, one of four resolving aggregate consumers, and exact source
  ordering. Eight are direct audit targets, bringing totals to 50 consumers
  and 86 direct targets. Generated strict Lean checks resolve all 424 names
  and all 50 consumers. The frozen Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- Focused builds pass for `State.Ray` (2,346 jobs) and `State.RayAudit` (2,347
  jobs); adjacent `StatePhase`, `Measurement`, and `Circuit.Basic` builds pass
  at 2,352 jobs; the public root passes at 2,563 jobs; and the combined
  quotient, diagnostic, root, and axiom targets pass at 2,565 jobs. Strict
  source checks pass for both new leaves, the public root, root audit, generated
  manifest checks, and the Stage 4B descent probe.
- Forbidden-hole/axiom/unsafe/opaque/heartbeat scans, public diagnostic
  boundary, exact manifest, prefix-preservation, checksum, whitespace,
  artifact, and `git diff --check` checks pass.
- Documentation now records quotient equality and the no-canonical-
  representative/cross-model-map boundaries. `FER03-D01-REBIT` and
  `FER03-FND-COMPLEX-STATE-RAY` deliberately remain **partially formalized**
  and not `closedByGoal2`: descended evolution/outcomes remain 4B work and the
  embedding-orbit boundary remains 4C work. No new correction was required.
