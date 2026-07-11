# 4C-EMBEDORBIT

## Current Facts

- Goal 2 Stages 1--3 and milestones 4A/4B are independently complete. The
  current tree has 65 Lean sources, 487 exact manifest entries, 54 resolving
  aggregate consumers, 100 direct root-audit entries, and 286 root audit
  commands using only `propext`, `Classical.choice`, and `Quot.sound`.
- `ComplexRay I` identifies normalized complex representatives under one unit
  complex phase on the right. `RealRay (I ⊕ I)` identifies normalized real
  representatives only under a real sign. These are different orbit
  relations; realification changes both the scalar and the index space.
- `State.realColumn0State` and `realColumn1State` map normalized complex
  representatives to normalized doubled real representatives. Raw
  `realColumn0`/`realColumn1` are injective, intertwine arbitrary compatible
  matrix action, preserve total weight, and preserve bottom-system basis
  weights after the two real sectors are summed.
- With the convention `realColumn0 v = (re v, -im v)` and
  `realColumn1 v = (im v, re v)`, direct algebra predicts
  `realColumn0 (v * eta) = eta.re • realColumn0 v - eta.im • realColumn1 v`
  and
  `realColumn1 (v * eta) = eta.im • realColumn0 v + eta.re • realColumn1 v`.
  For unit `eta`, this is an orthogonal top-sector rotation, not generally a
  real sign.
- The smallest anticipated obstruction is one-dimensional: normalized
  representatives with amplitudes `1` and `I` define the same `ComplexRay
  Unit`, while their first real columns occupy different doubled sectors and
  therefore should not define the same `RealRay (Unit ⊕ Unit)`.
- Existing simulations consume `realTopCombination`, `realTopState`, both
  canonical columns, bottom-sector marginal weights, and their matrix-action
  intertwiners. They do not currently consume a named rotation-orbit quotient.
  Strict probes now show that a separate relation/type improves those real
  consumers: both canonical columns and every normalized pure top-rebit
  encoding occupy one sector orbit, and only the bottom marginal distribution
  descends through that orbit.
- `State/RealificationOrbit.lean` now exports the 66-declaration core tested by
  the strict probes: the direct action and its ordered laws, normalized
  rotations, the independently proved `RealSectorPhaseEquivalent`, its
  quotient, normalized encoder/decoder equivalence, and
  `ComplexRay I ≃ RealSectorOrbit I`. Both canonical columns and every
  normalized pure top-rebit encoding are named consumers.
- `State/RealificationOrbitObservables.lean` exports ten declarations. It
  descends exactly the two-sector bottom marginal distribution and proves
  `ComplexRay.realificationOrbit_distribution`; it does not attach the
  generally phase-sensitive full doubled-real distribution to the orbit.
- `State/RealificationOrbitBoundary.lean` exports eight declarations. For
  either canonical column, a unit phase preserves the ordinary target
  `RealRay` exactly at `eta = 1 ∨ eta = -1`; phase `I` gives explicit
  inequality, and a representative-compatible lift from `ComplexRay I` exists
  exactly when `IsEmpty I`.
- The combined 84-declaration surface theorem-checks correction C-027: source
  rays must be formed before asking whether a representative embedding
  descends. Complex phase becomes a sector rotation, not ordinary real-sign
  equality. The representative matrix-intertwining and bottom-outcome
  theorems remain valid and are not weakened by this correction.
- `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` now have their complete
  quotient, descended-operation, and embedding-boundary evidence. Their
  canonical traceability rows are **proved as stated** and recorded
  `closedByGoal2`; the Stage 4C release gate remains open only for final
  audit/manifest/root/build evidence.

## Updated Assumptions

- A map `ComplexRay I → RealRay (I ⊕ I)` induced by either canonical column is
  not assumed. It may be exported only if representative independence under
  complex phase is proved; the expected `1`/`I` example should refute it.
- First prove the phase-to-top-rotation formulas on raw columns and normalized
  state wrappers. These formulas determine every sign and multiplication
  order before an orbit relation is designed.
- Define the real-sector rotation relation directly and quotient it. It has
  concrete public consumers: a well-defined representation equivalence from
  `ComplexRay`, equality of the two canonical-column orbit values, arbitrary
  `realTopState` orbit equality, and a descended bottom distribution. Call the
  quotient `RealSectorOrbit`, never `RealRay` or `RealificationRay`.
- The orbit quotient's relation must be independently
  proved reflexive, symmetric, and transitive; it cannot be defined by the
  desired quotient equality. Rotation composition must preserve order and the
  normalization proof must be mathematical rather than proof-irrelevance
  alone.
- Export the general phase-rotation theorem and strong no-descent theorem
  alongside the orbit type. The orbit equivalence is a chosen-sector
  representation equivalence, not channel equality or computational-model
  equivalence.
- Do not treat bottom-distribution equality as target real-ray equality. The
  doubled real sectors are marginalized observations, not erased state data.
- This stage concerns complex-to-real state realification. It does not yet
  classify all quaternion-to-complex cross-model simulations, channels,
  arbitrary effects, or approximation; those remain in their assigned later
  stages.

## Big Picture Objective

Prove exactly how complex unit phase acts after state realification, formalize
the strongest useful top-sector orbit interface justified by real consumers,
and theorem-check that the canonical encoding cannot be mistaken for an
ordinary map from complex rays to real sign rays.

## Detailed Implementation Plan

- Strict-probe the raw formulas for `realColumn0` and `realColumn1` under
  pointwise complex right multiplication by an arbitrary scalar `eta`.
- Specialize to `ComplexState.rightPhase` and prove the exact normalized
  top-sector coefficient formulas under `Complex.normSq eta = 1`.
- Define the minimal real-sector quarter-turn/rotation operation needed to
  express those formulas uniformly. Prove its coordinate equations,
  identity/composition behavior, total-weight preservation under unit
  coefficients, and compatibility with the two canonical columns.
- Define `RealSectorPhaseEquivalent` from the direct unit action, prove its
  equivalence laws and decoder characterization, and form `RealSectorOrbit`.
  Expose the standard constructor/induction/lift interface, normalized decoder,
  `ComplexRay.realificationOrbit`, its inverse, and the canonical equivalence.
- Prove both canonical columns and every normalized `realTopState` give the
  same orbit value. This is the immediate real consumer justifying the
  quotient rather than speculative infrastructure.
- Descend only the bottom marginal finite distribution to `RealSectorOrbit`
  and identify it with `ComplexRay.distribution` under the representation
  equivalence. Explicitly exclude the full doubled-real basis distribution,
  which sector rotations generally change.
- Construct normalized `Unit`-indexed complex states with amplitudes `1` and
  `I`. Prove they are equal after `ComplexRay.mk`, but both canonical
  real-column images are unequal after `RealRay.mk`.
- Export a functional no-go theorem: no function from `ComplexRay Unit` to
  `RealRay (Unit ⊕ Unit)` can agree with `realColumn0State` on every normalized
  representative; prove the column-one analogue when it adds symmetric useful
  evidence.
- Add a non-root diagnostic leaf consuming every new stable declaration and
  exercising the general formulas, the normalized phase example, the no-go
  theorem, bottom marginal preservation, and any chosen orbit API.
- Promote only stable public leaves through `QuaternionicComputing.lean`; add
  every stable declaration exactly once to the Goal 2 manifest with all seven
  axes, resolving consumers, and representative root axiom endpoints.
- Fold the precise boundary into architecture, conventions, equivalence,
  traceability, corrections if needed, release, axiom, and Goal 3 docs. Close
  the two transferred source rows only when their quotient, descent, and
  embedding-boundary evidence is complete.

## Build Structure

- `State/RealificationOrbit.lean`: direct sector action, normalized rotation,
  independently proved relation, quotient interface, decoders, representation
  equivalence, and canonical-column/arbitrary-top orbit consumers. It imports
  the existing representative realification and ray leaves, not diagnostics or
  the public umbrella.
- `State/RealificationOrbitObservables.lean`: bottom marginal distribution and
  its orbit/source-ray bridge. It does not export full target-basis
  distribution descent.
- `State/RealificationOrbitBoundary.lean`: exact `±1` ordinary-real-ray
  survival classification and constructor-compatible lift-existence iff
  `IsEmpty I` for both canonical columns.
- `State/RealificationOrbitAudit.lean`: non-root complete consumers, containing
  complete aggregate consumers, concrete `1`/`I` diagnostics, and local axiom
  prints.
- Focused builds target each new leaf. Adjacent builds include
  `State.RayObservables`, `State.RayEvolution`, `Simulation.ComplexToReal`,
  the public root, and the explicit root axiom audit. Warning-as-error checks
  cover every touched source.

## Boundary Checks

- Source and target spaces differ: complex `I` versus real `I ⊕ I`. No
  same-space equality relation may classify the encoding.
- Source complex phase is a unit complex scalar on the right. Its target
  action is a two-sector real rotation; it is not generally the real sign
  relation used by `RealRay`.
- Equality after bottom-sector marginalization is weaker than equality of
  doubled real states or real rays.
- Neither canonical column is a canonical representative of a complex ray.
  Choosing column zero or one fixes an encoding convention, not a
  phase-invariant real sign ray.
- The no-go theorem must use inhabited normalized examples and cannot rely on
  an empty index, impossible normalization premise, or unequal source rays.
- No channel, density, all-effect, schedule, resource, or approximation claim
  is introduced here.

## No-Cheating Checks

- Do not define a target orbit relation by equality of a proposed quotient or
  by equality of bottom distributions.
- Do not postulate that complex phase becomes `±1`, erase the added sector, or
  choose a representative with `Quotient.out`/`Classical.choose`.
- Do not prove only that two raw columns differ and call it a ray-level no-go;
  the source equality and target ray inequality must both compile on normalized
  states.
- Do not manufacture an orbit quotient without a named consumer or count a
  diagnostic label as a semantic theorem.
- No `sorry`, `admit`, `sorryAx`, new axiom, unsafe/opaque shortcut, heartbeat
  override, impossible hypothesis, public audit import, or silent change to
  the frozen cohort.

## Completion Requirements

- General raw and normalized theorems prove the exact target rotation induced
  by complex right phase, with the repository's sign convention.
- A normalized concrete source-phase equality and target-real-ray inequality
  prove that neither canonical column silently descends to ordinary real-ray
  equality; a functional no-go theorem rules out the corresponding induced
  map.
- Any exported orbit relation/type has equivalence laws, a real consumer,
  correct bottom-observation semantics, and explicit same-/cross-space axes.
  The canonical equivalence is documented as a representation equivalence,
  not a model/channel equivalence.
- A non-root audit consumes every stable declaration and the public root
  imports no diagnostic leaf.
- Both transferred ray rows have proof-bearing quotient, operation-descent,
  and embedding-boundary evidence and are moved to the strongest justified
  final status with all dependent effects recorded.
- Manifest exact-set, seven-axis, public-name, consumer-resolution,
  direct-audit, preserved-prefix, and frozen-checksum checks pass.
- Focused, adjacent, public-root, explicit-audit, warning-as-error,
  forbidden-token, diagnostic-boundary, artifact, whitespace, and
  `git diff --check` verification passes under `BUILD-PLAN.md`.

## Stage Results

- `State/RealificationOrbit.lean` contributes exactly 66 stable declarations.
  `realSectorAction` implements
  `(x,y) ↦ (re(eta)*x + im(eta)*y, -im(eta)*x + re(eta)*y)` and has
  coordinate, identity, multiplication, source-right-order composition, and
  `I` quarter-turn laws. The two canonical-column formulas fix the exact top
  coefficients `(eta.re,-eta.im)` and `(eta.im,eta.re)`, and total squared
  weight is scaled by `Complex.normSq eta`.
- Unit actions package as `RealState.sectorRotation`.
  `RealSectorPhaseEquivalent` is defined directly by existence of a unit
  action and is proved reflexive, symmetric, and transitive. Decoding with
  `complexOfRealColumn0` identifies it exactly with complex right phase; it is
  not defined from quotient equality or from outcomes.
- `RealSectorOrbit` supplies `mk`, exact constructor equality,
  representative existence, induction, invariant lifting, and function
  extensionality. `realColumn0StateEquiv` gives the normalized representative
  equivalence, while `ComplexRay.realificationOrbit`,
  `RealSectorOrbit.toComplexRay`, and `complexRayEquivRealSectorOrbit` prove the
  exact ray/orbit equivalence without a nonempty-index premise.
- The canonical second column and every `realTopState top psi` give the same
  orbit as the first column. These are concrete consumers of the orbit rather
  than speculative quotient infrastructure.
- `State/RealificationOrbitObservables.lean` contributes exactly ten stable
  declarations: scalar and unit bottom-weight laws, the normalized
  representative bottom distribution and phase invariance, quotient descent,
  both canonical-column bridges, and equality with
  `ComplexRay.distribution`. Finite events and deterministic postprocessing
  follow through the existing `FiniteDistribution` API; no full doubled-real
  distribution descent is claimed.
- `State/RealificationOrbitBoundary.lean` contributes exactly eight stable
  declarations. For either canonical column, ordinary real-ray survival is
  iff the phase is `±1`; `I` is an explicit counterexample. The two no-lift
  theorems cover every nonempty finite index, and the two iff theorems sharpen
  the boundary to existence exactly on `IsEmpty I`.
- Correction C-027 records the source-order issue: physical source values are
  rays before `h₀` or `h₁` is applied. Neither representative map descends
  to `RealRay` on a nonempty space; the correct codomain is
  `RealSectorOrbit`, and only the bottom marginal is invariant. Existing raw
  state intertwining and bottom-outcome results remain correct.
- `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` are now **proved as
  stated** and `closedByGoal2`. This closes only normalized pure-state ray
  semantics. Mixed top states, generic density/channel claims, and the
  phase-kickback interpretation remain assigned to Goal 3.
- **Root closure evidence pending:** record the final non-root audit aggregate
  allocation and local axiom prints; public-root imports; semantic-manifest
  total, consumer count, and direct-audit count; focused/adjacent/root/audit
  build job counts; generated name/consumer validation; exact axiom set; and
  forbidden-token, boundary, artifact, whitespace, checksum, and diff checks.
