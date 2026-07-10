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
- `/tmp/Stage4CRotationProbe.lean` and `/tmp/Stage4CScratch.lean` strictly
  compile the direct sector action, identity/right-composition laws, norm and
  bottom-weight scaling, normalized rotation, independently proved orbit
  equivalence, quotient API, normalized decoder, and a canonical
  `ComplexRay I ≃ RealSectorOrbit I` with no nonempty-index assumption.
- `/tmp/Stage4CNoDescentProbe.lean` strictly compiles a stronger ordinary-ray
  boundary than the initial Unit witness: for every normalized complex state,
  phase `I` gives the same source `ComplexRay` but a different target
  `RealRay` under either canonical column. For unit `eta`, the target real ray
  is unchanged exactly when `eta = 1 ∨ eta = -1`; a constructor-compatible
  canonical-column lift exists exactly when `IsEmpty I`.
- `FER03-D01-REBIT` and `FER03-FND-COMPLEX-STATE-RAY` remain partially
  formalized and not `closedByGoal2` solely because this embedding-orbit
  boundary has not yet been proved and audited.

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

- In progress.
