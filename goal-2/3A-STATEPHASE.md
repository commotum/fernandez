# 3A-STATEPHASE

## Current Facts

- Stage 2 exports exact state-independent operator/circuit relations and the
  distinct basis-weight, fixed-input, all-basis-input, all-normalized-pure-input,
  and normalized-distribution relations. Its stable API manifest has 61
  entries and is available to this milestone without importing diagnostics.
- `Complex.RightPhaseEquivalent` and
  `Quaternion.RightPhaseEquivalent` already compare raw columns by a unit
  scalar on the right, are equivalence relations, preserve basis/total weights,
  and commute with arbitrary compatible matrix action.
- There is no corresponding real sign relation. `State.RealState` is a
  normalized representative type, not a quotient by `±1`.
- Frozen rows `EQC-001-Q-LEFT-PHASE-FAILURE`,
  `EQC-002-Q-RIGHT-RAY`, `EQC-003-C-RIGHT-RAY`, and
  `EQC-043-REAL-SIGN-RAY` are owned by this milestone.
- Inventory review found a material evidence error in `EQC-001`:
  `Quaternion.phaseWitnessInput = (1,1)` has total quaternionic weight `2`,
  not `1`. The existing left-phase no-go theorem is valid for raw columns but
  is not a normalized-state witness.
- A warning-as-error probe recovered the intended stronger result with
  amplitudes `3/5` and `4/5`: the column has total weight one, is
  left-phase equivalent to its left `i` multiple before the
  `diag(1,j)` evolution, and is not left-phase equivalent afterward.
- One early expanded normalized circuit-evolution proof hit the default
  deterministic heartbeat limit during reduction. A later independent strict
  probe compiled all three direct theorem shapes, so this is not a mathematical
  or current API blocker. Stage 3A exports cheap raw ordered-circuit lifts and
  normalized matrix-unitary lifts; Stage 4 still owns a named descended circuit
  operation and should choose a compact definition rather than raise heartbeats.

## Updated Assumptions

- Real phase is multiplication on the right by a real scalar `s` satisfying
  `s*s=1`; this is equivalent to `s=1 ∨ s=-1`.
- Complex phase is written on the right for API uniformity and is central by
  commutativity.
- Quaternionic state phase is strictly right-sided. Left multiplication appears
  only in the rejected-convention audit.
- `ExactStateEq` should compare normalized state representatives, not erase
  subject type by wrapping arbitrary equality.
- No `Nonempty` assumption is needed for equivalence laws. Normalized states
  on an empty basis may be uninhabited, but the relations remain well-formed.
- Stage 3A supplies normalized representative relations and consequences.
  Quotient types, quotient equality, and descended operations remain Stage 4.

## Big Picture Objective

Complete the real/complex/quaternion normalized state-phase layer with explicit
scalar side and normalization semantics, repair the misleading normalized
left-phase witness claim, and connect phase equality to Stage 2 basis weights
and finite distributions without claiming operator global phase or channel
semantics.

## Detailed Implementation Plan

- Add `State/RealPhase.lean`, importing only `State.Basic`. Define
  `Real.SignEquivalent`, prove its equivalence laws and `±1`
  characterization, and add real basis/total-weight and matrix-action
  preservation.
- In the real leaf, add `RealState.rightSign`, its coordinate and
  basis-weight theorems, and the normalized state/sign-equivalence witness.
- Add `Semantics/StatePhase.lean`, importing `Semantics.Measurement`,
  `State.RealPhase`, `State.ComplexPhase`, and `State.Unitary`. Define
  `ExactStateEq`, `RealStatePhaseEq`, `ComplexStatePhaseEq`, and
  `QuaternionStatePhaseEq`.
- Prove equivalence laws, exact-to-phase implications, explicit phase
  constructors, `BasisWeightEq` and `NormalizedDistributionEq`
  consequences, compatible raw matrix-action preservation, and normalized
  unitary-evolution preservation for all three scalar systems.
- Add `Semantics/StatePhaseAudit.lean` as a non-root diagnostic leaf. Prove
  that the old witness has weight two, add the normalized `3/5,4/5`
  left-phase counterexample, and exercise real `-1`, complex `I`, and
  quaternion `j` phases plus exact-to-phase and phase-to-distribution APIs.
- Add every stable declaration from the two public leaves to the Goal 2
  semantic API manifest only after named consumers compile. Keep audit
  declarations outside that manifest.
- Update `EQC-001` evidence and any correction/traceability prose to
  distinguish the old raw witness from the repaired normalized witness. Finalize
  the four owned family classifications without closing Stage 4 quotient rows.

## Build Structure

- `State/RealPhase.lean`: reusable real scalar/state phase API; no semantic
  wrappers, distributions, circuits, or audits.
- `Semantics/StatePhase.lean`: public normalized-state semantic vocabulary and
  consequences; depends on the Stage 2 measurement leaf and three state-phase/
  unitary leaves.
- `Semantics/StatePhaseAudit.lean`: diagnostic/counterexample consumers only;
  not imported by either public leaf or the public root.
- Public-root promotion waits until both public leaves and the diagnostic
  consumer compile. If promoted, root and explicit AxiomAudit builds are
  mandatory.
- Focused builds:
  `lake build QuaternionicComputing.State.RealPhase`,
  `lake build QuaternionicComputing.Semantics.StatePhase`, and
  `lake build QuaternionicComputing.Semantics.StatePhaseAudit`.
- Adjacent consumers include `State.Unitary`, `Semantics.Measurement`, and
  the Stage 4 quotient probe; no circuit umbrella import is needed.

## Boundary Checks

- Real sign, complex unit phase, and quaternion unit right phase are different
  scalar relations with parallel normalized wrappers.
- State representative phase is not literal equality and is not yet quotient
  equality.
- Quaternionic phase witnesses always occur on the right in public APIs.
- The normalized left-phase counterexample is a rejection certificate, not a
  competing physical relation.
- Phase implies computational-basis distribution equality; the converse is not
  claimed and will receive exact strictness witnesses in Stage 8.
- No state-phase theorem is labeled operator global phase, projective operator
  action, basis-column phase, channel equality, or cross-model simulation.
- The old raw witness remains valid but may not be described as normalized.

## No-Cheating Checks

- `Real.SignEquivalent` is defined by a genuine unit-sign witness and is not
  defined as equality of weights.
- Normalized wrappers reuse existing raw relations; they do not define phase by
  the consequences to be proved.
- Exact-to-phase proofs construct the identity phase explicitly.
- Distribution consequences pass through `BasisWeightEq` and
  `basisWeightEq_iff_normalizedDistributionEq`.
- Unitary-evolution theorems use the actual normalized constructors and
  unitarity proofs; raw matrix phase naturality does not by itself fabricate a
  normalized output.
- No heartbeat increase, impossible normalization premise, `sorry`, `admit`,
  project axiom, unsafe/opaque shortcut, or tautological registry label is
  permitted.

## Completion Requirements

- Real sign equivalence has checked `refl`, `symm`, `trans`,
  `Equivalence`, and exact `±1` characterization theorems.
- All four normalized relations have distinct public signatures, equivalence
  laws, exact-to-phase lifts, and named real consumers.
- Real, complex, and quaternion phase equality imply the correct
  `BasisWeightEq` and `NormalizedDistributionEq` with no scalar-side error.
- Raw compatible matrix action and normalized unitary evolution preserve each
  scalar's phase relation.
- The old witness's total weight `2` and the new normalized left-phase failure
  both compile in the diagnostic leaf.
- The four owned frozen cohort rows have proof-bearing strongest
  classifications, with the `EQC-001` inventory wording repaired.
- Stable new exports appear exactly once in the API manifest; diagnostic
  declarations do not.
- Focused leaves, adjacent consumers, public root if promoted,
  warning-as-error checks, axiom audits, manifest validation, hole/shortcut/
  artifact/whitespace scans, and `git diff --check` pass.

## Stage Results

- Milestone active. The representation probe has fixed the scalar conventions,
  exposed the old witness's missing normalization, and validated a normalized
  repair. Repository implementation and release evidence remain in progress.
