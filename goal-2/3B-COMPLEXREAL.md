# 3B-COMPLEXREAL

## Current Facts

- Stage 3A exports literal normalized-state equality plus real-sign, complex
  unit-right-phase, and quaternionic unit-right-phase relations on normalized
  representatives. It also exports raw matrix/circuit naturality and normalized
  unitary evolution.
- Stage 2 exports ExactOperatorEq, ExactCircuitEq, BasisMeasurementEq,
  PureInputBasisMeasurementEq, and their exact-to-observational arrows.
- The plan fixes the intended orientations: V = ζ • U for one complex global
  phase, V y x = U y x * φ x for input-column phase, and
  V y x = θ y * U y x for output-row phase.
- Complex multiplication is commutative, but input-right and output-left
  formulas must remain visibly distinct so Stage 3C can preserve quaternionic
  order.
- Real unit phase is exactly ±1. Complex unit phase uses
  Complex.normSq ζ = 1; mathlib provides normSq multiplication/inversion and
  matrix scalar/mulVec compatibility.
- No public operator-phase, basis-phase, or projective-action relation exists.
  Stage 3B creates new semantic infrastructure; no frozen Goal 1 family is
  reclassified merely because a relation name is added.
- Projective action can quantify over normalized inputs while returning the raw
  output-column phase relation. This needs finite input indices but no output
  normalization or unitarity premise.
- Stage 3A closed with 133 manifest declarations and 217 root audit endpoints;
  both counts must grow exactly by the stable Stage 3B public surface.

## Updated Assumptions

- Real and complex global operator phase, input-basis phase, output-basis phase,
  and projective action are genuine symmetric equivalence relations on each
  fixed matrix type.
- Rectangular matrices are supported wherever a relation does not require a
  circuit or square unitary.
- One global phase implies constant input-column phase, constant output-row
  phase, and projective action. Input phase implies `BasisMeasurementEq` only;
  output phase and projective action each imply
  `PureInputBasisMeasurementEq`. No converse is claimed in this milestone.
- Projective action compares raw output rays for every normalized input. It does
  not claim an arbitrary matrix preserves normalization.
- Circuit relations are evaluator wrappers over operator relations. They do not
  compare gate lists or resource data.
- Real/complex examples must witness nontrivial phase equivalence without
  literal equality. Strict hierarchy witnesses remain primarily Stage 8 work.
- Quaternionic operator and basis phase is excluded and remains Stage 3C work.

## Big Picture Objective

Introduce reusable, side-explicit real and complex operator-phase semantics,
prove their equivalence laws and valid observational implications, and lift
them to chronological circuits without conflating one global phase,
input-column phase, output-row phase, projective action, or basis measurement.

## Detailed Implementation Plan

- Add `Semantics/OperatorPhase/ComplexReal.lean`, importing only
  Semantics.StatePhase plus narrow matrix APIs actually required.
- Define rectangular `RealGlobalSignEq` and `ComplexGlobalPhaseEq` with
  orientation `V = phase • U`.
- Define real/complex input-basis phase with a unit phase per input column acting
  on the right.
- Define real/complex output-basis phase with a unit phase per output row acting
  on the left.
- Define real/complex projective action by requiring raw output-column phase
  equivalence for every normalized input representative.
- Prove unfolding lemmas, reflexivity, symmetry, transitivity, packaged
  Equivalence, and exact-to-phase constructors for every genuine relation.
- Prove exact-to-global, global-to-input/output/projective,
  input/output-to-`BasisMeasurementEq`, and output/projective-to-
  `PureInputBasisMeasurementEq` for both scalars.
- Prove global-phase preservation of unitary membership in both directions.
- Add `Semantics/OperatorPhase/ComplexRealCircuit.lean`. Prove global two-pair
  multiplication; input-phase and projective preservation under common later
  evolution; output-phase preservation under common earlier evolution; and
  projective preservation under common earlier evolution only with an actual
  unitary/local-unitary premise. Lift those laws to chronological circuits and
  add exact-circuit global phase constructors.
- Add `Semantics/OperatorPhase/ComplexRealAudit.lean` as a non-root diagnostic
  with real -1 and complex I operator/circuit examples, scope consumers, and
  axiom spot checks.
- Add every stable public declaration to the semantic manifest with a real
  named audit consumer and seven axes. Exclude diagnostic declarations.

## Build Structure

- `Semantics/OperatorPhase/ComplexReal.lean`: stable real/complex operator,
  basis, projective, and circuit phase API.
- `Semantics/OperatorPhase/ComplexRealCircuit.lean`: sided multiplication and
  chronological-circuit wrappers/congruence laws; no diagnostics.
- `Semantics/OperatorPhase/ComplexRealAudit.lean`: examples, scope consumers, and
  axiom diagnostics; excluded from the public root.
- Stage 2 and Stage 3A leaves remain unchanged.
- Public promotion waits for stable and diagnostic leaves. Promotion requires
  root, AxiomAudit, manifest, and downstream smoke checks.
- Focused builds are the `ComplexReal`, `ComplexRealCircuit`, and
  `ComplexRealAudit` module targets.
- Adjacent consumers include Semantics.StatePhase, Semantics.Measurement,
  Circuit.Basic, and the Stage 3C import probe.

## Boundary Checks

- A single global phase is not an input-dependent or output-dependent family,
  even though it implies both via constant functions.
- Input phase multiplies each column on the right; output phase multiplies each
  row on the left. Commutativity must not erase those formulas.
- Basis phase proves basis-measurement agreement, not all-pure projective
  action, channel equality, or all-effect equality.
- Projective action quantifies over normalized pure inputs but returns a raw ray
  relation; normalized output requires a separate unitary premise.
- Circuit wrappers use OrderedCircuit.eval and do not compare gate lists,
  schedules, resources, or embeddings.
- Real phase is only ±1; complex phase is one norm-one scalar.
- No result accepts arbitrary quaternionic global operator phase or anticipates
  the Stage 3C central-kernel theorem.

## No-Cheating Checks

- No relation is defined by its measurement consequence.
- Unit conditions are carried by phase witnesses and proved stable under
  inverse/composition.
- Exact-to-phase arrows construct identity phases explicitly.
- Basis-measurement consequences are entrywise proofs from the actual
  input-right/output-left equations and scalar weight laws.
- Projective-to-pure-measurement passes through Stage 3A raw phase weights, not
  a channel or density shortcut.
- No two-sided composition closure is inferred. Common-later and common-earlier
  laws are separated, and the projective common-earlier theorem carries the
  exact unitarity premise required to pull an input backward.
- Circuit relations unfold only through evaluator wrappers.
- No impossible normalization premise, false converse, quaternionic
  commutation, heartbeat override, proof hole, project axiom, unsafe/opaque
  shortcut, or metadata-only proof is permitted.

## Completion Requirements

- Eight distinct real/complex operator relations have public signatures and
  checked reflexive, symmetric, transitive, and Equivalence laws.
- Projective-action relations quantify over every normalized pure input and do
  not assert output normalization.
- All planned exact/global/basis/projective/measurement and global-unitarity
  arrows compile for both scalars.
- Real and complex circuit wrappers compile through chronological evaluation
  with exact-circuit lifts and nontrivial phase examples.
- The `-1` and `I` examples prove phase equality and literal inequality at
  operator level. The rational unitary rotation with entries `3/5,4/5,-4/5,3/5`
  supplies nonzero-entry input/output phase and superposition strictness
  diagnostics reusable by Stage 8; scope consumers exercise every stable API.
- New stable declarations appear once in the manifest; diagnostics do not;
  direct audit labels match AxiomAudit.
- Focused, adjacent, root, warning-as-error, audit, manifest/name/consumer,
  hole/shortcut/artifact/whitespace, checksum, and diff checks pass.

## Stage Results

- Milestone active. Stage 3A is closed; real/complex operator-phase probes and
  implementation remain in progress.
