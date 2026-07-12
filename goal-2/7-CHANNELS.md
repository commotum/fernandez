# 7-CHANNELS

## Current Facts

- Stages 1--6 are independently closed. The current tree has 76 Lean sources
  including the public root, 802 exact Goal 2 semantic-manifest entries, 81
  resolving consumers, 168 direct manifest/root-audit labels, and 354 root
  axiom commands. The exact axiom union remains `propext`,
  `Classical.choice`, and `Quot.sound`.
- `DensityMatrix 𝕜 I` stores positive semidefiniteness and trace one;
  `Effect 𝕜 I` stores the genuine Loewner bounds `0 ≤ E ≤ 1`.
  `DensityMatrix.unitaryConjugate` gives the physical output of a supplied
  unitary, and `DensityMatrix.eq_iff_forall_effect_bornValue_eq` proves that
  every genuine effect separates arbitrary real/complex-style densities.
- `RealGlobalSignEq`, `ComplexGlobalPhaseEq`, `RealProjectiveActionEq`, and
  `ComplexProjectiveActionEq` already compare raw matrices at their exact
  stated scopes. Global phase implies normalized projective action, but the
  real/complex converse has not yet been formalized.
- Existing projective-action predicates quantify over normalized pure states.
  The quaternionic layer already demonstrates the correct normalization route
  from normalized to raw columns, but its noncommutative rank-one/dimension
  exception must not be imported into the commutative real/complex result.
- `OrderedCircuit.IsLocallyUnitary` proves that an evaluated chronological
  circuit is unitary. Existing exact and global-phase circuit relations compare
  `OrderedCircuit.eval`; no circuit channel wrapper exists yet.
- A density matrix cannot inhabit an empty index type. Consequently a
  density-input channel predicate would be vacuous there even though the empty
  square matrix type is subsingleton. Physical global-phase characterizations
  will state `Nonempty I` explicitly; any empty-index theorem must be named as
  a boundary result rather than presented as experimental evidence.

## Updated Assumptions

- Bundle a square matrix with its unitary certificate as a reusable
  `UnitaryOperator`; this makes `ChannelEq U V` a relation between physical
  operators and keeps proof arguments out of the relation's visible
  signature. Expose explicit real and complex aliases.
- Define `U.evolve ρ` by Stage 6 `unitaryConjugate`. Define `ChannelEq` as
  equality of those bundled density outputs for every density input, and
  `AllMeasurementEq` as equality of `bornValue` for every density input and
  every genuine `Effect`.
- Prove `ChannelEq ↔ AllMeasurementEq` uniformly over `RCLike`; the reverse
  direction must invoke Stage 6 physical-effect separation on each output.
- Add raw real/complex projective-action support only if it has real consumers:
  normalized projective action should extend to every raw column by an
  explicit zero/nonzero normalization proof, then feed the phase-kernel proof.
- For a nonempty finite space, reduce two projectively equal unitaries to the
  ray-fixing matrix `V * Uᴴ`. Computational-basis columns and their pairwise
  sums force one common scalar; its supplied ray witness proves unit norm. This
  should establish the real sign and complex phase converses without a
  dimension-at-least-two assumption and without determinant arguments.
- Keep public circuit wrappers evaluator-backed and proof-bearing. A circuit
  relation must retain local-unitarity certificates and must not compare gate
  lists, schedules, resources, or cross-model encodings.

## Big Picture Objective

Build the reusable same-space unitary-channel layer promised by the semantic
classification: physical equality on every mixed input, equivalent equality
of every genuine physical-effect outcome, exact real/complex global-phase and
projective kernels under explicit inhabited-space assumptions, and narrow
chronological-circuit wrappers.

## Detailed Implementation Plan

### 7A-CHANNEL-CORE

- Add `Semantics/Channel.lean` importing only Stage 6 separation. Define
  `UnitaryOperator 𝕜 I`, real/complex aliases, coercion/extensionality,
  identity and chronological multiplication, density evolution, and its
  identity/composition laws.
- Define `ChannelEq` and `AllMeasurementEq`; prove reflexivity, symmetry,
  transitivity, equivalence laws, exact/operator extensionality consequences,
  composition congruence, direct `ChannelEq → AllMeasurementEq`, and the
  converse through genuine physical-effect separation.
- Keep arbitrary trace-test matrices out of both definitions and exported
  theorem statements.

### 7B-PHASE-KERNEL

- Add `Semantics/ChannelPhase.lean` importing the channel core and existing
  real/complex operator phase leaf. Prove the pure-density equality to real
  sign/complex phase bridge and channel equality to normalized projective
  action.
- If needed, define explicitly named raw real/complex projective-action
  predicates, prove raw/normalized equivalence by genuine normalization, and
  use them to show that a nonempty finite ray-fixing linear unitary is one
  scalar multiple of identity.
- Prove both directions of
  `RealGlobalSignEq ↔ ChannelEq` and
  `ComplexGlobalPhaseEq ↔ ChannelEq`, and the corresponding
  `RealProjectiveActionEq ↔ ChannelEq` and
  `ComplexProjectiveActionEq ↔ ChannelEq`, with exact nonempty and unitary
  data visible in signatures.
- Add an explicitly named empty-index boundary theorem if the generic matrix
  equality is useful, while keeping the physical characterization theorem
  inhabited.

### 7C-CIRCUITS-AND-AUDIT

- Add `Semantics/ChannelCircuit.lean` with constructors from locally unitary
  evaluated circuits and evaluator-backed `CircuitChannelEq` and
  `CircuitAllMeasurementEq`. Prove their iff, equivalence laws, exact-circuit
  implication, real/complex global-phase implications and converses, and
  append congruence through channel composition.
- Add non-root `Semantics/ChannelAudit.lean` with exact aggregate consumers for
  every stable export, nontrivial real/complex Boolean examples, empty-index
  boundary checks, channel/all-effect agreement, phase characterization, and
  local axiom prints.
- Promote only stable channel/core/phase/circuit leaves, append every stable
  declaration to the separate Goal 2 semantic manifest, extend the root axiom
  audit, and fold exact evidence into all affected documentation.

## Build Structure

- `Semantics/Channel.lean`: low-dependency physical unitary operator and
  channel/all-effect equality core. It imports `EffectSeparation`, not phase,
  circuits, diagnostics, or the public root.
- `Semantics/ChannelPhase.lean`: real/complex pure/projective/global-phase
  characterization proof leaf. It imports `Channel` and the narrow
  `OperatorPhase/ComplexReal` leaf; it contains no circuit wrapper.
- `Semantics/ChannelCircuit.lean`: evaluator-backed chronological-circuit
  wrappers. It imports `ChannelPhase` and the existing circuit phase leaf.
- `Semantics/ChannelAudit.lean`: non-root complete consumers, concrete
  examples, boundary diagnostics, and axiom prints. It is never imported by a
  stable leaf or the public root.
- Focused builds target every new leaf. Adjacent consumers include the Stage 6
  density audit, real/complex phase audit, circuit core, public root, generated
  manifest checks, and explicit axiom audit.

## Boundary Checks

- `ChannelEq` compares equality of complete evolved density matrices for every
  density input. `AllMeasurementEq` quantifies over every density input and
  every genuine `Effect`; neither may be defined by basis effects or arbitrary
  trace tests.
- Global phase is one scalar shared by the entire operator. Input-column or
  output-row phase is not silently upgraded. Projective action concerns every
  normalized pure input; the theorem connecting it to channels retains
  unitarity and inhabited-space assumptions.
- The channel core is real/complex-style through `RCLike`; no quaternionic
  density, effect, channel, or arbitrary unit-quaternion phase is introduced.
- Circuit wrappers compare evaluated physical maps, not syntax, resource
  counts, schedules, cross-model embeddings, added wires, or decoded
  marginals.
- Empty-index channel quantification is physically vacuous. It cannot justify
  a nonvacuous phase-kernel statement without a separate matrix-subsingleton
  boundary proof.

## No-Cheating Checks

- Do not store channel equality or measurement equality as a field, postulate
  phase witnesses, or derive the converse from an arbitrary-matrix trace-test
  quantifier mislabeled as effects.
- Do not use impossible density inputs, contradictory unitarity hypotheses,
  basis-only outcomes, determinant roots, or a registry label as the phase
  characterization proof.
- Do not infer a quaternionic channel theorem from the commutative `RCLike`
  implementation or reuse the quaternionic arbitrary-unit-phase rank-one
  exception as a complex/real operator result.
- No `sorry`, `admit`, `sorryAx`, new axiom, opaque/unsafe shortcut, heartbeat
  override, public diagnostic import, silent frozen-cohort edit, or theorem
  engineered from a false premise.

## Completion Requirements

- Bundled physical unitary operators and their density evolution compile with
  exact identity and chronological composition laws.
- `ChannelEq U V ↔ AllMeasurementEq U V` compiles over the supported
  real/complex-style core, and the all-measurement definition visibly ranges
  over genuine `Effect` values.
- On explicit nonempty finite real and complex spaces, global sign/phase,
  normalized projective action, and channel equality are connected in both
  directions with the exact unitary hypotheses and phase orientation.
- Evaluator-backed circuit channel/all-measurement wrappers compile, preserve
  exact and global-phase implications, and expose chronological append
  congruence without syntax/resource claims.
- A non-root audit consumes every stable declaration. Public-root,
  manifest exact-set/seven-axis/name/consumer/direct-audit checks,
  focused/adjacent/root/default builds, warning-as-error checks, exact axiom
  union, frozen checksum, forbidden-token, import-boundary, artifact,
  whitespace, downstream-smoke, and diff checks pass.
- Documentation publishes only checked channel arrows, makes the inhabited
  boundary explicit, and continues to exclude quaternionic channels, partial
  trace, Kraus maps, instruments, mixed-top simulation, and cross-model
  channel equality.

## Stage Results

- In progress.
