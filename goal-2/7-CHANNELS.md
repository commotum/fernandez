# 7-CHANNELS

## Current Facts

- At Stage 7 entry, Stages 1--6 were independently closed and the tree had 76 Lean sources
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

- `QuaternionicComputing/Semantics/Channel.lean` now supplies the Stage 7A
  core with 41 explicitly named declarations plus one anonymous matrix
  coercion instance. `UnitaryOperator` bundles a finite `RCLike` square matrix
  with its actual unitary certificate; real and complex aliases, exact
  extensionality, identity, and chronological `followedBy` composition are
  exposed without an ambiguous multiplication instance.
- `UnitaryOperator.evolve` delegates to the Stage 6 physical conjugation.
  Identity and composition are exact: `U.followedBy V` stores `V * U` and
  evolves first by `U`, then by `V`.
- `ChannelEq` quantifies over every density input and compares the complete
  evolved density. `AllMeasurementEq` quantifies over every density input and
  every genuine `Effect`. Both are equivalence relations, respect exact
  underlying matrices and chronological composition, and
  `channelEq_iff_allMeasurementEq` proves their equivalence by invoking the
  Stage 6 physical-effect separation theorem for each output pair.
- The core imports only `EffectSeparation`; it has no phase, circuit,
  quaternionic channel, arbitrary trace-test, or hidden nonempty API. Strict
  warning-as-error compilation and the focused build pass at `2672/2672`; its
  representative axiom union is exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `QuaternionicComputing/Semantics/ChannelPhase.lean` now supplies 40 stable
  declarations and nine private proof helpers. Equal normalized ket--bra
  matrices determine one real sign or complex right phase. Explicit raw
  real/complex projective-action relations have complete equivalence laws,
  exact/global lifts, and exact iff bridges to the normalized relations through
  a checked zero/nonzero square-root normalization argument.
- On `[Nonempty I]`, a ray-fixing matrix is proved scalar by its basis columns
  and pairwise sums. This gives real and complex raw/normalized projective
  kernel theorems and the exact inhabited-space iff results
  `realGlobalSignEq_iff_channelEq`,
  `complexGlobalPhaseEq_iff_channelEq`, and their normalized/raw projective
  analogues. The proof uses `V * Uᴴ`, one supplied unitary certificate, and no
  determinant or dimension-at-least-two premise. Forward global-phase-to-
  channel and channel-to-projective arrows require no inhabited hypothesis.
  Named empty-index theorems separately record that empty square matrices are
  exactly equal, rather than advertising vacuous density quantification as a
  physical experiment.
- The phase leaf passes strict compilation and its `2682/2682` focused build.
  Fourteen representative/main endpoints use exactly `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden-token and import-boundary
  scans pass.
- `QuaternionicComputing/Semantics/ChannelCircuit.lean` now supplies 58
  explicitly named stable declarations plus one anonymous circuit coercion.
  `UnitaryCircuit` bundles only a chronological circuit and its local-unitary
  certificate, derives its `UnitaryOperator`, and has exact extensionality,
  identity, append, associativity, and evaluator laws. `C.append D` maps to
  `C.toOperator.followedBy D.toOperator`, so the matrix remains
  `eval D * eval C`.
- `CircuitChannelEq` and `CircuitAllMeasurementEq` are honest equivalence
  relations on certified circuits. Their iff, exact-evaluator implications,
  all-measurement conversions, both-pair append congruence, and common
  earlier/later congruences compile. Real/complex global phase and normalized
  projective action are each equivalent to circuit channel equality. The
  evaluator basis `BitBasis W` is inhabited canonically even at zero wires, so
  the public circuit theorems do not ask callers for redundant nonempty data.
- The circuit leaf passes strict compilation, its `2685/2685` focused build,
  the combined three-leaf build, representative exact-three-axiom checks,
  import/forbidden scans, diff checks, and an independent API review.
- The non-root `QuaternionicComputing/Semantics/ChannelAudit.lean` consumes
  every stable export exactly once through 23 aggregate consumers. Its checked
  allocation is `41 + 40 + 58 = 139/139`, excluding only generated structure
  projections and the two anonymous coercion instances. The audit imports only
  `ChannelCircuit` and passes strict compile, its automated exact-coverage
  validator, and the `2686/2686` focused build.
- Concrete diagnostics prove that global real `-1` and complex `I` preserve
  both complete channels and all-effect outcomes; identity and Boolean swap
  are instead separated by a real basis density and genuine basis effect.
  Other checks instantiate the raw/normalized/phase iff theorems, operator and
  circuit chronology, empty-index matrix equality versus vacuous channel
  quantification, and inhabited zero-wire real/complex circuits. All eleven
  local audit endpoints use exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- Public-root/axiom integration compiles at `2760/2760` with 39 representative
  Stage 7 root endpoints. The combined channel-audit/public-root/axiom build
  passes at `2761/2761`; the cached default build passes at `2759/2759`, and
  the adjacent Stage 6/7 diagnostic build passes at `2763/2763`. All six
  Stage 7/public integration sources also compile directly with warnings as
  errors.
- `docs/Goal2SemanticAPIManifest.json` appends the stable declarations in exact
  source order `41 + 40 + 58`, bringing the manifest to 941 unique entries,
  104 resolving consumers, and 207 direct root-audit labels. Both generated
  strict manifest consumers compile, the first-802 structural hash remains
  `6554f0c773ef602e3e8791c77142a37dda2c0fc97df5d8b1b41f8a162eadf2e0`,
  and the frozen Goal 1 cohort checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- README and the architecture, conventions, mathlib-API, axiom-audit, release,
  classification, traceability, and corrections documents now publish the
  checked Stage 7 boundary. The Goal 3 forecast is rebaselined to the current
  80-source, 941-manifest, 104-consumer, 207-direct-audit, and 393-root-audit
  checkpoint without treating Goal 2 as released.
- The root-only downstream smoke compiles the channel/all-effect iff,
  inhabited complex phase/channel iff, circuit phase/channel iff, empty-index
  boundary, and chronology. Proof-hole, declaration-shortcut, forbidden
  Stage 7 scope, import-boundary, generated-artifact, Markdown, whitespace,
  and diff scans pass. The 393 root audit commands report exactly the union
  `propext`, `Classical.choice`, and `Quot.sound`; all eleven local Stage 7
  commands report the same exact set.
- The independent integrated closure review passed requirement by requirement
  on 2026-07-11. It reran the focused `2686`, adjacent `2763`, and default
  `2759` builds; strict-compilation, manifest-generation, downstream-smoke,
  axiom-union, frozen-checksum, boundary, documentation, artifact, whitespace,
  and diff checks all passed. No semantic, proof, scope, or no-cheating defect
  was found. Stage 7 is complete.
