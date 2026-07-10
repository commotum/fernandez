# 3C-QUATERNION

## Current Facts

- Stage 3A fixes quaternionic state/ray representatives to unit phase on the
  right and proves raw matrix/circuit naturality plus normalized unitary
  evolution. Left phase is rejected by a normalized counterexample.
- Stage 3B exports distinct real/complex global, input-column, output-row, and
  normalized-projective operator relations, together with evaluator-backed
  circuit wrappers and chronology-correct composition laws.
- The completed milestone tree has 57 Lean sources, 264 root axiom endpoints,
  and a 384-item Goal 2 semantic API manifest. Stage 3C contributes exactly
  101 declarations (44 core, 43 circuit, and 14 kernel declarations), mapped
  to 11 diagnostic consumers and 13 direct root-audit targets. The frozen
  936-declaration Goal 1 cohort checksum remains unchanged.
- Quaternionic input-column phase must multiply each matrix entry on the right;
  output-row phase must multiply on the left. These formulas are no longer
  interchangeable by commutativity.
- Arbitrary unit-quaternion left multiplication is not a valid generic global
  operator phase. The intended dimension-at-least-two projective kernel is the
  central real sign family `±I`.
- A strict 482-line probe at `/tmp/Stage3CGeneralProbe.lean` compiles with
  warnings as errors and no holes. It proves that normalized projective action
  is equivalent to all-raw-column projective action for arbitrary finite
  rectangular quaternionic matrices, without unitarity or nonempty premises.
- The same probe proves the square-unitary kernel with the explicit hypothesis
  `1 < Fintype.card I`. Only the first matrix is assumed unitary. It also proves
  that every unit quaternion gives a projectively trivial rank-one scalar
  operator, while the `j` example is not a central sign.
- The probe is temporary evidence, not a public implementation. It omits the
  complete packaged equivalence surface, exact lifts, central-sign unitarity,
  circuit wrappers, public consumers, manifest entries, and release audits
  required to close this milestone.

## Updated Assumptions

- Use five operator relations: central real sign, input-right phase,
  output-left phase, raw all-column projective action, and normalized
  all-pure-input projective action.
- Keep central sign visibly real: `V = s • U` with `s : ℝ` and `s*s=1`.
  Do not encode it as existence of an arbitrary unit quaternion followed by a
  separate centrality proposition.
- Raw and normalized projective action are equivalent for every finite input
  type, including the empty type. For the empty type the normalized relation is
  vacuous, while the raw relation checks only the unique zero column and holds
  trivially; this bridge does not manufacture a normalized state.
- The kernel converse needs a square matrix, `DecidableEq I`, explicit
  `1 < Fintype.card I`, and unitarity of `U`. It does not need a separately
  assumed unitarity proof for `V`.
- Rank one is a genuine exception: the projective kernel contains the full
  unit-quaternion scalar family, not only the central real signs.
- Input-right phase implies all-basis-input measurement equality. Output-left
  phase and normalized projective action imply all-normalized-pure-input basis
  measurement equality. None implies channel equality at this stage.
- Raw projective action is preserved by arbitrary common earlier and later
  compatible matrices. Normalized projective action is preserved by arbitrary
  common later matrices, but a common earlier matrix must be unitary.

## Big Picture Objective

Introduce side-correct quaternionic operator and circuit phase semantics,
prove the exact dimension-sensitive projective kernel, and expose the rank-one
exception without ever treating arbitrary unit-quaternion multiplication as a
generic global operator phase.

## Detailed Implementation Plan

- Add `Semantics/OperatorPhase/Quaternion.lean` with transparent rectangular
  definitions:
  - `QuaternionCentralSignEq`;
  - `QuaternionInputRightPhaseEq`;
  - `QuaternionOutputLeftPhaseEq`;
  - `QuaternionRawProjectiveActionEq`;
  - `QuaternionProjectiveActionEq`.
- Prove reflexivity, symmetry, transitivity, and packaged `Equivalence` for all
  five relations. Add exact-operator constructors for each.
- Prove the normalized/raw projective bridge in both directions and as an iff.
  Normalize a nonzero raw column by the inverse square root of its total
  weight; handle the zero column separately and cancel only the nonzero central
  real scaling factor.
- Prove central-sign implications to input-right phase, output-left phase, raw
  projective action, and normalized projective action. Prove central-sign
  preservation and reflection of quaternionic unitarity.
- Prove input-right phase to `BasisMeasurementEq`; output-left phase to
  `BasisMeasurementEq`, explicit `mulVec` row factorization, and
  `PureInputBasisMeasurementEq`; normalized projective action to
  `PureInputBasisMeasurementEq`.
- Add `Semantics/OperatorPhase/QuaternionCircuit.lean` with matrix composition
  laws and four evaluator-backed circuit relations (central, input, output,
  normalized projective). Provide `iff_eval`/`eval` projections, equivalence
  laws, exact-circuit central lift, and the justified chronological
  congruences. Do not create a raw-projective circuit wrapper without a real
  downstream need.
- Add `Semantics/OperatorPhase/QuaternionKernel.lean` as a heavy public proof
  leaf. Keep normalization and ray-fixing helpers private where practical.
  Prove:
  - raw projective action iff central sign for `1 < card I` and unitary `U`;
  - normalized projective action iff central sign under the same hypotheses;
  - the rank-one arbitrary-unit-quaternion projective family;
  - a unitary `j` rank-one witness that is not central-sign equivalent.
- The kernel proof may form `A = V * star U`, use basis columns to diagonalize
  `A`, use `e_i + e_j` to identify diagonal phases, use
  `e_i*i + e_j` and `e_i*j + e_j` to force commutation with `i` and `j`, then
  prove the common quaternion is real and has square one. The cardinal
  hypothesis must remain explicit in the exported signature.
- Add `Semantics/OperatorPhase/QuaternionAudit.lean` as a non-root diagnostic
  with complete named consumers, a Bool-indexed dimension-two kernel consumer,
  right-input/left-output order tests, central `-1` examples, the rank-one `j`
  exception, and representative axiom prints.
- Promote only the three stable leaves through the public root. Add every
  stable declaration exactly once to the Goal 2 semantic manifest; exclude all
  diagnostic declarations and preserve the frozen Goal 1 checksum.
- Fold exact definitions, dimension hypotheses, rank-one behavior, and denied
  channel/global-phase upgrades into conventions, architecture, equivalence
  classification, traceability overlay, release report, axiom audit, and the
  Goal 3 prerequisite. Add no correction number unless implementation reveals
  a new source error beyond C-006.

## Build Structure

- `Semantics/OperatorPhase/Quaternion.lean`: low-dependency definitions,
  equivalence laws, exact/measurement arrows, bridge, and central unitarity.
- `Semantics/OperatorPhase/QuaternionCircuit.lean`: sided matrix composition
  and chronological circuit wrappers/congruences.
- `Semantics/OperatorPhase/QuaternionKernel.lean`: dimension-sensitive heavy
  kernel and rank-one theorems; public but isolated from the cheaper leaves.
- `Semantics/OperatorPhase/QuaternionAudit.lean`: diagnostic consumers and
  counterexamples; never imported by `QuaternionicComputing.lean`.
- Focused builds target each new leaf. Adjacent consumers are StatePhase,
  Measurement, Circuit.Basic, the Stage 4 ray probe, and the public root.
- Public promotion requires the diagnostic, manifest, root, audit, strictness,
  checksum, and downstream name/consumer checks to pass first.

## Boundary Checks

- Quaternionic state and input-column phases act on the right; output-row
  phases act on the left.
- `QuaternionCentralSignEq` permits only a real square-one scalar. No arbitrary
  unit quaternion is called global operator phase.
- The dimension-at-least-two kernel and rank-one exception are separate
  theorems with explicit cardinal assumptions.
- Projective action compares complete output rays for all normalized pure
  inputs. It is not basis-only equality, channel equality, or all-effect
  equality, and it does not assert output normalization.
- The rectangular operator relation may be vacuous on an empty input index;
  the circuit wrapper uses inhabited `BitBasis W` and is nonvacuous even at
  zero wires.
- The normalized/raw bridge is an iff of universal action predicates, not an
  assertion that every raw column is normalized.
- Circuit predicates compare only `OrderedCircuit.eval`; they do not compare
  gate lists, schedules, resources, embeddings, or compilers.
- No commutative scalar rearrangement may appear in quaternionic input/output
  or projective proofs. Real scalar centrality must be invoked explicitly.

## No-Cheating Checks

- Do not define central sign by the desired kernel theorem or projective action
  by a measurement consequence.
- Do not hide `1 < Fintype.card I` in `Nontrivial I` or an inferred instance.
- Do not assume `V` unitary when the proof derives the conclusion without it.
- Do not prove only the forward central-sign implication and describe it as a
  kernel characterization.
- Do not ignore the zero-column branch in the normalized/raw bridge or cancel
  a scalar without a nonzero proof.
- Do not use rank-one behavior as evidence for dimensions at least two, or the
  dimension-two theorem as evidence against the rank-one exception.
- Do not infer arbitrary two-sided circuit congruence. Inspect chronological
  multiplication order in every wrapper theorem.
- No `sorry`, `admit`, `sorryAx`, project axiom, impossible premise,
  unsafe/opaque shortcut, heartbeat override, or metadata-only proof.

## Completion Requirements

- All five operator relations have public signatures, transparent meanings,
  complete equivalence laws, and exact lifts.
- The side-correct basis-phase and measurement implications compile over
  rectangular matrices with only the required finiteness assumptions.
- Normalized and raw projective action are proved equivalent without unitarity
  or nonempty assumptions, with the empty-input vacuity documented.
- Both raw and normalized projective kernels are characterized as central real
  signs for finite square dimension at least two and unitary `U`.
- The rank-one arbitrary-unit-quaternion family and explicit unitary `j`
  noncentral witness compile.
- Quaternionic circuit wrappers and every justified sided chronological
  congruence compile; no invalid reverse-side or two-sided law is exported.
- A non-root audit exercises every stable declaration and supplies concrete
  side/order, dimension-two, and rank-one consumers.
- The semantic manifest exact set, seven axes, consumer resolution, direct
  audit labels, public-root names, and frozen checksum all pass.
- Focused, adjacent, public-root, full, warning-as-error, axiom, strictness,
  forbidden-token, diagnostic-boundary, artifact, whitespace, and diff checks
  pass under `BUILD-PLAN.md`.
- Documentation states the kernel theorem and exception precisely and makes no
  channel, all-effect, or arbitrary-quaternion global-phase claim.

## Stage Results

- `Semantics/OperatorPhase/Quaternion.lean` exports five transparent
  same-space relations with complete equivalence laws and exact lifts:
  `QuaternionCentralSignEq`, `QuaternionInputRightPhaseEq`,
  `QuaternionOutputLeftPhaseEq`, `QuaternionRawProjectiveActionEq`, and
  `QuaternionProjectiveActionEq`. It also exports the raw/normalized iff,
  central-sign implications and unitarity reflection, and the justified
  basis/all-pure-input measurement consequences.
- The normalized-to-raw bridge handles zero separately and normalizes every
  nonzero column by a nonzero central real inverse square root. It needs only
  finite input, not unitarity or nonemptiness. Thus both sides hold for an
  empty input type for different checked reasons: normalized quantification is
  vacuous and raw quantification sees only the zero column.
- `Semantics/OperatorPhase/QuaternionCircuit.lean` exports the seven
  side-correct matrix composition laws and exactly four evaluator-backed
  circuit relations, with projections, equivalence laws, the exact-circuit
  central lift, and chronology-correct congruences. There is no raw-projective
  circuit wrapper and no unjustified reverse-side or two-sided law.
- `Semantics/OperatorPhase/QuaternionKernel.lean` proves both raw and
  normalized projective action iff central real sign for finite square
  matrices with explicit `1 < Fintype.card I`, `[DecidableEq I]`, and only
  `U` assumed unitary. The proof derives the shared diagonal phase, forces it
  to commute with `i` and `j`, and then proves it is a real square-one scalar.
- Rank one is characterized completely: `quaternionRankOneScalar q` is
  unitary, raw-projectively trivial, and normalized-projectively trivial iff
  `Quaternion.normSq q = 1`. Projective triviality is therefore equivalent to
  unitarity in rank one. `quaternionRankOneJ_exception` packages a unitary,
  projectively trivial `j` scalar that is not central-sign equivalent.
- `Semantics/OperatorPhase/QuaternionAudit.lean` remains outside the public
  root. Its 11 aggregate consumers exercise all 101 stable declarations; its
  Bool kernel specialization, right-input/left-output order checks, central
  `-1` strictness example, and rank-one family compile. Eight local axiom
  prints use only `propext`, `Classical.choice`, and `Quot.sound`.
- The public root imports the three stable leaves, not the diagnostic leaf.
  `QuaternionicComputing/AxiomAudit.lean` adds 13 representative endpoints,
  for 264 total root prints, all using only the same three standard axioms.
- `docs/Goal2SemanticAPIManifest.json` now contains exactly 384 source-matched
  declarations with all seven axes, 46 resolving consumers, and 78 direct
  audit targets. Generated Lean checks resolve every public name and every
  consumer. The first 283 entries are structurally unchanged and the frozen
  Goal 1 checksum remains
  `65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b`.
- Focused builds passed for the kernel (2,354 jobs) and diagnostic leaf (2,356
  jobs); the public root passed at 2,562 jobs and the combined explicit target
  build at 2,564 jobs. Warning-as-error checks passed for all three public
  leaves, the diagnostic leaf, public root, generated manifest checks, and
  root audit. The initially reported flexible-simp linter warning in the
  kernel was removed by introducing typed intermediate equalities.
- Forbidden-hole/axiom/unsafe/opaque/heartbeat scans, diagnostic-boundary,
  whitespace, artifact, checksum, and `git diff --check` checks pass. The
  documentation and Goal 3 prerequisite now state the dimension-sensitive
  kernel and rank-one exception without claiming quaternionic channels,
  all-effect equality, or arbitrary-quaternion global operator phase. No new
  correction number was required beyond clarifying the consequences of C-006.
