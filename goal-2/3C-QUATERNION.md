# 3C-QUATERNION

## Current Facts

- Stage 3A fixes quaternionic state/ray representatives to unit phase on the
  right and proves raw matrix/circuit naturality plus normalized unitary
  evolution. Left phase is rejected by a normalized counterexample.
- Stage 3B exports distinct real/complex global, input-column, output-row, and
  normalized-projective operator relations, together with evaluator-backed
  circuit wrappers and chronology-correct composition laws.
- The current public tree has 53 Lean sources, 251 root axiom endpoints, and a
  283-item Goal 2 semantic API manifest. The frozen 936-declaration Goal 1
  cohort checksum remains unchanged.
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

- Milestone active. The strict temporary probe establishes a viable proof
  route but no Stage 3C declaration is yet part of the reusable library.
- Next action after the independent Stage 3B closure audit is to implement the
  low-dependency `Quaternion.lean` relation surface and compile its complete
  laws before beginning the kernel proof leaf.
