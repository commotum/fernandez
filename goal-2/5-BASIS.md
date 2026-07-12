# 5-BASIS

## Current Facts

- Stages 1--4 are independently complete, and Stage 5 is integrated. The tree
  has 72 Lean sources, 705 exact Goal 2 manifest entries, 73 resolving
  diagnostic consumers, 144 direct manifest/root-audit targets, and 330
  public-root axiom commands using exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `Semantics.Measurement` already distinguishes one-input
  `OutputWeightEqAt`, all-basis-input `BasisMeasurementEq`, and
  all-normalized-pure-input `PureInputBasisMeasurementEq`. Stage 3 exports
  real/complex input- and output-basis phase and quaternionic input-right and
  output-left phase. None of these relations records a classical permutation.
- `Circuit.BasisPreparation` defines `basisColumn`, `xorBasisEquiv`, the
  scalar-generic permutation matrix `basisPreparationMatrix`, its unitarity,
  and the exact ground-column preparation theorem. This is a genuine consumer
  for certified basis action, but only its current theorem about one known
  prepared input is in the frozen cohort.
- The source-level comparison `EQC-044-BASIS-CLASSICAL-BEHAVIOR` is now
  implemented only on explicitly certified permutation operators and circuits.
  The informal biconditional “`U|x>` is phased `|y>` iff `V|x>` is phased
  `|y>`” remains diagnostic-only: it can be true for two unrelated
  nonmonomial unitaries because neither side ever maps a basis column to a
  basis column.
- `BitBasis W` is inhabited even when `W` is empty. General finite index types
  may be empty, so permutation uniqueness and effectful examples must not rely
  on an impossible normalized state or a hidden nonempty premise.

## Updated Assumptions

- Certified classical behavior must contain an explicit `Equiv.Perm I` and a
  proof that each input column has exactly one nonzero unit-phase entry at its
  permuted output. A relation on raw transition predicates is diagnostic only.
- Use one scalar-parametric implementation structure with an explicit
  unit-phase predicate, then give real, complex, and quaternionic aliases and
  theorems. Quaternionic input phases remain on the right and output phases on
  the left.
- Define `SameBasisBehavior` only from two implementation certificates (or
  bundles containing them), as equality of their certified permutations. It
  must be impossible to apply this relation to two arbitrary matrices without
  first providing certificates.
- Prove permutation uniqueness from the nonzero consequence of unit phase.
  Do not bake uniqueness into the definition or infer it from registry labels.
- Basis-classical unitary operators and circuits should bundle unitarity and
  implementation evidence. Existing preparation matrices/gates should obtain
  certificates through their actual permutation-matrix formulas.
- On the certified class, establish the strongest exact equivalences justified
  by the scalar: same permutation, the corresponding input phase, the
  corresponding output phase, and basis-measurement equality. Outside that
  class publish only valid one-way implications and explicit counterexamples.

## Big Picture Objective

Define a nonvacuous, reusable notion of classical reversible computational-
basis behavior, connect it precisely to the existing phase and measurement
relations under certified hypotheses, and prove that the tempting unrestricted
transition biconditional is too weak.

## Detailed Implementation Plan

- Add a narrow `Semantics/BasisBehavior.lean` core with a generic basis ket,
  unit-phase-aware `BasisPermutationImplementation`, raw
  `BasisTransition`/`BasisTransitionRelationEq` diagnostics, permutation
  uniqueness, certified operator bundles, and `SameBasisBehavior`.
- Add scalar-specialized real, complex, and quaternionic constructors and
  theorems. Prove exact equality and the existing global/input/output phase
  relations preserve the certified permutation when both operands carry
  implementation certificates.
- Prove conversely that equal certified permutations produce the correct
  input- and output-phase witnesses in all three scalar systems, with the
  quaternion multiplication order explicit. Derive the restricted
  equivalences with `BasisMeasurementEq` using actual scalar weights.
- Add `Semantics/BasisBehaviorCircuit.lean` with evaluator-backed certified
  circuit bundles and wrappers. Certify `basisPreparationMatrix`, its singleton
  circuit, and the XOR permutation as real consumers; retain the distinction
  between one known preparation input and all-input classical behavior.
- Add a non-root `Semantics/BasisBehaviorAudit.lean`. Its aggregate consumers
  must exercise every stable export. Use two exact rational real `Bool`
  rotations with all entries nonzero to prove both raw transition relations are
  empty and hence equal, while their basis weights differ. Include identity,
  permutation, zero-wire, real/complex/quaternionic, and circuit examples.
- Promote only stable core/circuit leaves through `QuaternionicComputing.lean`,
  add representative root axiom endpoints, append every new stable declaration
  exactly once to the Goal 2 manifest, and fold the checked hierarchy and
  strictness boundary into equivalence, architecture, conventions,
  traceability, release, axiom, and Goal 3 documentation.

## Build Structure

- `Semantics/BasisBehavior.lean`: low-dependency public definitions,
  uniqueness, scalar specializations, and certified operator theorems. It may
  import the existing operator-phase leaf and matrix permutation API, but not
  circuits, diagnostics, or the public root.
- `Semantics/BasisBehaviorCircuit.lean`: public evaluator-backed circuit
  bundles and the existing basis-preparation consumer. It imports the core and
  `Circuit.BasisPreparation`.
- `Semantics/BasisBehaviorAudit.lean`: non-root aggregate consumers and
  rational nonmonomial counterexamples. It is never imported by the public
  root.
- Focused builds target each new leaf. Adjacent builds include
  `Circuit.BasisPreparation`, `Semantics.OperatorPhase.ComplexRealCircuit`,
  `Semantics.OperatorPhase.QuaternionCircuit`, the public root, and explicit
  AxiomAudit.

## Boundary Checks

- `SameBasisBehavior` forgets amplitudes after a certified classical basis
  permutation; it is not exact operator equality, projective action, channel
  equality, or a relation on generic matrices.
- A raw basis-transition biconditional records only which columns are phased
  basis kets. Equality of two empty transition relations is vacuous and must
  never be upgraded to certified behavior.
- `BasisMeasurementEq` compares entry weights. Its equivalence with certified
  permutation equality is restricted to implementation certificates with unit
  phases; it is false as a generic classical-behavior definition.
- Real signs, complex phases, and quaternion phases use different predicates.
  Quaternionic column phases multiply on the right and row phases on the left.
- Circuit behavior is behavior of `OrderedCircuit.eval`, not equality of gate
  lists, resource counts, schedules, or classical uniform generators.
- Basis preparation certifies the all-input XOR permutation, while the existing
  `eval_prepend_basisPreparation_mulVec_ground` theorem remains a one-known-
  input preparation statement.

## No-Cheating Checks

- Do not define `BasisPermutationImplementation` from `SameBasisBehavior`, or
  `SameBasisBehavior` from equality of measurement probabilities.
- Do not accept an arbitrary function in place of a bijection, omit phase
  normalization, or make a nonzero-column premise vacuous.
- Do not call `BasisTransitionRelationEq` classical behavior, and do not use a
  nonunitary or zero matrix as the only vacuity witness.
- Do not commute quaternion factors silently or reuse complex output-phase
  algebra for quaternionic input-right phase.
- No `sorry`, `admit`, `sorryAx`, new axiom, unsafe/opaque shortcut,
  impossible hypothesis, audit import through the public root, heartbeat
  override, or silent frozen-cohort edit.

## Completion Requirements

- The generic implementation certificate, scalar specializations, induced
  permutation uniqueness, unitary operator/circuit bundles, and certified-only
  `SameBasisBehavior` compile with real downstream consumers.
- The certified-class equivalences/implications among same permutation,
  exact/global/input/output phase, and basis measurement compile for every
  advertised real, complex, and quaternionic setting with correct sidedness.
- Two explicit nonmonomial unitary matrices have equal empty raw transition
  relations but unequal basis measurements, proving the unrestricted
  biconditional cannot define classical behavior.
- Existing basis preparation and its singleton circuit certify the XOR
  permutation; zero-wire behavior and permutation uniqueness are checked.
- A non-root audit consumes every stable declaration. Public root, manifest
  exact-set/seven-axis/name/consumer/direct-audit checks, focused/adjacent/root
  builds, strict source checks, exact axiom union, frozen checksum, forbidden-
  token, artifact, whitespace, and diff checks pass.
- `EQC-014` and `EQC-044` receive proof-bearing classifications without
  upgrading known-input preparation to arbitrary-input synthesis or generic
  basis measurement to classical reversible behavior.

## Stage Results

- The mathematical implementation is complete in two stable public leaves:
  `Semantics/BasisBehavior.lean` contributes 90 declarations and
  `Semantics/BasisBehaviorCircuit.lean` contributes 44, for 134 Stage 5
  semantic exports.
- `BasisTransition` and `BasisTransitionRelationEq` are explicitly diagnostic.
  `BasisPermutationImplementation` instead carries an `Equiv.Perm` and an
  all-input phased-one-hot proof. Unit phase implies nonzero phase, so
  `permutation_unique` derives uniqueness rather than storing it as data.
- `SameBasisBehavior` can be formed only from two implementation certificates.
  Exact equality and real/complex global phase or quaternionic central sign
  preserve it. On the certified real, complex, and quaternionic classes it is
  equivalent to the correctly sided input phase, output phase, and
  `BasisMeasurementEq`. Quaternionic input witnesses retain the order
  `star a * b` on the right; output witnesses retain `b * star a` on the left.
- `BasisClassicalUnitaryOperator` and `BasisClassicalCircuit` bundle unitarity
  with the explicit permutation certificate. Circuit behavior is behavior of
  `OrderedCircuit.eval`. The generic empty circuit implements the identity,
  including on the inhabited zero-wire basis.
- The existing `basisPreparationMatrix`, full-support gate denotation, and
  singleton circuit now certify the all-input XOR permutation through the
  actual permutation-matrix formula and unitarity proof. The separate
  `basisPreparationCircuit_mulVec_ground` and historical prepended-circuit
  theorem remain one-known-input statements; no arbitrary-state preparation
  or uniform synthesis claim is made.
- The non-root `Semantics/BasisBehaviorAudit.lean` has 14 exact-allocation
  aggregate consumers covering all 134 exports: ten allocate the 90 core
  declarations as `10/6/6/12/1/6/27/5/8/9`, and four allocate the 44 circuit
  declarations as `12/18/3/11`. It contains 30 explicit diagnostics and 18
  local axiom endpoints.
- The strictness witness uses the exact real unitaries
  `[[3/5,4/5],[-4/5,3/5]]` and
  `[[5/13,12/13],[-12/13,5/13]]`. Every entry is nonzero; neither matrix has
  any `BasisTransition` or certified permutation; their empty raw transition
  relations are equal; but the `false → false` weights are `9/25` and
  `25/169`. Thus the unrestricted transition biconditional cannot define
  classical reversible behavior even on unitaries.
- `EQC-014-BASIS-PREPARATION` is now classified by the all-input certified XOR
  action plus its separately scoped one-ground-input consequence.
  `EQC-044-BASIS-CLASSICAL-BEHAVIOR` is now classified by certified permutation
  equality, with the scalar-sided phase and basis-measurement equivalences only
  on the certified class. Neither row is upgraded to generic global phase,
  projective action, channel equality, or all-effect equality.
- Warning-as-error compilation and focused builds pass for the core, circuit,
  and diagnostic leaves. All 18 local audit endpoints use exactly `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden-token and diff checks are
  clean. The integrated public root builds in 2,573 jobs. The semantic manifest
  contains 705 entries, including all 134 Stage 5 exports; 73 consumers include
  the 14 Stage 5 allocation consumers; 144 direct labels include 25 Stage 5
  labels; and the root axiom audit contains 330 commands with the same exact
  three-axiom union.
- An independent closure review re-read the current sources, manifest,
  generated name/consumer checks, public-root imports, documentation, Goal 2
  and Goal 3 fold-back, scans, and build evidence. It returned **PASS** with no
  mathematical, API-boundary, coverage, or release defect remaining.
