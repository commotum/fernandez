# 6-DENSITY

## Current Facts

- Stages 1--5 are independently closed. The Stage 5 baseline has 72 Lean
  sources including the public root, 705 exact Goal 2 manifest entries, 73
  resolving consumers, 144 direct manifest/root-audit targets, and 330 root
  axiom commands using exactly `propext`, `Classical.choice`, and `Quot.sound`.
- The library has normalized real and complex pure-state columns and their
  computational-basis weights, but no density matrix, physical effect, Born
  value, or channel API. Existing reduced outer-product calculations are
  paper-specific and must not become an implicit generic mixed-state model.
- Pinned mathlib supplies `Matrix.PosSemidef`, Loewner order under
  `MatrixOrder`, `Matrix.PosSemidef.isHermitian`, conjugation preservation,
  trace cyclicity, positive trace, and finite Euclidean-space linear maps.
  Complex positivity also requires the `ComplexOrder` scope.
- A trace-one positive-semidefinite matrix cannot exist on an empty index type.
  The structures may be stated uniformly, but constructors and later channel
  converses must expose nonempty hypotheses exactly where physical inputs are
  required.
- `Matrix.ext_iff_trace_mul_left/right` separates matrices by arbitrary trace
  tests, but those tests are not physical effects. The Stage 1 probe instead
  constructs every normalized rank-one projector as an effect and identifies
  its trace pairing with the corresponding quadratic form.

## Updated Assumptions

- Use one scalar-generic core over `RCLike 𝕜`, then give explicit
  `RealDensityMatrix`, `ComplexDensityMatrix`, `RealEffect`, and
  `ComplexEffect` aliases. This shares proved mathematics without conflating
  real symmetry with complex Hermiticity.
- Define a density matrix by the actual invariants `PosSemidef` and
  `trace = 1`; Hermiticity is derived and is not stored redundantly.
- Define a physical effect by the genuine Loewner interval `0 ≤ E ∧ E ≤ 1`.
  An arbitrary matrix or trace-test functional cannot inhabit this structure.
- Define the Born value as the real part of `trace (E * ρ)`. Prove that the
  trace pairing is real in this setting and that the value lies in `[0,1]`;
  do not postulate probability bounds as fields.
- Use the convention `U * ρ * Uᴴ` for unitary evolution. Prove positivity and
  trace preservation from matrix theorems and unitarity, with chronological
  multiplication order explicit.
- Pure densities are ket-bra outer products `ψ * ψᴴ`. Basis densities and
  basis effects are their computational-basis specializations, and their Born
  values must recover the existing real/complex basis weights.
- Prove physical-effect separation using normalized rank-one projectors and
  symmetric/Hermitian quadratic-form polarization. A separately named
  algebraic trace-test lemma may support the proof, but it cannot replace the
  quantifier over `Effect`.

## Big Picture Objective

Build the smallest reusable finite real/complex physical state-and-effect
layer needed for rigorous unitary channels: trace-one positive-semidefinite
density matrices, Loewner-interval effects, Born values with proved bounds,
unitary conjugation, pure/basis compatibility, and a theorem that genuine
physical effects separate density matrices.

## Detailed Implementation Plan

### 6A-DENSITY

- Add `Semantics/Density.lean` with the generic `DensityMatrix 𝕜 I` structure,
  coercion/extensionality API, Hermiticity and trace facts, real/complex
  aliases, and the exact empty-index obstruction.
- Define normalized rank-one pure densities and real/complex constructors from
  the existing `RealState` and `ComplexState`. Define basis densities from
  `basisKet` and prove their entry, positivity, trace, and pure-state laws.
- Define `unitaryConjugate U hU ρ := U * ρ * Uᴴ`. Prove matrix computation,
  positivity, Hermiticity, trace one, identity, and ordered composition.

### 6B-EFFECTS

- Add `Semantics/Effect.lean` with the generic `Effect 𝕜 I` structure, matrix
  coercion/extensionality, positive/complement-positive facts, zero/identity
  effects, real/complex aliases, and normalized rank-one/basis effects.
- Define `bornValue E ρ` from the real part of `trace (E * ρ)`. Prove the trace
  is real, `0 ≤ bornValue`, `bornValue ≤ 1`, complement and zero/identity laws,
  and compatibility with unitary conjugation where useful.
- Prove pure-density/basis-effect and basis-density/basis-effect formulas that
  reduce exactly to existing `State.realWeight` and `State.complexWeight`.

### 6C-SEPARATION

- Add `Semantics/EffectSeparation.lean`. Prove a named quadratic-form identity
  for normalized rank-one effects and show equality of all physical Born
  values forces equality of all normalized quadratic forms.
- Extend from normalized to arbitrary vectors without an impossible division
  case, use symmetry/Hermiticity polarization, and conclude equality of the
  underlying matrices and bundled density matrices for both real and complex
  scalars.
- If an arbitrary trace-test extensionality lemma is exposed, name and document
  it as algebraic support only. The final theorem must quantify over genuine
  `Effect` values.
- Add non-root `Semantics/DensityAudit.lean` with real/complex pure and mixed
  examples, basis effects, empty-index impossibility, unitary evolution,
  bounds, and complete aggregate consumers for every stable export.
- Promote only stable density/effect/separation leaves through the public root,
  add representative axiom endpoints, append every stable declaration to the
  separate Goal 2 manifest, and fold exact evidence into documentation.

## Build Structure

- `Semantics/Density.lean`: low-dependency physical state definitions,
  pure/basis constructors, and unitary conjugation. It may import the current
  state and matrix-unitary leaves plus the narrow mathlib matrix-order API.
- `Semantics/Effect.lean`: physical effects and Born values. It imports
  `Density` but not separation, circuits, diagnostics, or the public root.
- `Semantics/EffectSeparation.lean`: the heavier rank-one and polarization
  proof. It imports `Effect` and the narrow inner-product positivity API.
- `Semantics/DensityAudit.lean`: non-root complete consumers and examples. It
  is never imported by a public semantic leaf or the public root.
- Focused builds target each leaf. Adjacent builds include existing real and
  complex normalized-state/measurement leaves, the public root, and explicit
  axiom audit.

## Boundary Checks

- `DensityMatrix` is positive semidefinite and trace one, not an arbitrary
  Hermitian or normalized-entry matrix. `Effect` is in the Loewner interval,
  not an arbitrary trace test.
- Born equality for basis effects is basis measurement only. Quantification
  over every physical effect and every density input is deferred to Stage 7;
  Stage 6 proves only the state/effect infrastructure and separation theorem.
- Real and complex density/effect theorems share an `RCLike` implementation
  only where the mathematics is genuinely uniform. Quaternionic positivity,
  densities, effects, and channels remain absent.
- `unitaryConjugate` uses `U * ρ * Uᴴ`, not `Uᴴ * ρ * U`, entrywise star, or a
  reordered commutative surrogate.
- Empty index types have no density values; no theorem may exploit an
  impossible density premise to advertise a nonvacuous physical statement.
- Partial trace, Kraus maps, instruments, arbitrary mixed top states, native
  quaternionic density matrices, and channel semantics remain outside this
  stage.

## No-Cheating Checks

- Do not store Hermiticity, probability bounds, or separation as assumptions
  when they follow from the defining physical invariants.
- Do not define an effect as every matrix, use `Matrix.ext_iff_trace_mul_*` as
  if its test matrices were effects, or call equality of diagonal entries
  physical-effect separation.
- Do not prove separation only for pure densities and present it as separation
  of arbitrary density matrices.
- Do not assume a normalized vector exists on an empty type or hide
  nonemptiness in a global instance.
- No `sorry`, `admit`, `sorryAx`, new axiom, opaque/unsafe shortcut, heartbeat
  override, public-root audit import, silent frozen-cohort edit, or theorem
  engineered from contradictory premises.

## Completion Requirements

- Generic and scalar-specialized density/effect structures compile with actual
  positivity, trace, and Loewner-order invariants and real downstream values.
- Pure and basis density/effect constructors compile and recover existing real
  and complex computational-basis weights.
- Unitary conjugation preserves positivity and trace one with identity and
  composition order checked.
- Born values are proved real and lie in `[0,1]`; zero, identity, complement,
  and representative basis laws compile.
- A theorem quantifying over genuine physical effects proves equality of any
  two real or complex density matrices. The empty-index boundary and rank-one
  normalization cases are explicit.
- A non-root audit consumes every stable declaration. Public root, manifest
  exact-set/seven-axis/name/consumer/direct-audit checks, focused/adjacent/root
  builds, warning-as-error checks, exact axiom union, frozen checksum,
  forbidden-token, artifact, whitespace, and diff checks pass.
- Documentation records the conventions and explicitly leaves partial trace,
  Kraus channels, quaternionic mixed states, and Stage 7 channel relations out.

## Stage Results

- In progress.
