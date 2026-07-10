# Correction and Obstruction Log

Statuses in this file are evidence states, not promises: **confirmed** means
the source issue is independently checkable now; **open proof obligation**
means the corrected mathematical target is known but not yet formalized;
**provisional** means further source/API work could change the diagnosis.

## C-001 — Conflicting source dates

- **Source:** front matter and displayed header, lines 1–14.
- **Status:** confirmed metadata ambiguity; documentation-only.
- **Diagnosis:** the extraction gives February 1, 2008, while the displayed
  arXiv label says version 2 dated November 5, 2004.
- **Resolution:** identify the work by title, authors, and
  `quant-ph/0307017v2`; preserve both dates rather than selecting one silently.
- **Dependents:** bibliographic documentation only.

## C-002 — Realification target dimension and domain

- **Source:** Theorem 3, line 207; compare Equation (8), lines 181–189.
- **Status:** confirmed statement error; proof target open.
- **Diagnosis:** Equation (8) has four `N × N` blocks, so its image is
  `2N × 2N`, not `N × N`.  Thus `G_N ≤ SO(N)` is ill-typed and must read
  `G_N ≤ SO(2N)`.  Moreover, the construction and proof begin with an arbitrary
  unitary matrix; restriction from `U(N)` to `SU(N)` is unnecessary for the
  orthogonal image result.
- **Repair:** prove the stronger embedding of the full complex unitary group
  into `SO(2N)`, separating orthogonality from the determinant calculation.
- **Lean declaration:** to be assigned in Stage 3.
- **Dependents:** Lemmas 1–5, Theorem 2, the universality discussion, and the
  quaternionic proof template.

## C-003 — Quaternionic image target dimension

- **Source:** Theorem 5, line 891; compare Equations (47)–(48), lines 863–886.
- **Status:** confirmed statement error; proof target open.
- **Diagnosis:** the displayed image has four `N × N` complex blocks and hence
  lies in dimension `2N`; `\widehat G_N ≤ SU(N)` must be
  `\widehat G_N ≤ SU(2N)`.
- **Repair:** prove an injective star-preserving group homomorphism into the
  complex unitary group in dimension `2N`; treat determinant one separately as
  C-004.
- **Lean declaration:** to be assigned in Stage 3.
- **Dependents:** Lemmas 6–10, Theorem 4, Corollary 1, and Section 5.

## C-004 — Missing determinant-one argument in Theorem 5

- **Source:** Theorem 5 and its claimed proof, lines 889–965.
- **Status:** confirmed proof gap; open proof obligation.
- **Diagnosis:** Lemmas 6 and 7 prove multiplicativity and adjoint preservation,
  which imply a unitary image.  They do not prove that the complex determinant
  is `1`.  Unitarity alone only gives determinant modulus one.
- **Repair:** first export the sufficient and stronger-for-reuse unitary image
  theorem.  Prove the special-unitary refinement independently if an algebraic
  or topological proof can be formalized; otherwise mark only that refinement
  unresolved and explain that the simulation does not depend on it.
- **Lean declaration:** to be assigned in Stage 3.
- **Dependents:** the exact status of Theorem 5; no dependency of the central
  operator or measurement simulation on determinant one.

## C-005 — Missing normalization equation for quaterbits

- **Source:** Definition 3, Equation (44), lines 793–800.
- **Status:** confirmed typographical omission.
- **Diagnosis:** the prose says “unit vector,” but the displayed condition only
  defines the norm expression and never states that it equals `1`.
- **Repair:** define a valid pure quaterbit/state by norm square `1` (equivalently
  norm `1`), while keeping algebraic vector lemmas normalization-free.
- **Lean declaration:** to be assigned in Stage 4.
- **Dependents:** measurement probabilities and all state-level simulation
  statements.

## C-006 — Quaternionic global phase is on the wrong side

- **Source:** Definition 3, Equation (45), lines 802–810.
- **Status:** confirmed convention error.
- **Diagnosis:** column vectors acted on by quaternionic matrices from the left
  form a right quaternionic module.  Right phase is respected by evolution,
  `A(ψq) = (Aψ)q`.  The paper's left phase generally is not:
  `A(qψ)` cannot move `q` past arbitrary entries of `A`.
- **Repair:** use unit right phase, `ψ = ψ' q` with `|q| = 1`.  Keep the side
  explicit in every ray/evolution theorem.
- **Lean declaration:** to be assigned in Stage 4.
- **Dependents:** Definition 3, physical-state equivalence, initialization, and
  any statement phrased as state rather than measurement equality.

## C-007 — Overstated linearity of state realification

- **Source:** discussion following Equations (18)–(19), lines 378–397.
- **Status:** confirmed imprecision.
- **Diagnosis:** splitting a complex vector into real and imaginary parts is
  real-linear, not complex-linear.  Calling both maps simply “proper linear
  homomorphisms” hides the scalar field.  Quaternionic analogues likewise need
  a precisely stated restricted or semilinear action.
- **Repair:** export additive/real-linear properties and only stronger scalar
  laws that are proved with an explicit action.
- **Lean declaration:** to be assigned in Stages 2 and 4.
- **Dependents:** state embeddings, phase behavior, and Lemmas 4/9.

## C-008 — Wrong codomain named for `h₀` and `h₁`

- **Source:** initialization discussion, line 493.
- **Status:** confirmed typographical error.
- **Diagnosis:** the text calls `h₀,h₁` maps from `H_C^N` to `H_C^N`, although
  Equations (18)–(19) map an `N`-dimensional complex vector to a
  `2N`-dimensional real vector.
- **Repair:** state the codomain as the doubled real space.
- **Dependents:** Lemmas 4 and 5.

## C-009 — Incorrect noncommutative Kronecker condition

- **Source:** Equation (46) and following sentence, lines 822–835.
- **Status:** confirmed overstatement; exact formal theorem open.
- **Diagnosis:** over a noncommutative semiring, the interchange calculation
  changes the order of entries from the second left factor and first right
  factor.  A sufficient entrywise condition is that every entry of `B` commute
  with every entry of `C`.  Requiring both `C` and `D` to be 0–1 matrices is not
  necessary, and the phrase “only if” is false (many non-0–1 central or mutually
  commuting entries work).
- **Repair:** prove the entrywise commutation theorem and concrete failure
  witness.  Define quaternionic gate placement without assuming interchange.
- **Lean declaration:** to be assigned in Stages 5 and 7.
- **Dependents:** circuit composition, ordering ambiguity, Figures 6–7, and all
  local-to-global simulation lemmas.

## C-010 — “Exactly simulates the operator” is underspecified

- **Source:** Theorem 4, line 855; similarly Theorem 2, line 169.
- **Status:** confirmed type/semantic ambiguity.
- **Diagnosis:** source and target operators have different scalar fields and
  dimensions, so they cannot literally be equal.  Operator embedding,
  compatibility on embedded states, and equality of bottom-wire measurement
  distributions are distinct claims.
- **Repair:** export these as separate theorems and use observable equality as
  the computational simulation conclusion.
- **Lean declaration:** to be assigned in Stage 6.
- **Dependents:** all “exact simulation” and computational-power prose.

## C-011 — Malformed tensor display for `\widehat h`

- **Source:** Equation (48), lines 875–886.
- **Status:** confirmed presentation error.
- **Diagnosis:** the displayed aligned equation starts with a bare equals sign
  and no left-hand expression.  Its “tensor” is an operator-valued mnemonic,
  not a standard scalar Kronecker product.
- **Repair:** use the explicit block matrix as the definition and treat the
  tensor notation only as source motivation.
- **Dependents:** Lemmas 6–10.

## C-012 — Undefined final state in Lemma 9

- **Source:** Lemma 9, lines 1007–1015 and continuation.
- **Status:** confirmed missing hypothesis/definition.
- **Diagnosis:** the lemma quantifies `|Ψ⟩` but uses `|Φ⟩` without stating
  `|Φ⟩ = Q|Ψ⟩`; nearby formulas also mix subscripts on source and embedded
  vectors.
- **Repair:** state the evolution equation explicitly and type every source and
  target vector.
- **Lean declaration:** to be assigned in Stage 4 or 6.
- **Dependents:** Lemma 10 and Theorem 4.

## C-013 — Generic gate-decomposition bound is unsupported and likely false

- **Source:** Section 5.1, lines 1180–1198, especially line 1182 and Table 1.
- **Status:** confirmed gap; quantitative repair deferred to Stage 8.
- **Diagnosis:** the paper asserts that a generic `2^(d+1) × 2^(d+1)` unitary
  can be decomposed into at most `2^(d+1)` elementary gates.  No decomposition
  theorem or gate model is supplied.  Standard parameter counting for fixed-
  arity gates indicates a generic unitary requires order `4^d`, not `2^d`,
  gates.  The table therefore cannot be accepted as proved.
- **Repair:** define the gate library/encoding and use a verified synthesis bound
  if formalized; otherwise retain only the exact same-count bound for
  unrestricted `(d+1)`-ary image gates and mark elementary-gate asymptotics
  unresolved/corrected.
- **Dependents:** Table 1, “efficient similar size” conclusions, and BQP prose.

## C-014 — Gate-count variable typo and depth inconsistency

- **Source:** lines 1184 and 1178–1196.
- **Status:** confirmed textual inconsistency; cost theorem open.
- **Diagnosis:** line 1184 says the total gate count is not exactly `n` but
  `O(n)`, although gate count is denoted `s`.  Table 1 gives target depth
  `t 2^(d+1)`, while the shared-top-wire construction serializes gates and the
  preceding text allows worst-case depth `s` before decomposition.
- **Repair:** define size, width, and depth independently; derive bounds from
  the actual translated schedule rather than repairing symbols by guesswork.
- **Dependents:** Section 5.1 and final efficiency claims.

## C-015 — Unproved logarithmic-depth alternative

- **Source:** line 671.
- **Status:** open proof obligation.
- **Diagnosis:** the claim that several top wires can be recombined with only
  `O(log s)` depth increase gives no construction, ancilla bound, gate set, or
  correctness proof.
- **Repair:** formalize a fan-in/recombination construction and cost model, or
  classify this claim unresolved.  It is not needed for exact simulation.
- **Dependents:** real-simulation resource discussion.

## C-016 — Improper-image target typo and low-dimensional exception

- **Source:** converse discussion, line 1251.
- **Status:** confirmed target error; properness theorem open.
- **Diagnosis:** `\widehat h` maps into `SU(2N)`, not `Sp(2N)`.  Moreover,
  `Sp(1) ≅ SU(2)`, so a blanket “does not span” claim needs a dimension/nontrivial
  system qualification.  The analogous realification statement also depends
  on whether the domain is `SU(N)` or the stronger `U(N)`.
- **Repair:** state separate proper-image results with exact domain, codomain,
  and size hypotheses; do not use an informal counting argument as a proof.
- **Dependents:** claimed non-converses and information-processing discussion.

## C-017 — Method limitation presented as impossibility

- **Source:** line 1204 before Corollary 1.
- **Status:** confirmed logical overreach.
- **Diagnosis:** failure of the displayed method to use only `n+1` rebits does
  not prove that no other exact simulation with that width exists.  The next
  sentence also calls an `(n+2)`-rebit construction “just one extra rebit,”
  which is ambiguous about the baseline.
- **Repair:** record only that composing the two embeddings yields `n+2`
  rebits; make no lower-bound claim without a proof.
- **Dependents:** Corollary 1 interpretation, not its constructive upper bound.

## C-018 — Universal order-dependence is too strong

- **Source:** lines 835–839, 1223–1229, and conclusions at line 1239.
- **Status:** confirmed qualification needed.
- **Diagnosis:** quaternionic circuits *can* depend on evaluation order, but
  circuits with real/central or commuting relevant entries need not.  Distinct
  operators also do not automatically imply distinct statistics for every
  input and measurement.
- **Repair:** prove an explicit order-sensitive operator/outcome witness and
  separate it from sufficient order-independence hypotheses.
- **Lean declaration:** to be assigned in Stage 7.
- **Dependents:** Definitions 4–5, physical interpretations, and bit-commitment
  discussion.

## C-019 — Resource conclusions require an encoding model

- **Source:** lines 432, 673, 1176–1198, and 1239–1241.
- **Status:** confirmed missing assumptions.
- **Diagnosis:** constant-time gate conversion, linear description conversion,
  and BQP-level efficiency depend on how arbitrary real/complex/quaternionic
  entries and gates are encoded and synthesized.  Matrix dimensions alone do
  not provide those conclusions.
- **Repair:** distinguish exact finite algebraic translation from uniform
  computable circuit families and state every cost theorem relative to an
  explicit encoding and primitive-gate model.
- **Dependents:** Theorems 2/4 as complexity claims, Section 5, and conclusions.

