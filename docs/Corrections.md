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
- **Status:** corrected and proved.
- **Diagnosis:** Equation (8) has four `N × N` blocks, so its image is
  `2N × 2N`, not `N × N`.  Thus `G_N ≤ SO(N)` is ill-typed and must read
  `G_N ≤ SO(2N)`.  Moreover, the construction and proof begin with an arbitrary
  unitary matrix; restriction from `U(N)` to `SU(N)` is unnecessary for the
  orthogonal image result.
- **Repair:** the full complex unitary group is embedded into `SO(2N)`; the
  orthogonal and determinant-one parts are proved separately.
- **Lean declarations:** `Matrix.realifyStarMonoidHom`,
  `Matrix.realifyUnitaryEquivImage`, `Matrix.realify_mem_orthogonal`, and
  `Matrix.realify_mem_specialOrthogonal`.
- **Dependents:** Lemmas 1–5, Theorem 2, the universality discussion, and the
  quaternionic proof template.

## C-003 — Quaternionic image target dimension

- **Source:** Theorem 5, line 891; compare Equations (47)–(48), lines 863–886.
- **Status:** dimension and unitary-image correction proved; special-unitary
  refinement remains C-004.
- **Diagnosis:** the displayed image has four `N × N` complex blocks and hence
  lies in dimension `2N`; `\widehat G_N ≤ SU(N)` must be
  `\widehat G_N ≤ SU(2N)`.
- **Repair:** an injective star-preserving group homomorphism into the complex
  unitary group in dimension `2N` is proved; its image is also complex
  symplectic.  Determinant one is treated separately as C-004.
- **Lean declarations:** `Quaternion.complexifyStarMonoidHom`,
  `Quaternion.complexifyUnitaryEquivImage`,
  `Quaternion.complexify_mem_unitary`, and
  `Quaternion.complexify_mem_symplectic`.
- **Dependents:** Lemmas 6–10, Theorem 4, Corollary 1, and Section 5.

## C-004 — Missing determinant-one argument in Theorem 5

- **Source:** Theorem 5 and its claimed proof, lines 889–965.
- **Status:** confirmed proof gap; unitary image and strongest currently
  justified determinant alternative proved; positive sign unresolved.
- **Diagnosis:** Lemmas 6 and 7 prove multiplicativity and adjoint preservation,
  which imply a unitary image.  They do not prove that the complex determinant
  is `1`.  Unitarity alone only gives determinant modulus one.
- **Repair:** the reusable unitary and symplectic image theorems are exported.
  The block symmetry proves that the complex determinant is real, and
  unitarity then gives the formally checked alternative `det = 1 ∨ det = -1`.
  Excluding the negative branch requires infrastructure absent from the pinned
  mathlib: a Pfaffian congruence theorem, connectedness of the finite compact
  symplectic group, or nonnegativity of the Study determinant.  Mathlib's own
  `LinearAlgebra.SymplecticGroup` file lists determinant one as a TODO and
  proves only that the determinant is a unit.  The simulation does not depend
  on resolving this sign.
- **Lean declarations:** `Quaternion.complexify_det_star_fixed`,
  `complexify_det_im_eq_zero`,
  `complexify_det_sq_eq_one_of_mem_unitary`, and
  `complexify_det_eq_one_or_neg_one_of_mem_unitary`.
- **Dependents:** the exact status of Theorem 5; no dependency of the central
  operator or measurement simulation on determinant one.

## C-005 — Missing normalization equation for quaterbits

- **Source:** Definition 3, Equation (44), lines 793–800.
- **Status:** confirmed typographical omission; corrected and proved.
- **Diagnosis:** the prose says “unit vector,” but the displayed condition only
  defines the norm expression and never states that it equals `1`.
- **Repair:** `Quaterbit` is a `Bool`-indexed quaternionic state whose total
  norm square is definitionally required to equal `1`; algebraic vector lemmas
  remain normalization-free.
- **Lean declarations:** `State.Quaterbit` and
  `State.Quaterbit.normalization`.
- **Dependents:** measurement probabilities and all state-level simulation
  statements.

## C-006 — Quaternionic global phase is on the wrong side

- **Source:** Definition 3, Equation (45), lines 802–810.
- **Status:** confirmed convention error; obstruction and generic repair proved.
- **Diagnosis:** column vectors acted on by quaternionic matrices from the left
  form a right quaternionic module.  Right phase is respected by evolution,
  `A(ψq) = (Aψ)q`.  The paper's left phase generally is not:
  `A(qψ)` cannot move `q` past arbitrary entries of `A`.
- **Evidence:** `phaseWitnessGate` is the norm-preserving two-coordinate
  evolution `diag(1,j)`.  Its input and `i`-left-multiple begin on the same
  left-phase ray, but `not_leftPhaseEquivalent_gate_i_input` proves that no
  output left phase exists.  The separate theorem
  `fixed_left_phase_not_natural` records the one-dimensional noncommutation
  diagnostic without overclaiming ray failure.
- **Repair:** use unit right phase, `ψ = ψ' q` with `|q| = 1`.  Unit right
  phase is now proved to preserve every basis weight, total weight,
  normalization, and arbitrary compatible quaternionic matrix evolution.
- **Lean declarations:**
  `QuaternionicComputing.Quaternion.LeftPhaseEquivalent`,
  `RightPhaseEquivalent`, `phaseWitnessGate_normSq`,
  `not_leftPhaseEquivalent_gate_i_input`, and
  `rightPhaseEquivalent_gate`; plus
  `State.QuaternionState.rightPhase`,
  `State.rightPhaseEquivalent_quaternionBasisWeight`,
  `State.quaternion_mulVec_right_smul`, and
  `State.rightPhaseEquivalent_mulVec`.
- **Dependents:** Definition 3, physical-state equivalence, initialization, and
  any statement phrased as state rather than measurement equality.

## C-007 — Overstated linearity of state realification

- **Source:** discussion following Equations (18)–(19), lines 378–397.
- **Status:** confirmed imprecision; corrected and proved for all four state columns.
- **Diagnosis:** splitting a complex vector into real and imaginary parts is
  real-linear, not complex-linear.  Calling both maps simply “proper linear
  homomorphisms” hides the scalar field.  Quaternionic analogues likewise need
  a precisely stated restricted or semilinear action.
- **Repair:** export additive/real-linear properties and only stronger scalar
  laws that are proved with an explicit action.
- **Lean declarations:** `QuaternionicComputing.Quaternion.complexPart` and
  `jPart` are explicitly `ℝ`-linear; `State.realColumn0Linear`,
  `realColumn1Linear`, `complexColumn0Linear`, and `complexColumn1Linear`
  bundle the state maps with the same exact scalar convention.
- **Dependents:** state embeddings, phase behavior, and Lemmas 4/9.

## C-008 — Wrong codomain named for `h₀` and `h₁`

- **Source:** initialization discussion, line 493.
- **Status:** confirmed typographical error; corrected and proved.
- **Diagnosis:** the text calls `h₀,h₁` maps from `H_C^N` to `H_C^N`, although
  Equations (18)–(19) map an `N`-dimensional complex vector to a
  `2N`-dimensional real vector.
- **Repair:** `realColumn0` and `realColumn1` have codomain `n ⊕ n → ℝ`,
  so the doubled dimension is enforced by their Lean types; their
  reconstruction and injectivity theorems prove no coordinates are lost.
- **Lean declarations:** `State.realColumn0`, `State.realColumn1`,
  `realColumn0_injective`, and `realColumn1_injective`.
- **Dependents:** Lemmas 4 and 5.

## C-009 — Incorrect noncommutative Kronecker condition

- **Source:** Equation (46) and following sentence, lines 822–835.
- **Status:** confirmed overstatement; the noncommutative placement law needed
  by both simulations is proved, while the general criterion remains Stage 7.
- **Diagnosis:** over a noncommutative semiring, the interchange calculation
  changes the order of entries from the second left factor and first right
  factor.  A sufficient entrywise condition is that every entry of `B` commute
  with every entry of `C`.  Requiring both `C` and `D` to be 0–1 matrices is not
  necessary, and the phrase “only if” is false (many non-0–1 central or mutually
  commuting entries work).
- **Repair:** `place` pads only on the right by an identity and reindexes along
  an explicit support split.  `kronecker_one_mul` proves this restricted
  multiplication law through block diagonal matrices over an arbitrary
  semiring, so no coefficient commutativity is assumed.  Stage 7 will add the
  broader entrywise-commutation theorem and concrete failure witness.
- **Lean declarations:** `Circuit.kronecker_one_mul`, `place_mul`,
  `place_mem_unitary`, and `OrderedCircuit.eval_mem_unitary`; the general
  interchange declarations remain to be assigned in Stage 7.
- **Dependents:** circuit composition, ordering ambiguity, Figures 6–7, and all
  local-to-global simulation lemmas.

## C-010 — “Exactly simulates the operator” is underspecified

- **Source:** Theorem 4, line 855; similarly Theorem 2, line 169.
- **Status:** confirmed type/semantic ambiguity; repaired and proved at each
  distinct semantic level.
- **Diagnosis:** source and target operators have different scalar fields and
  dimensions, so they cannot literally be equal.  Operator embedding,
  compatibility on embedded states, and equality of bottom-wire measurement
  distributions are distinct claims.
- **Repair:** the two primary leaves separately export typed operator
  embedding, state-column evolution, normalized source/target output, and
  bottom probability equality.  The packaged exact-simulation theorems include
  these observable conclusions without identifying differently typed states
  or operators.
- **Lean declarations:** `eval_realifyCircuit`,
  `eval_complexifyCircuit`, all `eval_*_mulVec_wire*` theorems,
  `realifyCircuitOutput_bottomProbability`,
  `complexifyCircuitOutput_bottomProbability`,
  `complexToReal_exactSimulation`, and
  `quaternionToComplex_exactSimulation`.
- **Dependents:** all “exact simulation” and computational-power prose.

## C-011 — Malformed tensor display for `\widehat h`

- **Source:** Equation (48), lines 875–886.
- **Status:** confirmed presentation error; corrected definition and laws proved.
- **Diagnosis:** the displayed aligned equation starts with a bare equals sign
  and no left-hand expression.  Its “tensor” is an operator-valued mnemonic,
  not a standard scalar Kronecker product.
- **Repair:** use the explicit block matrix as the definition and treat the
  tensor notation only as source motivation.
- **Lean declarations:** `Quaternion.complexify`, its four block-entry lemmas,
  `complexify_mul`, and `complexify_conjTranspose`.
- **Dependents:** Lemmas 6–10.

## C-012 — Undefined final state in Lemma 9

- **Source:** Lemma 9, lines 1007–1015 and continuation.
- **Status:** confirmed missing hypothesis/definition; repaired and proved.
- **Diagnosis:** the lemma quantifies `|Ψ⟩` but uses `|Φ⟩` without stating
  `|Φ⟩ = Q|Ψ⟩`; nearby formulas also mix subscripts on source and embedded
  vectors.
- **Repair:** eliminate the undefined name by stating the two general typed
  identities directly for arbitrary `A` and `ψ`; specializing the right side
  to a named final state is then ordinary rewriting.
- **Lean declarations:** `State.complexify_mulVec_complexColumn0` and
  `State.complexify_mulVec_complexColumn1`.
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
- **Status:** confirmed logical overreach; constructive upper bound repaired
  and proved.
- **Diagnosis:** failure of the displayed method to use only `n+1` rebits does
  not prove that no other exact simulation with that width exists.  The next
  sentence also calls an `(n+2)`-rebit construction “just one extra rebit,”
  which is ambiguous about the baseline.
- **Repair:** record only that composing the two embeddings yields `n+2`
  rebits; make no lower-bound claim without a proof.  The composition is
  formalized literally, including nested state evolution and four-sector
  bottom probability equality.
- **Lean declarations:** `quaternionToRealCircuit`,
  `eval_quaternionToRealCircuit`,
  `quaternionToRealCircuitOutput_nestedEncoding_apply`,
  `quaternionToRealCircuitOutput_bottomProbability`, and
  `quaternionToReal_exactSimulation`.
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
- **Status:** confirmed missing assumptions; exact abstract structural costs
  proved, encoding/synthesis conclusions remain Stage 8.
- **Diagnosis:** constant-time gate conversion, linear description conversion,
  and BQP-level efficiency depend on how arbitrary real/complex/quaternionic
  entries and gates are encoded and synthesized.  Matrix dimensions alone do
  not provide those conclusions.
- **Repair:** distinguish exact finite algebraic translation from uniform
  computable circuit families.  The abstract model now proves unchanged list
  gate count, exact width `+1`/`+2`, exact per-gate local arity `+1`/`+2`,
  transformed arity bounds, and maximum-arity results with the necessary
  nonempty hypothesis.  Runtime, synthesis, depth, and uniformity still require
  an explicit encoding/primitive-gate model.
- **Lean declarations:** `Circuit.card_addedWire`, `ArityBound`,
  `maxLocalArity`, the primary `gateCount_*`, `mem_*_arity`,
  `arityBound_*`, `maxLocalArity_*` families, and their composed analogues.
- **Dependents:** Theorems 2/4 as complexity claims, Section 5, and conclusions.

## C-020 — Theorem 3 also omits determinant one

- **Source:** proof of Theorem 3, lines 273–320.
- **Status:** confirmed source proof gap; repaired and proved.
- **Diagnosis:** the proof concludes after showing `h(U)ᵀ = h(U)⁻¹`.  This is
  orthogonality, not membership in the special orthogonal group; `det = 1` is
  never established.  The intended stronger result is true via
  `detℝ h(A) = |detℂ A|²`; the source omits that identity entirely.
- **Repair:** `realify_det` proves the determinant identity for every finite
  index type, including the empty type.  It yields determinant one for a
  complex unitary and hence the special-orthogonal refinement.
- **Lean declarations:** `Matrix.realify_det`,
  `Matrix.realify_det_eq_one_of_mem_unitary`, and
  `Matrix.realify_mem_specialOrthogonal`.
- **Dependents:** Theorem 3's final codomain only; Theorem 2 needs orthogonality,
  not determinant one.

## C-021 — State-intertwining proofs are dimensionally ill-typed

- **Source:** proofs of Lemmas 4 and 9, lines 507–558 and 1021–1073.
- **Status:** confirmed derivation error; corrected statements proved.
- **Diagnosis:** the derivations apply encoding columns `T₀/T₁` to already
  encoded vectors such as `Ψ₀`, and let an `N × N` source matrix act where a
  `2N`-vector is shown.  Several hats, subscripts, and signs also change.  These
  products cannot all be typed as written.
- **Repair:** prove the correctly typed componentwise statements
  `h(U) (h₀ ψ) = h₀ (Uψ)` and
  `ĥ(Q) (ĥ₀ ψ) = ĥ₀ (Qψ)`, plus their second-column analogues.
- **Lean declarations:** `State.realify_mulVec_realColumn0`,
  `realify_mulVec_realColumn1`, `complexify_mulVec_complexColumn0`, and
  `complexify_mulVec_complexColumn1`, all generalized to compatible
  rectangular matrices.
- **Dependents:** Lemmas 4/9, Lemmas 5/10, and both central simulations.

## C-022 — Lemma 8 is asserted by analogy without its critical proof

- **Source:** lines 967–980.
- **Status:** confirmed proof omission; repaired and proved locally and for
  arbitrary ordered circuits.
- **Diagnosis:** multiplicativity of `ĥ` handles ordered composition only after
  each local quaternionic gate's contextual placement is shown to map to the
  claimed target placement.  The paper calls the construction “purely formal”
  and supplies no quaternionic padding/naturality proof, even though
  noncommutative tensor behavior is the central hazard.
- **Repair:** local placement is defined by a support equivalence, Kronecker
  with an identity, and reindexing.  `wireComplexify_place` proves directly
  from entries that complexification commutes with this actual placement after
  adjoining one shared top wire; `complexifyPlacedGate_denote` packages the
  result for locality-certified gates.  No general Kronecker interchange is
  used.  `eval_complexifyCircuit` then applies the public ordered-list
  induction helper to prove the full corrected Lemma 8.
- **Lean declarations:** `Circuit.wireComplexify_place`,
  `complexifyPlacedGate_denote`, `OrderedCircuit.eval_map_of_denote_eq`, and
  `Simulation.eval_complexifyCircuit`.
- **Dependents:** Lemma 8 and Theorem 4.

## C-023 — “Any Hilbert space” is insufficient for circuit semantics

- **Source:** line 61 and the transition to quaternionic circuits.
- **Status:** confirmed overgeneralization.
- **Diagnosis:** an inner product and linear structure give single-system state
  evolution and weights, but not automatically a coherent subsystem tensor
  product, local gate embedding, or order-independent parallel composition.
  The paper's own Equation (46) demonstrates the missing structure.
- **Repair:** formalize only explicitly constructed finite state spaces and
  local-placement semantics; document which circuit laws require commutative
  or central coefficients.
- **Dependents:** model-soundness prose and Definitions 4–5.

## C-024 — Algebraic exactness conflicts with finite-precision descriptions

- **Source:** Theorems 2/4 and footnote 6 at line 1292.
- **Status:** confirmed scope ambiguity; exact abstract side proved and
  finite-precision side isolated.
- **Diagnosis:** the main theorems repeatedly say “exact,” while the footnote
  says gate matrices supplied to the simulator are finite-precision
  approximations.  Exact equality of abstract matrices and approximate,
  effectively encoded circuit compilation are different results.
- **Repair:** `complexToReal_exactSimulation`,
  `quaternionToComplex_exactSimulation`, and
  `quaternionToReal_exactSimulation` prove exact algebraic translations for
  exact input matrices.  Approximation error, computable encodings, and uniform
  compilation remain separate Stage 8 obligations and are not consequences of
  these theorems.
- **Dependents:** Theorems 2/4, preprocessing bounds, and BQP conclusions.
