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
- **Status:** confirmed overstatement; a corrected sufficient interchange
  theorem and explicit success/failure boundary examples are proved.
- **Diagnosis:** over a noncommutative semiring, the interchange calculation
  changes the order of entries from the second left factor and first right
  factor.  A sufficient entrywise condition is that every entry of `B` commute
  with every entry of `C`.  The source instead names `C` and `D` as 0–1
  matrices, although `D` is not one of the factors whose order crosses.
  Zero–one middle factors are sufficient, but the phrase “only if” is false:
  non-zero–one central or mutually commuting entries also work.
- **Repair:** define `EntrywiseCommute B C` and prove the rectangular identity
  under that sufficient hypothesis.  Derive the commutative and zero–one
  special cases.  A quaternionic `1 × 1` example proves interchange with
  non-zero–one named right-hand factors, while a second example with middle
  entries `i` and `j` proves failure.  These results deliberately do not claim
  that entrywise commutation is necessary.  Independently, `place` continues
  to use the narrower identity-complement law needed by the simulations.
- **Lean declarations:** `Matrix.EntrywiseCommute`,
  `kronecker_mul_kronecker_of_entrywiseCommute`,
  `kronecker_mul_kronecker_commutative`,
  `IsZeroOneMatrix.entrywiseCommute_left`,
  `IsZeroOneMatrix.entrywiseCommute_right`,
  `disjoint_kronecker_factors_commute_of_entrywiseCommute`,
  `QuaternionExamples.oneByOne_interchange_without_zeroOne`,
  `QuaternionExamples.oneByOne_interchange_i_j_failure`, and the placement
  theorem `Circuit.kronecker_one_mul`.
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
  or operators.  The normalized bottom weights are additionally packaged as
  equal finite distributions, yielding equal weight for every finite event and
  equal distribution after every deterministic finite postprocessing map.
- **Lean declarations:** `eval_realifyCircuit`,
  `eval_complexifyCircuit`, all `eval_*_mulVec_wire*` theorems,
  `realifyCircuitOutput_bottomProbability`,
  `complexifyCircuitOutput_bottomProbability`,
  `realifyCircuitBottomDistribution_eq`,
  `complexifyCircuitBottomDistribution_eq`,
  `realifyCircuitOutput_pushforward_eq`,
  `complexifyCircuitOutput_pushforward_eq`,
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
- **Status:** confirmed gap; generic synthesis remains unresolved, while its
  valid conditional consequences are formalized.
- **Diagnosis:** the paper asserts that a generic `2^(d+1) × 2^(d+1)` unitary
  can be decomposed into at most `2^(d+1)` elementary gates.  No decomposition
  theorem, primitive library, approximation convention, or gate model is
  supplied.  Moreover, the advertised full dense local matrix already has
  exactly `4^d` scalar-entry slots before adding the image wire, so neither the
  claimed `O(2^d)` reading time nor the primitive count follows from dense
  description size.  Slot count alone is not a formal runtime lower bound, but
  it exposes the missing encoding assumption.
- **Repair:** retain the exact same-count result for unrestricted `(d+1)`-ary
  abstract image gates and prove the dense-slot formula separately.  An
  `ExactGateCompiler` is only user-supplied certified data containing a
  primitive predicate, exact expansion, primitive membership, and evaluator
  equality.  From such data, compiled count is the exact sum of per-gate
  counts and is at most `s*K` under an explicit per-image-gate bound `K`.
  No compiler instance or `2^(d+1)` synthesis theorem is postulated.
- **Lean declarations:** `PlacedGate.denseEntrySlots_eq_four_pow`,
  `OrderedCircuit.totalDenseEntrySlots_le_gateCount_mul_four_pow`,
  `Circuit.ExactGateCompiler`, `ExactGateCompiler.eval_compileCircuit`,
  `gateCount_compileCircuit`, `gateCount_compileCircuit_le`,
  `Simulation.eval_compile_realifyCircuit`,
  `eval_compile_complexifyCircuit`, `gateCount_compile_realifyCircuit_le`,
  and `gateCount_compile_complexifyCircuit_le`.
- **Dependents:** Table 1, “efficient similar size” conclusions, and BQP prose.

## C-014 — Gate-count variable typo and depth inconsistency

- **Source:** lines 1184 and 1178–1196.
- **Status:** confirmed textual inconsistency; corrected finite count/depth
  statements are proved in explicit models.
- **Diagnosis:** line 1184 says the total gate count is not exactly `n` but
  `O(n)`, although gate count is denoted `s`.  Table 1 gives target depth
  `t 2^(d+1)`, while the shared-top-wire construction serializes gates and the
  preceding text allows worst-case depth `s` before decomposition.
- **Repair:** gate count is consistently `s`.  `SupportLayering` defines depth
  by nonempty support-disjoint layers that flatten to the exact chronology.
  Every layering has depth at most gate count, while every layering of either
  literal shared-top image has depth exactly `s`.  After a supplied exact
  compiler, the exact primitive count is a sum and only the canonical serial
  depth is bounded by `s*K` under the explicit per-gate premise.  Corrected
  Table 1 therefore separates the source, literal abstract image, and
  conditional compiled target instead of retaining `t*2^(d+1)`.
- **Lean declarations:** `Circuit.SupportLayering`, `depth_le_gateCount`,
  `depth_eq_gateCount_of_commonWire`,
  `Simulation.depth_realifyCircuit_eq_gateCount`,
  `depth_complexifyCircuit_eq_gateCount`,
  `depth_quaternionToRealCircuit_eq_gateCount`, and the conditional
  `depth_compileRealifyCircuitSerialLayering_le` and
  `depth_compileComplexifyCircuitSerialLayering_le`.
- **Dependents:** Section 5.1 and final efficiency claims.

## C-015 — Unproved logarithmic-depth alternative

- **Source:** line 671.
- **Status:** unresolved; the missing construction cannot be recovered from
  the paper or the one-shared-wire implementation.
- **Diagnosis:** the claim that several top wires can be recombined with only
  `O(log s)` depth increase gives no construction, ancilla bound, gate set, or
  correctness proof.
- **Repair:** no logarithmic-depth theorem is stated.  The proved result is
  instead exact for the literal construction: every support-disjoint layering
  has depth `s` because all image gates use its one shared top wire.  This
  neither proves nor rules out a different multi-top translation.  Recovering
  the source claim would require the missing construction, ancilla count,
  fan-in/gate-set model, and correctness proof.
- **Lean declarations:** `Simulation.depth_realifyCircuit_eq_gateCount` and
  `depth_complexifyCircuit_eq_gateCount` delimit the available construction.
- **Dependents:** real-simulation resource discussion.

## C-016 — Improper-image target typo and low-dimensional exception

- **Source:** converse discussion, line 1251.
- **Status:** confirmed target error; corrected dimension-four non-surjectivity
  witnesses proved.
- **Diagnosis:** the displayed complexification has complex unitary target in
  dimension `2N`, with image satisfying an additional complex-symplectic
  identity.  It does not have the paper's stated `Sp(2N)` codomain in the
  converse sentence.  If that notation means the compact unitary-symplectic
  group, it describes the image rather than a larger target; if the intended
  target is `SU(2N)`, the blanket “does not span” claim has the low-rank
  exception `Sp(1) ≅ SU(2)`.  The analogous realification statement is about
  the full `U(N)` source used by the construction, for which `U(1) → SO(2)` is
  likewise the exceptional onto case.  The library's general `SU(2N)` image
  refinement remains subject to the determinant-sign gap in C-004.
- **Repair:** replace the counting argument by exact witnesses in the first
  dimension needed uniformly by both displayed embeddings.  The real matrix
  `diag(-1,-1,1,1)` lies in `SO(4)` but is not the realification of any complex
  `2 × 2` matrix because the two realification diagonal blocks must agree.
  The same diagonal matrix over `ℂ` lies in `SU(4)` but is not the
  complexification of any quaternionic `2 × 2` matrix because the two diagonal
  blocks would have to be complex conjugates.  These are set-theoretic
  nonimage theorems even before restricting the sources to unitaries.  No
  result is asserted at `N = 1`, and no circuit-width, communication,
  signaling, or information-processing lower bound is inferred.
- **Lean declarations:**
  `Matrix.ProperImage.realWitness_specialOrthogonal_not_realify` and
  `Matrix.ProperImage.complexWitness_specialUnitary_not_complexify`.
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
- **Status:** confirmed qualification needed; corrected sufficient
  independence and existential dependence results are proved.
- **Diagnosis:** quaternionic circuits *can* depend on evaluation order, but
  circuits with real/central or commuting relevant entries need not.  Distinct
  operators also do not automatically imply distinct statistics for every
  input and measurement.
- **Repair:** `LegalSchedule.scheduledEval_eq_of_pairwise_commute` proves that
  all supplied legal schedules agree when every pair of distinct global gate
  denotations commutes.  In the other direction, two rational locally unitary
  quaternionic mixers with `i` and `j` off-diagonal directions are placed on
  disjoint Boolean wires.  The empty precedence relation admits both orders,
  whose operators are unequal.  On one explicitly normalized input, their
  `00` outcome weights are respectively `8281/15625` and `1369/15625`.
  Complexification preserves the operator inequality and both exact weights.
  A complementary diagnostic starts from the normalized, pointwise-factorized
  ground column.  The two orders agree at `00`, `01`, and `10` but give
  opposite `∓(16/25)k` amplitudes at `11`; their normalized outputs are not
  related by any unit right phase, while every computational-basis weight is
  nevertheless equal.  Together these are existential witnesses, not a
  theorem about every disjoint pair or every input/measurement, and neither
  establishes signaling, entanglement, causality violation, or security.
- **Lean declarations:** `Circuit.LegalSchedule.scheduledEval_eq_of_pairwise_commute`;
  `Circuit.OrderingWitness.gate_supports_disjoint`, `iGate_locallyUnitary`,
  `jGate_locallyUnitary`, `scheduled_operators_ne`,
  `output_basis00_weight_ne`; and
  `Simulation.OrderingWitness.complexified_scheduled_operators_ne`,
  `complexOutput_basis00_weight_ne`; plus
  `Circuit.ProductInputOrderingWitness.groundColumn_product`,
  `ground_outputs_not_rightPhaseEquivalent`, and
  `ground_outputs_basis_weights_eq`.
- **Dependents:** Definitions 4–5, physical interpretations, and bit-commitment
  discussion.

## C-019 — Resource conclusions require an encoding model

- **Source:** lines 432, 673, 1176–1198, and 1239–1241.
- **Status:** confirmed missing assumptions; exact finite structural and
  conditional compiler results are proved, but runtime/uniformity conclusions
  remain outside the formal model.
- **Diagnosis:** constant-time gate conversion, linear description conversion,
  and BQP-level efficiency depend on how arbitrary real/complex/quaternionic
  entries and gates are encoded and synthesized.  Matrix dimensions alone do
  not provide those conclusions.
- **Repair:** distinguish exact finite algebraic translation from uniform
  computable circuit families.  The abstract model now proves unchanged list
  gate count, exact width `+1`/`+2`, exact per-gate local arity `+1`/`+2`,
  transformed arity bounds, and maximum-arity results with the necessary
  nonempty hypothesis.  It additionally proves literal shared-top support
  depth, exact dense scalar-slot factors, exact empty-precedence schedule
  count, and deterministic finite postprocessing preservation.  Generic work
  and primitive-count bounds expose explicit per-gate `K` premises and a
  supplied `ExactGateCompiler`; they do not produce either.  Discrete scalar
  encodings, arithmetic/approximation cost, topological sorting, synthesis,
  uniform generators, polynomial runtime, and BQP containment remain
  unformalized.
- **Lean declarations:** `Circuit.card_addedWire`, `ArityBound`,
  `maxLocalArity`, the primary `gateCount_*`, `mem_*_arity`,
  `arityBound_*`, `maxLocalArity_*` families and their composed analogues;
  `SupportLayering`, `denseEntrySlots`, `totalDenseEntrySlots`,
  `translationWork_le_gateCount_mul`, `ExactGateCompiler`,
  `allChronologicalOrders`, `FiniteDistribution`, and the simulation resource
  and postprocessing theorem families.
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
- **Status:** confirmed overgeneralization; the corrected finite circuit
  assumptions and their noncommutative boundary are explicit and proved.
- **Diagnosis:** an inner product and linear structure give single-system state
  evolution and weights, but not automatically a coherent subsystem tensor
  product, local gate embedding, or order-independent parallel composition.
  The paper's own Equation (46) demonstrates the missing structure.
- **Repair:** formalize only explicitly constructed finite state spaces and
  locality-certified placement semantics.  The corrected Kronecker theorem
  uses entrywise commutation of the middle factors as a sufficient hypothesis;
  finite legal schedules retain order when this hypothesis is unavailable,
  and the disjoint `i`/`j` witness shows that support separation alone does not
  restore commutation.  No classification theorem for arbitrary Hilbert-space
  scalar systems is inferred.
- **Lean declarations:** `Circuit.PlacedGate`, `Circuit.place`,
  `Matrix.EntrywiseCommute`,
  `Matrix.kronecker_mul_kronecker_of_entrywiseCommute`,
  `Circuit.LegalSchedule`,
  `Circuit.LegalSchedule.scheduledEval_eq_of_pairwise_commute`, and
  `Circuit.OrderingWitness.output_basis00_weight_ne`.
- **Dependents:** model-soundness prose and Definitions 4–5.

## C-024 — Algebraic exactness conflicts with finite-precision descriptions

- **Source:** Theorems 2/4 and footnote 6 at line 1292.
- **Status:** confirmed scope ambiguity; exact abstract and conditional exact
  compilation sides are proved, while finite-precision compilation remains
  deliberately unclaimed.
- **Diagnosis:** the main theorems repeatedly say “exact,” while the footnote
  says gate matrices supplied to the simulator are finite-precision
  approximations.  Exact equality of abstract matrices and approximate,
  effectively encoded circuit compilation are different results.
- **Repair:** `complexToReal_exactSimulation`,
  `quaternionToComplex_exactSimulation`, and
  `quaternionToReal_exactSimulation` prove exact algebraic translations for
  exact input matrices.  `ExactGateCompiler` can further preserve those
  operators only from a supplied exact certificate.  The library has no
  discrete scalar representation, rounding semantics, error metric,
  accumulation/stability theorem, or computable approximate compiler.
  Consequently finite precision, uniform approximation, and their runtimes
  are not consequences of any exact theorem here.
- **Lean declarations:** the three `*exactSimulation` families and
  `ExactGateCompiler.eval_compileCircuit` mark the exact side of the boundary;
  no approximation declaration is introduced.
- **Dependents:** Theorems 2/4, preprocessing bounds, and BQP conclusions.

## C-025 — Equation 63 is an embedding, not an isomorphism onto `SO(4N)`

- **Source:** Equation 63 and the sentence following it, lines 1208–1221.
- **Status:** coordinate formula verified; group statement corrected and
  proved, including explicit properness at quaternionic rank one.
- **Diagnosis:** the displayed `4 × 4` scalar formula is mathematically sound,
  but its coordinate order is not the nested sum order produced literally by
  first complexifying and then realifying.  More importantly, the paper says
  that the formula induces a group isomorphism from `Sp(N)` “to `SO(4N)`.”
  Read as surjectivity onto the whole special orthogonal group, this is false;
  the map is an injective homomorphism and hence an isomorphism only onto its
  image.
- **Repair:** use the transparent sector order `[Re, ImI, ImK, ImJ]` and prove
  all 16 displayed entries.  The resulting `directRealify` is exactly
  `realify (complexify A)` after applying the same pure sector permutation
  `[3,1,0,2]` to rows and columns; no additional basis signs occur.  The map is
  injective, multiplicative, adjoint-preserving, and sends quaternionic
  unitaries to `SO(4N)` with determinant one.  The induced unitary-group map is
  explicitly equivalent to its image.  Finally,
  `diag(-1,-1,1,1)` in the paper-sector order lies in `SO(4)` but cannot be the
  direct realification of any quaternionic `1 × 1` matrix, because all four
  direct-image diagonal coordinates would have to equal the same real part.
- **Lean declarations:** `Quaternion.card_directRealIndex`,
  `Quaternion.directRealify`, its 16 `directRealify_*_*` coordinate lemmas,
  `directRealify_eq_reindex`, `directRealify_mul`,
  `directRealify_conjTranspose`, `directRealify_injective`,
  `directRealify_mem_specialOrthogonal`,
  `directRealifyUnitaryEquivImage`, and
  `Matrix.ProperImage.directWitness_specialOrthogonal_not_directRealify`.
- **Dependents:** the optional direct proof of Corollary 1, the converse/image
  discussion, and the interpretation of the two added real sectors.

## C-026 — Ground-state “without loss of generality” hides preparation assumptions

- **Source:** algorithm convention at line 59 and the basis-input
  specialization at line 561.
- **Status:** ambiguity confirmed; the known computational-basis case is
  corrected and proved, while no uniform arbitrary-state preparation claim is
  used.
- **Diagnosis:** replacing an arbitrary pure input by the all-zero input can
  mean several different things: existence of a unitary carrying the ground
  vector to a fixed known state, an exact gate decomposition for that unitary,
  or a uniform efficient procedure from a finite state description.  The
  source does not distinguish these levels.  Its later simulation argument
  only needs a classically known computational-basis input, and the library's
  central state-evolution theorems already quantify over arbitrary source
  columns directly.
- **Repair:** for any known finite basis assignment `b`, XOR by `b` is packaged
  as a full-support permutation gate.  It is locally and globally unitary,
  sends the all-zero basis column exactly to `b`, and may be prepended to an
  ordered circuit with the expected chronological semantics.  This proves the
  finite basis-input reduction actually used by the paper, but does not claim
  preparation of an unknown state, primitive synthesis, a discrete input
  language, or uniform runtime.
- **Lean declarations:** `Circuit.groundBasis`, `xorBasisEquiv`,
  `basisPreparationMatrix_mem_unitary`,
  `basisPreparationGate_mulVec_ground`, and
  `eval_prepend_basisPreparation_mulVec_ground`.
- **Dependents:** the input convention in Definitions 2 and 5 and all resource
  or uniformity interpretations of state preparation; the central exact
  simulation theorems themselves do not require this reduction.
