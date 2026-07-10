# Paper-to-Lean Traceability

## Source and status policy

The local source is `Fernandez/fernandez-2003.md`, an extraction of José M.
Fernandez and William A. Schneeberger's *Quaternionic Computing*, labeled
`quant-ph/0307017v2`.  Line locators below refer to that file.  See
`Corrections.md` for diagnoses and repairs.

During implementation, **planned** and **in progress** are temporary statuses.
At release every row marked important must have exactly one terminal status:

- **proved as stated**;
- **corrected and proved**;
- **partially formalized**;
- **intentionally excluded**;
- **unresolved**.

Priorities are `P0` (central dependency cone), `P1` (important reusable result),
`P2` (model/context), and `P3` (external, historical, physical, or speculative).
Lean declaration names replace the current stage targets as proofs land.

## Numbered definitions, theorems, lemmas, and corollary

| ID | Source | Concise target and dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-D01-REBIT` | L92–115, Eq. 4–6 | Normalized vectors in `ℝ²`, with optional pure-state quotient by `±1`. Depends on finite real state conventions. | P2 / 4-STATES | planned; quotient may be partial |
| `FER03-D02-REAL-ALGORITHM` | L140–142 | Classical uniform generator, real circuit measurement, and postprocessing. Depends on circuit/output semantics and an encoding model. | P2 / 8-RESOURCES | planned partial interface |
| `FER03-D03-QUATERBIT` | L791–812, Eq. 44–45 | Normalized vectors in `ℍ²`, right unit phase, and basis weights. Depends on quaternion norm and right-module conventions. | P0 / 4-STATES | planned correction C-005/C-006 |
| `FER03-D04-ORDERED-CIRCUIT-OUTPUT` | L841–849 | Product of explicitly placed gates along one legal order. Depends on noncommutative-safe placement and evaluation order. | P0 / 5-CIRCUITS, 7-ORDERING | planned correction |
| `FER03-D05-QUATERNIONIC-ALGORITHM` | L851 | Uniform generator emits circuit plus legal ordering; ordered state is measured/postprocessed. | P2 / 8-RESOURCES | planned partial interface |
| `FER03-T01-BERNSTEIN-VAZIRANI-REAL-QTM` | L148–156 | External approximate-real-amplitude QTM result. | P3 / 9-COVERAGE | **intentionally excluded**: attributed, unproved, and underspecified in source |
| `FER03-T02-COMPLEX-CIRCUIT-TO-REAL` | L167–170 | Translate `n`-qubit, `s`-gate, arity-`≤d` ordered circuits to `n+1` rebits with `s` image gates of arity `≤d+1`; separately prove operator and observable preservation. | P0 / 6-SIMULATION | planned correction C-010/C-019 |
| `FER03-T03-COMPLEX-REALIFICATION-GROUP` | L173–320 | Injective star-preserving realification; `U(N)` image is in `SO(2N)`. Depends on L01/L02 and determinant identity. | P0 / `Matrix/Unitary.lean`, `Matrix/Determinant.lean` | **corrected and proved**: `realifyStarMonoidHom`, `realifyUnitaryEquivImage`, `realify_mem_specialOrthogonal`; dimension/domain repair C-002 and missing determinant proof C-020 |
| `FER03-T04-ORDERED-QUATERNIONIC-TO-COMPLEX` | L853–855 | Translate a fixed ordered `n`-quaterbit circuit to `n+1` qubits with one arity-`d+1` image gate per source gate; prove embedded evolution and bottom measurement equality. | P0 / 6-SIMULATION | planned correction C-006/C-010 |
| `FER03-T05-QUATERNION-COMPLEXIFICATION-GROUP` | L861–965 | Injective star-preserving homomorphism from quaternionic unitaries to complex unitaries in dimension `2N`; separately audit determinant one. | P0 / `Matrix/Unitary.lean`, `Matrix/Determinant.lean` | **partially formalized**: corrected `U(2N)` and symplectic image proved by `complexifyUnitaryEquivImage`, `complexify_mem_unitary`, `complexify_mem_symplectic`; determinant is formally reduced to `1 ∨ -1`, but the `SU(2N)` sign refinement remains unresolved (C-003/C-004) |
| `FER03-L01-REALIFICATION-MUL` | L211–270, Eq. 11–13 | `h(AB)=h(A)h(B)` for compatible complex matrices. Depends on re/im product identities. | P0 / `Matrix/Realification.lean` | **proved as stated**, generalized to compatible rectangular shapes by `realPart_mul`, `imagPart_mul`, `realify_mul` |
| `FER03-L02-REALIFICATION-ADJOINT` | L282–320, Eq. 15–16 | `h(Aᴴ)=h(A)ᵀ`. | P0 / `Matrix/Realification.lean` | **proved as stated**, generalized to rectangular matrices by `realPart_conjTranspose`, `imagPart_conjTranspose`, `realify_conjTranspose` |
| `FER03-L03-REAL-CIRCUIT-COMPOSITION` | L438–487, Eq. 23 | Evaluation of translated ordered circuit equals realification of source evaluation. Depends on L01 and local placement naturality. | P0 / 6-SIMULATION | planned correction/generalization |
| `FER03-L04-REALIFICATION-INTERTWINES-STATES` | L489–558, Eq. 24–27 | `h(U) h₀(ψ)=h₀(Uψ)` and corresponding `h₁` identity. | P0 / 4-STATES | planned correction of typed proof |
| `FER03-L05-REAL-REDUCED-MEASUREMENT` | L561–659, Eq. 28–33 | Equal reduced real matrices for both encodings and pointwise equality of computational-basis diagonals/weights. | P0 / 4-STATES | planned typed bridge |
| `FER03-L06-QUATERNION-COMPLEXIFICATION-MUL` | L895–927, Eq. 49 | `ĥ(AB)=ĥ(A)ĥ(B)` for compatible quaternion matrices. Depends on Co/Wd multiplication. | P0 / `Matrix/Complexification.lean` | **proved as stated**, generalized to compatible rectangular shapes by `complexPartMatrix_mul`, `jPartMatrix_mul`, `complexify_mul` without commutativity |
| `FER03-L07-QUATERNION-COMPLEXIFICATION-ADJOINT` | L929–965, Eq. 50–51 | `ĥ(Aᴴ)=ĥ(A)ᴴ`. | P0 / `Matrix/Complexification.lean` | **proved as stated**, generalized to rectangular matrices by `complexPartMatrix_conjTranspose`, `jPartMatrix_conjTranspose`, `complexify_conjTranspose` |
| `FER03-L08-QUATERNIONIC-CIRCUIT-COMPOSITION` | L967–980 | Translated ordered operator equals `ĥ(Qσ)`. Depends on L06 and placement naturality. | P0 / 6-SIMULATION | planned; source proof missing |
| `FER03-L09-QUATERNION-STATE-INTERTWINING` | L983–1073, Eq. 52–57 | `ĥ(Q) ĥ₀(ψ)=ĥ₀(Qψ)` and corresponding `ĥ₁` identity. | P0 / 4-STATES | planned correction C-012 |
| `FER03-L10-QUATERNION-COMPUTATIONAL-MEASUREMENT` | L1075–1171, Eq. 58–62 | Each complex encoding preserves bottom computational-basis weights after summing over top qubit. | P0 / 4-STATES | planned typed bridge |
| `FER03-C01-ORDERED-QUATERNIONIC-TO-REAL` | L1202–1221, Eq. 63 | Compose T04 and T02 to simulate with `n+2` rebits; optionally prove direct `4N` real representation. | P1 / 6-SIMULATION, 9-COVERAGE | planned correction C-017 |

## Foundational and model claims

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-FND-COMPLEX-STATE-RAY` | L38, L73–90 | Normalized complex vectors modulo unit right/commutative phase. | P2 / 4-STATES | planned, quotient secondary |
| `FER03-FND-COMPUTATIONAL-MEASUREMENT` | L40–48, Eq. 1 | Basis outcome weight is squared scalar norm; normalized weights sum to one. | P0 / 4-STATES | planned |
| `FER03-FND-LINEAR-ISOMETRY-UNITARY` | L50, FN2 | Complex-linear finite norm preservers are unitary; antiunitaries excluded by linearity. | P2 / 9-COVERAGE | planned or reuse mathlib |
| `FER03-FND-FINITE-DIM-COMPLETE` | FN1 | Finite-dimensional inner-product spaces are complete. | P3 / 9-COVERAGE | **intentionally excluded**: existing background fact not used by finite matrix core |
| `FER03-FND-ARBITRARY-WIRE-ROUTING` | L57, FN3 | Route noncontiguous gates with swaps under an explicit cost model. | P2 / 5-CIRCUITS, 8-RESOURCES | planned partial; quadratic claim needs parameters |
| `FER03-FND-GROUND-STATE-WLOG` | L59, L561 | Absorb known basis input preparation into a circuit; not an unknown-state WLOG. | P1 / 5-CIRCUITS | planned correction |
| `FER03-FND-ANY-HILBERT-SCALARS` | L61 | Claim that any Hilbert scalar system automatically gives a sound circuit model. | P2 / 7-ORDERING | **partially formalized** target: document countervailing subsystem/tensor requirements |
| `FER03-FND-REAL-PRESERVERS-ORTHOGONAL` | L67–69 | A complex-linear map preserving the real subspace has a real matrix; norm preservation gives orthogonality. | P1 / 3-MATRICES | **partially formalized**: the matrix-level norm-preserving consequence needed here is `realify_mem_orthogonal`; the broader invariant-real-subspace characterization is not used by the simulations |
| `FER03-FND-REAL-CIRCUIT-SOUNDNESS` | L119–134 | Products and legal placements of orthogonal gates remain orthogonal. | P1 / 5-CIRCUITS | planned |
| `FER03-FND-OUTCOME-EQUIVALENCE-SUFFICES` | L140–142 | Classical postprocessing only observes the output distribution. | P0 / 4-STATES | planned semantic definition |
| `FER03-FND-FINITE-PRECISION` | FN6 | Classical descriptions contain finite-precision approximations. | P1 / 8-RESOURCES | planned partial; separate from algebraic exactness |

## Complex-to-real algebra, states, and circuits

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-R-REALIFICATION-DEF` | L175–203, Eq. 8–10 | Define `h(A)=[[re A,im A],[-im A,re A]]`; tensor notation only mnemonic. | P0 / `Matrix/Realification.lean` | **proved as stated**: `realPart`, `imagPart`, `realify` and four block-entry lemmas; the operator-valued tensor mnemonic is intentionally not encoded |
| `FER03-R-REIM-PRODUCT` | L213–239, Eq. 11–12 | Scalar and compatible-matrix real/imaginary product formulas. | P0 / mathlib, `Matrix/Realification.lean` | **proved as stated**: scalar `Complex.mul_re`/`Complex.mul_im`; matrix `realPart_mul`/`imagPart_mul` |
| `FER03-R-REIM-ADJOINT` | L310–318, Eq. 16 | Real/imaginary components of complex adjoint. | P0 / `Matrix/Realification.lean` | **proved as stated**: `realPart_conjTranspose`, `imagPart_conjTranspose` |
| `FER03-R-SERIAL-COMPOSITION` | L322–340, Fig. 1 | A legal order gives a reverse chronological matrix product. | P0 / 5-CIRCUITS | planned |
| `FER03-R-TOPO-SORT-COMPLEXITY` | L336, FN5 | Topological sorting is efficient; circuit/TM equivalence is external. | P2 / 7-ORDERING, 8-RESOURCES | planned partial |
| `FER03-R-QUANTUM-GATE-PADDING` | L344–363, Eq. 17, Fig. 2 | Lift arbitrary-arity local gate to noncontiguous wires via explicit support/permutation. | P0 / 5-CIRCUITS | planned correction/generalization |
| `FER03-R-STATE-ENCODINGS` | L365–390, Eq. 18–19 | `h₀(z)=(re z,-im z)`, `h₁(z)=(im z,re z)` coordinatewise. | P0 / 4-STATES | planned |
| `FER03-R-ENCODINGS-ORTHOGONAL` | L393 | Both state encodings preserve norm and are mutually real-orthogonal. | P1 / 4-STATES | planned |
| `FER03-R-ENCODINGS-LINEAR` | L393 | Encodings are additive and `ℝ`-linear, not `ℂ`-linear. | P0 / 4-STATES | planned correction C-007 |
| `FER03-R-BASIS-ENCODING` | L395–405, Eq. 20–21 | Real basis vectors acquire top coordinate 0 or 1. | P0 / 4-STATES | planned |
| `FER03-R-LOCAL-GATE-COST` | L407 | Constant-arity exact entry conversion is constant cost under a fixed encoding. | P2 / 8-RESOURCES | planned conditional result |
| `FER03-R-NONFACTORING-OUTPUT` | Fig. 3, L409–411, L561 | Non-real examples yield non-product encoded states. | P1 / 4-STATES, 10-RELEASE | planned example |
| `FER03-R-REAL-GATE-PADDING` | L413–430, Eq. 22, Fig. 4 | Place each image gate on the source support plus shared top wire. | P0 / 5-CIRCUITS | planned generalization |
| `FER03-R-ANCILLA-REUSE` | L432–436, Fig. 5 | All translated gates reuse one top wire; abstract gate count remains `s`. | P0 / 6-SIMULATION | planned |
| `FER03-R-SWAP-REALIFICATION` | L462–478 | Realification commutes with central permutation/padding operations. | P0 / 5-CIRCUITS | planned |
| `FER03-R-PARTIAL-TRACE-BLOCK-SUM` | L579–598, Eq. 30 | Tracing a two-level top subsystem sums diagonal blocks. | P0 / 4-STATES | planned if density formulation retained |
| `FER03-R-ARBITRARY-TOP-REBIT` | L661 | Any normalized pure or mixed product top rebit yields the same bottom basis statistics. | P1 / 4-STATES | planned |
| `FER03-R-REAL-GATE-OPTIMIZATION` | L667 | A real source gate maps to identity on top coordinate times the gate. | P1 / `Matrix/Realification.lean`, 6-SIMULATION | **partially formalized**: `realify_map_ofReal` proves the exact doubled block-diagonal matrix; its local-wire circuit consequence remains Stage 6 |
| `FER03-R-SERIAL-DEPTH` | L669 | Shared-top construction has target depth at most gate count and can lose parallelism. | P1 / 8-RESOURCES | planned construction bound |
| `FER03-R-MULTI-ANCILLA-LOG-DEPTH` | L671 | Several top wires allegedly give `O(log s)` depth increase. | P2 / 8-RESOURCES | unresolved pending construction, C-015 |
| `FER03-R-PREPROCESSING-COST` | L673 | Translation is linear time under fixed-arity/unit-cost exact gate encoding. | P1 / 8-RESOURCES | planned conditional result |
| `FER03-R-SUBSET-MEASUREMENTS` | L673 | All marginals of bottom computational-basis outcomes are preserved. | P1 / 4-STATES | planned |
| `FER03-R-COMPUTATIONAL-UNIVERSALITY` | L675–679 | Image of a quantum-universal family computationally simulates it with shared top rebit. | P1 / 8-RESOURCES | planned correction: not surjectivity onto all orthogonal gates |
| `FER03-R-PHASE-TRACKING-INTERPRETATION` | L681–687, FN7 | Top rebit records the real/imaginary relation; heuristic phase-kickback analogy. | P2 / 10-RELEASE | planned documentation/example only |

## Quaternion algebra, states, and ordering

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-Q-ALGEBRA` | L697–711, Eq. 34–35, FN8 | Reuse associative noncommutative division algebra and basis multiplication. | P0 / `Scalar/Quaternion.lean` | **proved as stated** via mathlib `Quaternion` plus public `i`, `j`, `k`, `i_mul_i`…`i_mul_j_mul_k` |
| `FER03-Q-CONJUGATE-NORM` | L713–729, Eq. 36–37 | Conjugation and norm-square coordinate formula. | P0 / mathlib + `Scalar/Quaternion.lean` | **proved as stated** via `Quaternion.normSq_def'`, `self_mul_star`, `star_mul_self`, and component norm theorem |
| `FER03-Q-CO-WD-DECOMP` | L731–753, Eq. 38–40 | Define `complexPart` and neutral-name `jPart` (paper “weird part”); reconstruct `q=z+w j`. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart`, `jPart`, `eq_complexPart_add_jPart_mul_j`, `components_injective` |
| `FER03-Q-CO-WD-MUL` | L755–769, Eq. 41 | Order-sensitive multiplication formulas. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart_mul`, `jPart_mul` |
| `FER03-Q-CO-WD-NORM` | L771–777, Eq. 42 | Quaternion norm square is sum of component complex norm squares. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `normSq_eq_complexPart_add_jPart` |
| `FER03-Q-CO-WD-CONJ` | L779–787, Eq. 43 | Components under quaternion conjugation. | P0 / `Scalar/Quaternion.lean` | **proved as stated**: `complexPart_star`, `jPart_star` |
| `FER03-Q-UNITARY-SP` | L816–820 | Generic quaternionic unitary matrices form the compact symplectic group. | P0 / `Matrix/Unitary.lean` | **corrected and proved** at the finite matrix/image level: quaternionic unitaries use generic `unitary (Matrix n n ℍ)` and `complexify_mem_symplectic` proves their complex images preserve `Matrix.J`; no quaternion determinant is assumed |
| `FER03-Q-KRONECKER-INTERCHANGE` | L822–830, Eq. 46 | Prove commutative case and correct entrywise-commutation sufficient condition; disprove “only if C,D are 0–1.” | P0 / 5-CIRCUITS, 7-ORDERING | planned correction C-009 |
| `FER03-Q-PARALLEL-ORDER-DEPENDENCE` | L831–839, Fig. 6 | Exhibit disjoint local gates/orderings with distinct operators and observable outcomes. | P0 / 7-ORDERING | planned correction C-018 |
| `FER03-Q-CUT-POSET` | L837 | Relate legal gate linear extensions to evaluation chains; do not identify one sort with a total order on all cuts. | P2 / 7-ORDERING | planned partial/correction |
| `FER03-Q-NUMBER-OF-PATHS` | L839 | Families can have many linear extensions; state any counting bound precisely. | P2 / 8-RESOURCES | planned partial |
| `FER03-Q-COMPLEXIFICATION-DEF` | L861–887, Eq. 47–48 | Define the explicit complex block embedding; tensor notation is mnemonic. | P0 / `Matrix/Complexification.lean` | **corrected and proved**: `complexify` is the explicit block matrix, with entrywise lower-block conjugation and four block-entry lemmas; malformed/formal tensor display excluded per C-011 |
| `FER03-Q-ADJOINT-COMPONENTS` | L931–940, Eq. 50 | Co/Wd identities for quaternionic conjugate transpose. | P0 / `Matrix/Complexification.lean` | **proved as stated**: `complexPartMatrix_conjTranspose`, `jPartMatrix_conjTranspose` |
| `FER03-Q-STATE-ENCODINGS` | L983–1005, Eq. 52–53 | Define `ĥ₀(q)=(Co q,-conj(Wd q))`, `ĥ₁(q)=(Wd q,conj(Co q))`. | P0 / 4-STATES | planned |
| `FER03-Q-ARBITRARY-TOP-QUBIT` | L1075 | Any normalized pure/mixed product top qubit preserves bottom basis statistics. | P1 / 4-STATES | planned |
| `FER03-Q-DIRECT-REALIFICATION` | L1208–1221, Eq. 63 | Verify direct `4×4` scalar representation and matrix/unitary consequences. | P1 / 9-COVERAGE | planned; determinant separate |

## Resource and universality claims

| ID | Source | Target / dependencies | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-RES-Q-WIDTH-DEPTH` | L1176–1180 | Abstract ordered simulation width `n+1`; shared top wire can serialize depth to `s`. | P1 / 8-RESOURCES | planned |
| `FER03-RES-ABSTRACT-GATE-COUNT` | L1180 | One `(d+1)`-ary image gate per `d`-ary source gate. | P0 / 6-SIMULATION | planned |
| `FER03-RES-GENERIC-DECOMPOSITION` | L1180–1184 | Generic target unitary elementary-gate synthesis bound. | P1 / 8-RESOURCES | unresolved/corrected target; source `O(2^d)` bound unsupported, C-013 |
| `FER03-RES-CONSTANT-D` | L1184 | With fixed `d` and a valid synthesis theorem, overhead is constant per gate. | P1 / 8-RESOURCES | planned conditional correction; `n`/`s` typo C-014 |
| `FER03-RES-QUATERNIONIC-UNIVERSAL-SET` | L1186 | Existence of finite quaternionic universal gate set. | P2 / 9-COVERAGE | **unresolved**: explicitly conjectural in paper |
| `FER03-RES-UNIFORM-CIRCUIT-WITHOUT-UNIVERSAL-SET` | L1186 | Alternative uniformly generated bounded-description gate interface. | P2 / 8-RESOURCES | planned documentation/interface only |
| `FER03-RES-EXPLICIT-MATRIX-ARITY` | L1188 | Full matrix descriptions of polynomial size imply `d=O(log n)`. | P1 / 8-RESOURCES | planned corrected encoding theorem |
| `FER03-RES-ARBITRARY-D-OVERHEAD` | L1188 | Polynomial overhead conclusion from logarithmic arity. | P1 / 8-RESOURCES | planned correction: `n^{O(1)}`, not necessarily `O(n)` |
| `FER03-RES-TABLE-1` | L1190–1198 | Width/size/depth summary after binary synthesis. | P1 / 8-RESOURCES | planned corrected table; current size/depth unsupported, C-013/C-014 |
| `FER03-RES-ABSTRACT-LITTLE-OVERHEAD` | Abstract L18–20, L1239 | Similar width/size and efficient simulation. | P1 / 8-RESOURCES | planned conditional wording, C-019 |

## Interpretation, converse, and physical claims

| ID | Source | Disposition target | Priority / stage | Status |
|---|---|---|---|---|
| `FER03-INT-QUATERNION-PHASE-QUBIT` | L1200–1204 | Document component-subspace intuition; do not claim a qubit literally stores all unit-quaternion degrees of freedom. | P2 / 10-RELEASE | planned partial documentation |
| `FER03-INT-NOT-NPLUS1-REBITS` | L1204 | Record only a limitation of the presented method; no lower bound follows. | P2 / 9-COVERAGE | **partially formalized** as correction C-017; no impossibility theorem |
| `FER03-INT-ORDER-DEPENDENCE-INTRINSIC` | L1223–1229, Fig. 7 | Prove algebraic explicit witness; separate “non-local time” interpretation. | P1 / 7-ORDERING | planned corrected theorem |
| `FER03-INT-FREE-NONLOCAL-CORRELATION` | L1231, FN10 | Distinguish gate-order dependence from entanglement/signaling. | P2 / 9-COVERAGE | planned documentation/counterexample analysis |
| `FER03-INT-BIT-COMMITMENT` | L1231 | Source supplies no hiding/binding definitions or security proof. | P3 / 9-COVERAGE | **unresolved**; intentionally no theorem without a protocol/security model |
| `FER03-INT-RULE-OUT-PHYSICALITY` | L1233, L1245–1249 | Philosophical/external information-theoretic interpretation. | P3 / 9-COVERAGE | **intentionally excluded** from Lean theorem surface |
| `FER03-INT-PREFERRED-PATH-BQP` | L1239–1241 | Conditional documentation after corrected uniform resource theorem. | P2 / 8-RESOURCES | planned partial |
| `FER03-INT-NONSURJECTIVE-CONVERSES` | L1251 | Prove exact image/properness facts with corrected target and low-dimensional exceptions; do not infer all operational lower bounds. | P1 / 9-COVERAGE | planned correction C-016 |
| `FER03-INT-DESTRUCTIVE-INTERFERENCE-CAUSE` | L1253–1257 | Conjectural explanation of quantum speedup. | P3 / 9-COVERAGE | **intentionally excluded** as a mathematical theorem |

## Explicit open questions

The paper asks, rather than proves, each item below.  They are retained for
source completeness and are **intentionally excluded** from the completion
requirements of this library unless a later stage proves a nearby finite result.

| ID | Source | Question |
|---|---|---|
| `FER03-OPEN-ALL-EVALUATION-PATHS` | L1243 | Can a model coherently follow all gate-evaluation paths? |
| `FER03-OPEN-PATH-WEIGHTS` | L1243 | Could paths carry probabilities or amplitudes? |
| `FER03-OPEN-PATH-INTERFERENCE` | L1243 | Could paths interfere constructively or destructively? |
| `FER03-OPEN-BEYOND-QUANTUM-SPEEDUP` | L1243 | Could path parallelism exceed quantum computational power? |
| `FER03-OPEN-QUATERBIT-TELEPORTATION` | L1251 | How many classical bits are needed to teleport a quaterbit? |
| `FER03-OPEN-CHANNEL-CAPACITY` | L1251 | How do quaternionic amplitudes affect channel capacities? |
| `FER03-OPEN-COMMUNICATION-COMPLEXITY` | L1251 | How does communication complexity change? |
| `FER03-OPEN-REBIT-INFORMATION-THEORY` | L1251 | What analogous distinctions occur for rebits? |
| `FER03-OPEN-OTHER-SCALARS` | L1253–1257 | What coherent models arise from octonions or finite fields? |
| `FER03-OPEN-ALGEBRAIC-COMPLEXITY-PICTURE` | L1257 | How much does amplitude structure affect complexity classes? |

## Figure, table, and footnote coverage

- Figure 1 maps to `FER03-R-SERIAL-COMPOSITION`.
- Figure 2 maps to `FER03-R-QUANTUM-GATE-PADDING`.
- Figure 3 maps to `FER03-R-NONFACTORING-OUTPUT`.
- Figure 4 maps to `FER03-R-REAL-GATE-PADDING`.
- Figure 5 maps to `FER03-R-ANCILLA-REUSE` and L03.
- Figure 6 maps to `FER03-Q-KRONECKER-INTERCHANGE` and
  `FER03-Q-PARALLEL-ORDER-DEPENDENCE`.
- Figure 7 maps to `FER03-INT-ORDER-DEPENDENCE-INTRINSIC`.
- Table 1 maps to `FER03-RES-TABLE-1`.
- Footnotes 1–10 are covered respectively by the finite-dimensional,
  antiunitary, routing, historical attribution, topological-sort, finite-
  precision, phase analogy, quaternion non-anticommutativity, nomenclature, and
  non-entanglement qualifications above.  Historical attributions and mere
  nomenclature are intentionally excluded from Lean declarations.

## Central dependency spine

```text
Co/Wd and re/im scalar identities
  → multiplicative, star-preserving matrix embeddings
    → unitary/orthogonal image results
      → state embeddings and basis-weight preservation
        → noncommutative-safe local gate placement
          → ordered circuit evaluation
            → corrected Theorems 2 and 4
              → Corollary 1, ordering witnesses, and defensible resource bounds
```
