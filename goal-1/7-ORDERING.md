# 7-ORDERING

## Current Facts

- `OrderedCircuit` already represents a fixed chronological gate list and
  evaluates it as the reverse product; fixed-value quaternionic checks certify
  this orientation.
- Stage 6 proves both simulations for every such fixed order.  A legal-schedule
  layer should therefore produce an `OrderedCircuit`, not replace or redefine
  its semantics.
- The paper's Equation (46) is false over general quaternion entries.  Stage 5
  proves only the special right-identity law needed for contextual placement.
  The general sufficient condition is entrywise commutation between the second
  factor of the left Kronecker matrix and the first factor of the right one.
- The paper's phrase “only if `C,D` are 0–1 matrices” is false: central or
  otherwise mutually commuting entries also work.  Both a positive theorem
  and explicit positive/negative examples are required.
- The Stage 5 `i`/`j` order check uses scalar zero-wire gates and distinguishes
  evaluation order, but it is not yet the paper's stronger disjoint-support
  witness with different observable statistics.
- A computational-basis input to two monomial disjoint gates changes only
  quaternion phase and cannot witness different basis probabilities.  A valid
  witness needs mixing and interference; rational unitary `2×2` matrices with
  `3/5,4/5` and `i` versus `j` entries avoid square-root proof overhead.
- Repository-root `BUILD-PLAN.md` remains authoritative for narrow module
  ownership, focused/adjacent builds, boundary scans, and fold-back.

## Updated Assumptions

- A generic `LegalSchedule` over a finite gate identifier type can record a
  permutation of all identifiers and preservation of a precedence relation.
  Mapping its order through a gate family gives the existing circuit semantics.
- It is unnecessary to implement a topological-sorting algorithm to formalize
  Definition 4; existence/complexity belongs to Stage 8.  The schedule object
  should nevertheless make completeness, no duplication, and precedence
  preservation machine checked.
- A broad and reusable order-independence theorem can state that permutation of
  a chronological list preserves evaluation when the relevant global
  denotations are pairwise commuting.  Entrywise Kronecker results give a
  separate sufficient condition for disjoint tensor factors.
- Definition 5's classical Turing-machine generator/postprocessor cannot be
  fully formalized without an encoding model.  Stage 7 should formalize its
  finite scheduled-circuit semantic core and leave uniformity/runtime explicit
  for Stage 8.

## Big Picture Objective

Formalize the corrected noncommutative ordering story: exact Kronecker
interchange hypotheses and counterexamples, fixed legal schedules feeding the
public evaluator/simulations, useful order-independence criteria, and an actual
two-wire disjoint-gate example whose order changes a computational-basis
outcome probability.

## Detailed Implementation Plan

- Add a narrow matrix leaf defining entrywise commutation for compatible
  Kronecker factors.  Prove the corrected interchange identity over a general
  semiring, recover the commutative case, and give quaternionic `1×1` success
  and failure examples refuting the paper's 0–1 “only if.”
- Add a generic schedule leaf with finite gate identifiers, a precedence
  relation, a chronological list containing every identifier exactly once,
  and a proof that precedence is respected.  Define scheduled circuit and
  scheduled evaluation through `OrderedCircuit.eval`.
- Prove length/count and permutation facts.  Show two schedules enumerate the
  same gate multiset; if the gate denotations commute pairwise, scheduled
  evaluation is independent of the schedule.
- Connect each scheduled quaternionic circuit directly to
  `quaternionToComplex_exactSimulation`; do not duplicate the Stage 6 proof.
- Add a diagnostic/public witness leaf on two disjoint global wires.  Define
  rational quaternionic unitary local gates based on `i` and `j`, place them on
  separate supports, prove local unitarity and support disjointness, and compare
  the two chronological orders.
- Use an explicitly normalized input with two nonzero basis amplitudes and
  prove one named output basis weight has two distinct exact rational values.
  Also prove the operators differ.  Do not infer that every input or observable
  distinguishes the orders.
- Add useful independence corollaries for globally commuting gates and, where
  cleanly derivable, central/real or entrywise-commuting disjoint tensor
  factors.
- Update root imports/audit, traceability, C-009/C-018/C-023, conventions,
  architecture, and README after leaves stabilize.

## Build Structure

- `Matrix/KroneckerCommute.lean`: public algebra/proof leaf importing only the
  Kronecker and quaternion scalar surfaces needed for generic theorem plus
  narrow counterexamples; no circuit/simulation imports.
- `Circuit/Ordering.lean`: low-dependency public schedule/evaluation leaf
  importing `Circuit/Basic` and list permutation/big-operator lemmas; no scalar
  embedding or simulation imports.
- `Simulation/Scheduled.lean`: thin proof/API bridge importing
  `Circuit/Ordering` and `QuaternionToComplex`; connects any fixed legal
  schedule to Stage 6 without changing either layer.
- `Circuit/OrderingWitness.lean`: narrow quaternion-specific diagnostic/public
  example importing `Circuit/Ordering` and scalar/state basics as needed; heavy
  rational evaluation proofs stay out of the generic schedule core.
- `Simulation/OrderingWitness.lean`: narrow end-to-end consumer importing the
  witness and scheduled bridge; it proves that complexification preserves the
  exact operator and observable separation for the supplied schedules.
- `QuaternionicComputing.lean` and `AxiomAudit.lean`: changed only after all
  ordering leaves and adjacent scheduled-simulation consumers compile; root
  change requires full build.

## Boundary Checks

- The corrected Kronecker theorem must expose the exact entrywise commutation
  direction.  It may not assume a `CommSemiring` and then be advertised as the
  quaternionic result.
- Do not use `Matrix.mul_kronecker_mul` inside the generic/noncommutative proof;
  it may appear only in a separately labeled commutative corollary if needed.
- “0–1” is neither necessary nor a characterization.  The formal API must not
  preserve the paper's false “only if” wording.
- A legal schedule must contain every gate identifier once and respect the
  stated precedence relation.  An arbitrary list with attached prose is not a
  legal order.
- Scheduled evaluation must call the public chronological evaluator; it cannot
  define order-independent semantics or choose a privileged sort internally.
- The Stage 6 simulation bridge must take the schedule as input and translate
  that exact ordered circuit.  It cannot quantify away the order ambiguity.
- The order-dependent witness must use two provably disjoint supports and
  locally unitary gates, and must prove unequal basis weights for one explicit
  normalized input.  Operator inequality alone is insufficient.
- Do not generalize the witness to universal order dependence.  Independence
  theorems and non-distinguishing inputs/observables remain compatible with it.
- Classical generator encodings, topological-sort runtime, counts of linear
  extensions, bit-commitment security, and physical causality claims are not
  consequences of the finite schedule semantics.

## Completion Requirements

- Corrected Kronecker interchange theorem, commutative/central success, and
  explicit quaternionic failure compile with no false necessity claim.
- Legal schedules have completeness, uniqueness, precedence, and gate-count
  facts and evaluate through the existing ordered core.
- Pairwise commuting denotations give schedule-independent evaluation under an
  explicit theorem.
- Every fixed legal quaternionic schedule is connected to the Stage 6 exact
  simulation theorem.
- A two-disjoint-wire, locally unitary quaternionic example has two legal
  orders with distinct operators and a proved unequal computational-basis
  probability for one normalized input.
- Definitions 4 and the finite semantic core of 5 have explicit counterparts;
  excluded uniform TM content is documented rather than silently claimed.
- Focused leaves, adjacent consumers, root, full build, strict warnings,
  downstream smoke, audit, boundary scans, and `git diff --check` pass and are
  recorded below.

## Stage Results

- Completed on 2026-07-09.
- `Matrix/KroneckerCommute.lean` now exports
  `EntrywiseCommute` and
  `kronecker_mul_kronecker_of_entrywiseCommute` over an arbitrary semiring,
  with the exact crossing direction `B` against `C`.  It also proves the
  commutative specialization, zero-one sufficiency on either side, and
  commutation of canonical disjoint tensor factors under the corresponding
  entrywise hypothesis.
- `Matrix.QuaternionExamples.oneByOne_interchange_without_zeroOne` is a
  checked non-zero-one success example, while
  `oneByOne_interchange_i_j_failure` evaluates the failed interchange to the
  quaternionic `i`/`j` sign conflict.  Thus the paper's “only if” wording is
  disproved rather than retained as an API promise.
- `Circuit/Ordering.lean` defines `LegalSchedule`: a complete, duplicate-free
  chronological enumeration with an explicit precedence-index certificate.
  It proves full length, permutation, membership, count, and precedence facts;
  `scheduledCircuit` feeds the list directly to `OrderedCircuit`, and
  `scheduledEval_eq_of_pairwise_commute` proves independence only under an
  explicit pairwise-commutation premise on the global denotations.
- `Simulation/Scheduled.lean` applies the established Stage 6 theorem to the
  exact supplied schedule.  `scheduledQuaternionToComplex_exactSimulation`
  exposes operator embedding, unchanged occurrence count, width `+1`, arity
  bound `+1`, and normalized bottom-probability equality without choosing or
  quotienting schedules.
- `Circuit/OrderingWitness.lean` constructs two rational one-wire quaternionic
  mixers with off-diagonal `i` and `j` directions.  The placed gates have
  supports exactly `{false}` and `{true}`, are locally unitary with local arity
  one, and admit the two opposite legal schedules for the empty precedence
  relation.  The normalized input has amplitudes `3/5` at `00` and `(4/5)k` at
  `11`.  The two chronological output amplitudes at `00` are exactly `91/125`
  and `-37/125`, so their weights are `8281/15625` and `1369/15625`.
  `scheduled_operators_ne` and `output_basis00_weight_ne` record the operator
  and observable distinctions separately.
- `Simulation/OrderingWitness.lean` initializes the added complex wire in the
  normalized state `|0⟩`, translates both exact schedules, and proves both the
  retained operator inequality and the same two exact bottom weights through
  `complexifyCircuitOutput_bottomProbability`.
- An independent review unfolded the supports to `{false}` and `{true}`, the
  chronological matrices to `jGate.denote * iGate.denote` versus
  `iGate.denote * jGate.denote`, and the scalar calculation to
  `(3/5)^3 + (4/5)^3` versus `(3/5)^3 - (4/5)^3`.  It separately checked input
  normalization, schedule certificates, complexification injectivity, and the
  normalized probability bridge and found no defect.
- Strict direct compilation with `-DwarningAsError=true` passed for every new
  leaf and for the public root.  The combined focused build
  `lake build QuaternionicComputing.Matrix.KroneckerCommute
  QuaternionicComputing.Circuit.Ordering
  QuaternionicComputing.Circuit.OrderingWitness
  QuaternionicComputing.Simulation.Scheduled
  QuaternionicComputing.Simulation.OrderingWitness` completed 2,358 jobs.
- After the public-root import change, `lake build QuaternionicComputing`
  completed 2,519 jobs and the full `lake build` completed 2,519 jobs.
  `/tmp/Stage7ImportSmoke.lean`, importing only `QuaternionicComputing`,
  successfully checked the corrected Kronecker theorem, legal schedules,
  schedule independence, scheduled exact simulation, disjointness, and both
  source/translated observable inequalities.
- The expanded strict `AxiomAudit.lean` passed.  Every audited Stage 7 result
  reports only the established Lean/mathlib foundations `propext`,
  `Classical.choice`, and `Quot.sound` (with some results using a subset).
  Lean-only scans found no `sorry`, `admit`, `sorryAx`, project `axiom`,
  `opaque`, or `unsafe`; the forbidden
  `Matrix.mul_kronecker_mul` shortcut has no hit in the noncommutative leaf;
  schedule/witness boundary scans and `git diff --check` passed.
- Definition 4 now has a corrected finite formal counterpart.  Definition 5
  is formalized only through its fixed finite schedule/evaluation/simulation
  core; a uniform classical generator, description encoding, runtime, and
  postprocessing cost remain explicitly assigned to Stage 8.
