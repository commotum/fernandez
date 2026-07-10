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

- In progress.  Stage opened after verified completion of 6-SIMULATION on
  2026-07-09.
