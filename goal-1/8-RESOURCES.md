# 8-RESOURCES

## Current Facts

- Stage 6 already proves the exact representation-level costs that do not need
  an encoding model: unchanged gate count, width `+1` for each primary
  translation, exact local arity `+1` per gate, corresponding arity bounds and
  nonempty maximum equalities, and width/arity `+2` for the visible composite.
- Both primary circuit translations are literal `List.map`s.  This proves one
  image-gate occurrence per source occurrence, but by itself is not a runtime
  theorem about scalar encodings, allocation, matrix arithmetic, or target
  gate synthesis.
- Every image gate in the current uniform construction includes the same
  distinguished top wire in its certified local support.  In the conventional
  disjoint-support parallelism model, that structural fact forces the mapped
  circuit to serialize.  The project does not yet expose a typed layering/depth
  certificate that states this precisely.
- Stage 7 separates a fixed chronological order from precedence constraints.
  It does not implement topological sorting or charge for producing a legal
  schedule.  For the empty precedence relation, all permutations are legal;
  this gives a clean factorial path-count result without claiming that all
  circuits have that many linear extensions.
- The paper's full local matrix for a `d`-wire gate has `2^d × 2^d = 4^d`
  scalar-entry slots.  Its line-1182 `O(2^d)` generic decomposition-time claim
  is therefore not even an output-size consequence for a dense explicit
  matrix, and no synthesis algorithm or primitive gate library is supplied.
- The paper's `O(log s)` multi-ancilla depth claim supplies no construction,
  correctness theorem, ancilla count, fan-in convention, or gate set.  It
  cannot be inferred from the one-shared-wire simulation.
- The Stage 6 normalized pointwise probability theorems imply preservation of
  every finite event, marginal, and deterministic classical postprocessing,
  but the reusable pushforward-distribution result is not yet packaged.
- Definition 5's uniform classical TM generator, finite-precision gate
  descriptions, runtime, and oracle/postprocessor model are outside the current
  finite matrix API.  A semantic circuit-family wrapper without computability
  evidence would not prove those claims and is not useful completion evidence.
- Repository-root `BUILD-PLAN.md` remains authoritative for module ownership,
  focused/adjacent builds, boundary scans, and fold-back.

## Updated Assumptions

- A support-layering certificate should contain nonempty layers, pairwise
  disjoint gate supports within each layer, and an exact flattening to the
  chronological circuit.  It is a resource certificate only: flattening fixes
  semantics, and no noncommutative order-independence is inferred from support
  disjointness.
- A generic common-wire theorem should prove that every such layering has
  depth exactly equal to gate count.  Applying it to the literal image circuits
  will give the corrected serialization statement for both simulations.
- Dense description size can be modeled exactly by the number of scalar-entry
  slots.  Scalar bit length, sharing/compression, arithmetic work, and
  elementary-gate synthesis must remain explicit additional hypotheses.
- A generic additive list-cost theorem can justify the conditional statement
  “bounded work per gate gives work at most gate count times that bound.”  It
  must not be advertised as an unconditional `O(s)` theorem for arbitrary
  exact scalar descriptions.
- A finite pushforward-weight API is sufficient to prove preservation under
  deterministic classical postprocessing and subset/marginal events.  It does
  not formalize randomized Turing machines or their runtime.

## Big Picture Objective

State and prove the strongest resource conclusions justified by the actual
finite construction: exact syntactic size/width/arity and dense-entry costs,
serialization in an explicit support-depth model, factorially many schedules
in the unconstrained finite case, and preservation under arbitrary finite
deterministic postprocessing.  Isolate every missing encoding, synthesis,
uniformity, and asymptotic assumption instead of promoting algebraic exactness
to a complexity-class theorem.

## Detailed Implementation Plan

- Add a generic support-depth leaf.  Define nonempty pairwise-disjoint layers
  whose flattening is an `OrderedCircuit`; construct the singleton/serial
  layering; prove depth is at most gate count; and prove equality for every
  layering when all circuit gates use one common wire.
- In a simulation resource leaf, prove the distinguished top wire belongs to
  every realified and complexified gate support.  Instantiate the common-wire
  theorem to show every support layering of either primary image circuit has
  depth exactly the unchanged source gate count, and expose serial-layering
  witnesses.  State clearly that the optional real-gate optimization is not
  used by the uniform translator.
- Add a dense-description leaf defining per-gate and total scalar-entry slots.
  Prove `4^localArity`, exact factor `4` under a `+1` arity translation, exact
  factor `16` under `+2`, the logarithmic arity consequence of a finite slot
  bound, and a generic conditional additive-work bound.
- Connect dense-slot theorems to `realifyCircuit`, `complexifyCircuit`, and the
  composed translation.  Do not introduce or assume an elementary-gate
  decomposition theorem.
- Add a schedule-count leaf enumerating the permutations of all finite gate
  identifiers.  Prove the list has exactly `(Fintype.card ι)!` distinct orders
  and that each gives a `LegalSchedule` for the empty precedence relation.
- Add a reusable finite distribution/pushforward leaf and thin simulation
  corollaries.  Derive equality for arbitrary finite events and arbitrary
  deterministic maps of bottom computational-basis outcomes from the existing
  normalized pointwise probability equalities.
- Update the public root and axiom audit only after all leaves compile.  Update
  traceability/resource rows, corrections C-013/C-014/C-015/C-019/C-024,
  Definition 5's status, architecture, conventions, Mathlib API notes, and
  README with exact boundaries.
- Assign terminal non-proved dispositions, with precise obstructions, to the
  generic elementary decomposition bound, multi-ancilla logarithmic depth,
  finite quaternionic universal set, unconditional preprocessing runtime,
  approximation/finite-precision conversion, and BQP containment claims.

## Build Structure

- `Circuit/Depth.lean`: low-dependency public resource API importing
  `Circuit/Basic` plus narrow list lemmas; contains layering certificates and
  generic common-wire depth results, with no scalar embedding imports.
- `Circuit/DescriptionCost.lean`: low-dependency public proof leaf importing
  `Circuit/Cost` and natural-log/list-sum lemmas; owns dense slot counts and
  conditional additive work bounds, not runtime implementations.
- `Circuit/ScheduleCount.lean`: ordering-specific proof leaf importing
  `Circuit/Ordering` and list permutation APIs; owns factorial enumeration and
  stays out of the generic schedule core.
- `State/Distribution.lean`: scalar-independent finite probability/pushforward
  API importing only the normalized-state basics and finite sums.
- `Simulation/Resources.lean`: thin adjacent consumer importing both primary
  translations plus depth/description cost; owns shared-top serialization and
  exact translation slot factors.
- `Simulation/Postprocessing.lean`: thin observable consumer importing the
  primary output theorems plus `State/Distribution`; owns event and
  deterministic-postprocessing preservation.
- `QuaternionicComputing.lean` and `AxiomAudit.lean`: touched only after all
  leaves and adjacent consumers compile; the root change requires a full build.

## Boundary Checks

- Support layering is a cost certificate whose `flatten` fixes chronological
  semantics.  No theorem may infer quaternionic within-layer commutation from
  disjoint support; Stage 7's explicit commutation hypotheses remain required.
- “Depth equals gate count” applies to the literal shared-top translations and
  the stated disjoint-support depth model.  It is not a universal lower bound
  against alternative encodings or the paper's unconstructed multi-ancilla
  proposal.
- Scalar-entry slots are not bit complexity.  Exact factor theorems may not be
  described as runtime without separately stated per-entry encoding/work
  hypotheses.
- No use of a nonexistent or assumed generic unitary synthesis routine; no
  project axiom may encode the paper's `2^(d+1)` elementary-gate assertion.
- A factorial count is proved only for empty precedence.  General DAGs can have
  fewer legal orders, including one.
- Pushforward preservation is for finite deterministic postprocessing of the
  already normalized bottom distribution.  It does not prove TM uniformity,
  randomized postprocessing cost, approximation error, or a complexity-class
  containment.
- A pure function called a generator is not evidence of computability or
  polynomial runtime.  Uniformity claims remain non-proved unless backed by an
  explicit encoding and computational model.
- The paper's open finite quaternionic universal-set belief and physical/BQP
  interpretations must not become Lean theorem assumptions.

## Completion Requirements

- A reusable support-layering API and exact common-wire serialization theorem
  compile, with both primary translations instantiated.
- Dense scalar-entry slots are exact, their translation factors are proved,
  and any linear-work conclusion carries an explicit per-gate cost premise.
- Empty-precedence chronological orders are enumerated without duplicates and
  counted exactly by a factorial, with certified legal schedules.
- Event/marginal and deterministic finite postprocessing preservation are
  derived for both primary normalized simulations.
- Every important resource/uniformity claim has either a proved theorem in its
  explicit model or a terminal documented obstruction; no unsupported source
  asymptotic remains “planned.”
- Focused leaves, adjacent consumers, strict warnings, public root, full build,
  downstream smoke, axiom audit, proof-hole/shortcut scans, and
  `git diff --check` pass and are recorded below.

## Stage Results

- In progress.  Stage opened after verified completion of 7-ORDERING on
  2026-07-09.
