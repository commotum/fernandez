# Axiom Audit

## Executable audit

The audit source is `QuaternionicComputing/AxiomAudit.lean` and imports only
the public root. It now runs 557 `#print axioms` commands (542 at Stage 11, 536
at Stage 10, 494 at Stage 9C, 458 at Stage 9B, 442 at Stage 9A, 422 at Stage 8,
393 at Stage 7, 354 at Stage 6, 330 at Stage 5, and 305 at Stage 4C).
Representative endpoint categories include:

- quaternion scalar decomposition and phase correction;
- both primary matrix embeddings, Equation 63 direct realification, group
  images, determinants, and explicit nonimage witnesses;
- normalized states, phase equivalence, state embeddings, and measurements;
- exact operator/circuit equality and the distinct fixed-input, basis-input,
  pure-input, distribution, event, and deterministic-pushforward relations;
- normalized exact-state equality plus real-sign, complex-unit-phase, and
  quaternionic right-phase equivalence, distribution, circuit, and unitary
  evolution endpoints;
- normalized `RealRay`, `ComplexRay`, and `QuaternionRay` quotient equality,
  representative lifting/elimination, the real equality-or-negation theorem,
  and exact nonempty/empty index boundaries;
- descended real/complex/quaternionic ray distributions, basis and finite-event
  weights, deterministic pushforwards, unitary evolution, locally-unitary
  circuit evolution, exact identity/composition laws, and representative-phase
  iff quotient-equality bridges;
- complex-to-real sector action and normalized orbit equivalence, descended
  bottom marginal distribution, canonical-column and normalized `Rebit`
  coefficient orbit consumers, the exact `±1` ordinary-real-ray boundary, and
  empty/nonempty no-lift classification;
- real/complex global operator phase, input-column phase, output-row phase,
  projective action, evaluator-backed circuit relations, and their sided
  composition and measurement implications, including the arbitrary-
  rectangular global projective kernel at zero, empty, and rank-one boundaries;
- quaternionic central sign, input-right phase, output-left phase, raw and
  normalized projective action, evaluator-backed circuit relations, the
  dimension-at-least-two central kernel, and the full-unit-quaternion rank-one
  exception;
- gate placement, chronological circuits, schedules, ordering witnesses, and
  basis preparation;
- certified basis-permutation implementations, certified unitary
  operator/circuit bundles, certified-only same-basis behavior, scalar-sided
  phase/measurement equivalences, and the all-input XOR consumer;
- finite real/complex density matrices, pure and basis constructors, the exact
  empty-index obstruction, unitary conjugation and chronological composition,
  genuine Loewner effects, Born bounds and basis formulas, and separation by
  all physical effects;
- bundled real/complex-style unitary operators, complete channel equality,
  equality under every genuine physical effect, raw/normalized projective
  kernels, global sign/phase characterizations, empty-index boundaries, and
  evaluator-backed locally-unitary circuit channels;
- the all-three-scalar output-row-phase/all-pure-input characterizations,
  finite-distribution event and deterministic-pushforward characterizations,
  state-ray covering arrows, real/complex channel/all-effect consequences,
  and their evaluator-backed circuit lifts;
- directional exact/lossless state encodings, mapped operators, state
  intertwining, decoded weight/distribution agreements, explicit top-sector
  policies, and the canonical raw `LinearEquiv` and normalized representative
  `Equiv` endpoints;
- proof-bearing rectangular, reindexed, placed-gate, primary, scheduled,
  composed, and conditional-compiler simulation wrappers;
- explicit full-target one- and two-added-wire outcome decoders, their exact
  `tailBits` pushforward characterization, and decoded raw-weight,
  distribution, event, and deterministic-pushforward simulation wrappers;
- exact fixed-order and scheduled simulations;
- count, arity, depth, dense-description, conditional compilation, finite
  distribution, event, and deterministic postprocessing results; and
- the non-product and product-input diagnostics.
- the six stable final-classification wrappers for normalized left-phase
  rejection, canonical reduced outer agreement, distribution/ray separation,
  commuting schedules, the bounded ordering witness, and supplied exact
  compilation.

Run it from the repository root with:

```sh
lake build QuaternionicComputing.AxiomAudit
```

For a fresh warning-as-error source check, use:

```sh
lake env lean -DwarningAsError=true QuaternionicComputing/AxiomAudit.lean
```

`Semantics/OperatorPhase/QuaternionAudit.lean` is deliberately not imported by
the public root. Its 11 aggregate consumer theorems exercise all 101
declarations in the three public quaternionic operator-phase leaves. Eight
local axiom prints sample five of those aggregates plus the three side-order
and central-sign diagnostics; they include the generic raw/normalized bridge,
the dimension-two kernel, and the rank-one exception. The generic bridge proof
itself covers the empty-input zero-column case; this diagnostic leaf does not
contain a separate `Empty` specialization. The 330-command public-root count
does not fold these diagnostic-only commands into it.

`State/RayAudit.lean` is likewise non-root. Four aggregate consumers cover all
40 stable Stage 4A declarations, while seven local axiom prints sample those
aggregates and the concrete rebit `-1`, qubit `I`, and quaterbit right-`j`
constructor equalities. The 330-command root count includes eight independent
public-ray endpoints but excludes these diagnostic-only prints.

`State/RayDescentAudit.lean` is the non-root Stage 4B consumer. Its aggregate
theorems exercise the scalar-neutral pushforward and local-unitarity helpers,
all real/complex/quaternionic observable and evolution operations, the three
semantic bridges, representative computation, matrix and chronological
composition order, proof-argument irrelevance, and the inhabited zero-wire
circuit boundary. Its local axiom prints are diagnostic-only. The public-root
count instead includes 14 independent Stage 4B endpoints.

Stage 4C adds 84 stable declarations split `66 + 10 + 8` across
`State/RealificationOrbit.lean`, `RealificationOrbitObservables.lean`, and
`RealificationOrbitBoundary.lean`. The core relation is proved independently,
the observable leaf descends only the bottom marginal, and the boundary leaf
proves the exact ordinary-`RealRay` obstruction. The non-root
`State/RealificationOrbitAudit.lean` has five aggregate consumers allocating
the complete surface as `28 + 13 + 25 + 10 + 8 = 84` declarations. Its 12
local prints cover those aggregates and seven concrete boundary/consumer
examples. The public-root audit instead adds 19 independent Stage 4C endpoints,
bringing the Stage 4C executable root total to 305 commands; the public root
does not import the diagnostic leaf.

Stage 5 adds 134 stable declarations split `90 + 44` across
`Semantics/BasisBehavior.lean` and `BasisBehaviorCircuit.lean`. The non-root
`Semantics/BasisBehaviorAudit.lean` has 14 exact-allocation aggregate
consumers: ten cover the 90 core declarations with allocation
`10/6/6/12/1/6/27/5/8/9`, and four cover the 44 circuit declarations with
allocation `12/18/3/11`. Its 30 explicit diagnostic declarations also include
empty-index, nonidentity-permutation, and zero-wire checks. Eighteen local
`#print axioms` endpoints cover the 14 aggregates plus those three boundary
consumers and `unitary_vacuity_witness`.

The vacuity endpoint proves that two everywhere-nonzero rational real unitary
rotations have no `BasisTransition` at any input/output pair and admit no
`BasisPermutationImplementation`. Their empty raw transition relations are
equal, but their `false → false` basis weights are respectively `9/25` and
`25/169`. This is an audit of the strict boundary between diagnostic raw
transitions and certified behavior, not an additional public relation. The
public root does not import `BasisBehaviorAudit.lean`.

The public-root audit adds 25 independent Stage 5 endpoints, bringing its
total to 330 commands. These root endpoints are separate from the 18 local
diagnostic prints.

Stage 6 adds 97 stable declarations split `40 + 52 + 5` across
`Semantics/Density.lean`, `Effect.lean`, and `EffectSeparation.lean`. The
non-root `Semantics/DensityAudit.lean` has eight exact-allocation aggregate
consumers: three allocate all 40 density declarations as `33 + 1 + 6`, four
allocate all 52 effect declarations as `17 + 11 + 20 + 4`, and one consumes
all five separation declarations. Generated structure projections and the two
anonymous coercion instances are excluded consistently from the named-export
count, while their coercions are exercised by the aggregate statements.

Concrete diagnostic consumers cover real and complex pure/basis
compatibility, the genuinely mixed real density `(1/2) I`, Born bounds and
complementation, chronological unitary conjugation, separation by a genuine
basis effect, and impossibility of a density on `Empty`. Seven local
`#print axioms` commands sample four complete aggregates plus mixedness,
complex separation, and the empty-index obstruction. The public root imports
only the three stable leaves, never `DensityAudit.lean`.

The root audit adds 24 independent Stage 6 endpoints, bringing its total to
354 commands. They include the empty/nonempty boundary, pure/basis entries,
unitary conjugation and `V * U` composition, projector bounds, Born reality and
`[0,1]` membership, and both directions of genuine physical-effect
separation. These endpoints do not audit a channel relation because Stage 6
does not define one.

Stage 7 adds 139 stable declarations split `41 + 40 + 58` across
`Semantics/Channel.lean`, `ChannelPhase.lean`, and `ChannelCircuit.lean`.
The non-root `Semantics/ChannelAudit.lean` has 23 exact-allocation aggregate
consumers. The core allocation is `20 + 11 + 10 = 41`; the phase allocation is
`2 + 7 + 7 + 6 + 2 + 2 + 6 + 6 + 2 = 40`; and the circuit allocation is
`2 + 19 + 2 + 10 + 10 + 1 + 2 + 2 + 2 + 4 + 4 = 58`. Generated structure
projections and the two anonymous coercion instances are excluded consistently
from the named count while the aggregate statements exercise both coercions.

The concrete audit distinguishes identity from a real swap using a genuine
basis effect, checks real `-1` and complex `I` global phases, verifies
chronological `V * U` and `eval D * eval C` order, separates the empty-matrix
boundary from vacuous empty-density channel quantification, and checks the
inhabited zero-wire circuit basis. It remains outside the public root and
contains 11 representative local axiom commands that are separate from the
root count. Strict compilation and the emitted local audit reproduce exactly
the standard three-item union below.

The root audit adds 39 independent Stage 7 endpoints, bringing its total to
393 commands. They cover complete-output/all-effect equivalence, raw and
normalized phase bridges, inhabited real/complex global and projective
characterizations, exact empty-index matrix facts, circuit exact/global lifts,
and chronological append. No quaternionic or cross-model channel endpoint is
present.

Stage 8 adds 49 stable declarations split `9 + 13 + 27` across
`Semantics/Hierarchy/OutputPhase.lean`, `Hierarchy/State.lean`, and
`Hierarchy/Operator.lean`. The non-root
`Semantics/HierarchyAudit.lean` has 12 exact-allocation aggregates covering all
49 declarations. Its concrete diagnostics include arbitrary rectangular and
empty matrix boundaries, genuine singleton distributions, real/complex
channel strictness, equal-distribution/not-ray witnesses, the exact
one-input quaternionic ordering scope, the rank-one kernel exception, and all
certified-classical equivalences under their supplied certificates.

The hierarchy audit contains 33 local `#print axioms` endpoints. The public
root does not import it. Instead, the root audit adds 29 independent Stage 8
endpoints, bringing its total to 422 commands. Focused builds completed 2,355,
2,356, 2,693, and 2,713 jobs for the output-phase, state, operator, and audit
leaves respectively; the combined hierarchy-audit/public-root/axiom-audit
target completed 2,769 jobs. Every new endpoint emits a subset of the exact
standard three-item union below.

Stage 9A adds 58 stable declarations split `38 + 20` across
`Semantics/Simulation.lean` and `Semantics/SimulationEncoding.lean`. Eleven
manifest consumers allocate the complete surface: nine aggregates cover the
generic directional relations and two cover the concrete representative
encodings. The non-root `Semantics/SimulationAudit.lean` also checks the
complex-to-real and quaternion-to-complex concrete instances, explicit
normalized `Rebit`/`Qubit` coefficient parameters, empty and singleton
boundaries, ordinary-ray non-descent, and the non-product witness.

The simulation audit contains ten local `#print axioms` endpoints and is not
imported by the public root. The root audit instead adds 20 independent Stage
9A endpoints, bringing its total to 442 commands. Focused builds completed
2,345, 2,350, and 2,368 jobs for the relation, encoding, and audit leaves,
respectively; the combined public-root/axiom-audit target completed 2,766 jobs.
Every new endpoint emits a subset of the same exact standard union below.

Stage 9B adds 16 stable declarations in
`Semantics/SimulationWrappers.lean`. Six disjoint consumers in the existing
non-root `SimulationAudit.lean` allocate them as
`2 + 3 + 4 + 3 + 2 + 2`: matrix state action, reindexing/placement, primary
circuits, supplied schedules, composed circuits, and conditional compilation.
The consumers also check canonical raw coefficient pairs, rectangular and
empty input indices, the concrete unequal-schedule witness, local identity
compiler inhabitation, and zero-wire circuits.

The root audit adds all 16 wrappers directly, bringing its total to 458
commands. The local simulation audit adds six aggregate endpoints, bringing
its total to 16 commands. Focused builds completed 2,369 and 2,381 jobs for the
wrapper and extended audit leaves, and the combined stable/audit/public-root/
axiom-audit target completed 2,767 jobs. Every new endpoint emits a subset of
the same exact standard union below.

Stage 9C adds 36 stable declarations split `10 + 8 + 18` across
`Simulation/OutcomeDecoder.lean`, `Simulation/Postprocessing.lean`, and
`Semantics/SimulationOutcomes.lean`. The decoder leaf gives explicit full-
target one- and two-added-wire decoders and proves that one-wire decoding is
exactly deterministic pushforward by `tailBits`. The postprocessing additions
package the full-target realification, complexification, and composed
quaternion-to-real outcomes. In the composed decoder the outer realification
wire is removed first and the inner complexification wire second.

The 18 semantic wrappers are allocated exactly as `2 + 4 + 4 + 4 + 4`:
two representative raw pointwise wrappers, then four wrappers each for
complex-to-real, fixed-order quaternion-to-complex, supplied-schedule
quaternion-to-complex, and composed quaternion-to-real simulation. Raw point
wrappers need no local-unitarity hypothesis. Normalized distribution, event,
and deterministic-pushforward wrappers use the required local-unitarity
certificate; scheduled distribution-level wrappers use its pointwise form.
The schedule remains supplied data. These endpoints do not add product or
mixed-top semantics, partial traces, channels, randomized algorithms, resource
bounds, or a compiler/schedule construction.

The non-root simulation audit adds two infrastructure aggregates allocating
the decoder and postprocessing additions as `10 + 8`, and five semantic
aggregates allocating the 18 wrappers by the five groups above. Seven selected
prints replace three older selected diagnostics, a net increase of four that
brings the diagnostic leaf to 20 commands. The public-root audit
adds all 36 declarations directly, bringing its total to 494 commands. Focused
builds completed 2,347, 2,361, 2,365, and 2,385 jobs for the decoder,
postprocessing, semantic-wrapper, and extended-audit leaves, respectively; the
combined stable/audit/public-root/axiom-audit target completed 2,769 jobs.
Every new endpoint emits a subset of the same exact standard union below.

Stage 10 adds 169 stable declarations split
`24 + 23 + 48 + 43 + 17 + 14` across the real/complex operator, global-phase,
native quaternionic operator, state/ray, finite-distribution, and strictness
leaves. The non-root `Semantics/ApproximationAudit.lean` allocates the complete
surface through 24 aggregates with exact group sizes
`15/5/4/2/5/8/8/13/11/11/5/7/1/12/7/5/5/5/3/6/13/4/9/5`.
Concrete consumers check the inhabited zero-wire basis, a nontrivial unitary,
directional real-to-complex mapped zero closeness, quaternionic right-phase
side, normalized singleton output bounds, finite Boolean events/pushforwards,
and all strictness chains. The audit remains outside the public root.

The local approximation audit contains 16 selected `#print axioms` endpoints;
all 16 are nonempty and their union is exactly the standard three items below.
The root audit adds 42 selected Stage 10 commands, bringing its total from 494
to 536. Forty are literal fully qualified Stage 10 manifest intersections; two
long strictness targets were printed under an opened namespace at that
checkpoint. The root parser finds 533 nonempty and three
axiom-free blocks. Focused builds complete 2,345, 2,365, 2,372, 2,376, 2,378,
2,374, and 2,383 jobs for the distribution, operator, operator-phase,
quaternion, state, strictness, and approximation-audit leaves. Every selected
endpoint remains within the exact standard union below. The combined stable/
audit/public-root/release-audit target completes 2,775 jobs, and the cached
default build completes 2,773.

Stage 11 adds six stable declarations in
`Semantics/ExistingResults.lean`. The non-root
`Semantics/ExistingResultsAudit.lean` allocates those declarations through
three source-order aggregates and gives the remaining Stage 11-owned
diagnostic, algebraic, combinatorial, and resource families meaningful
nonbehavioral consumers. Its 15 selected `#print axioms` endpoints are all
nonempty. The public-root audit adds all six stable wrappers directly, bringing
its total from 536 to 542 commands. The root parser finds 539 nonempty and three
axiom-free blocks; the local parser finds 15 nonempty and no axiom-free block.
Both exact unions are the same standard three items below.
Stage 11 puts the two long Stage 10 strictness targets in their exact namespace
scope and corrects their manifest evidence from transitive to direct; the
selected endpoints and root command count do not change.

The combined Stage 11 stable/local-audit/public-root/release-audit build
completes 2,776 jobs. The separate final registry validator resolves all 936
frozen declaration names and all named proof, consumer, and audit targets; it
does not infer axiom cleanliness from metadata alone.

Stage 12 first added nine stable projective-to-input hierarchy arrows. The final
kernel repair adds six more stable arrows: raw, normalized, and evaluator-backed
projective action each determine one global sign or phase over real and complex
scalars. All 15 are selected directly in the root audit.
`ProjectiveInputAudit.lean` remains non-root and selects the complete nine-arrow
consumer, the complete six-arrow kernel consumer, and two quaternionic
strictness boundaries. The expanded root parser has 554 nonempty and three
axiom-free blocks; all four local projective-input blocks are nonempty. Each
exact union is the same standard three items below. The final post-kernel
default, integrated root/audit, and all-15-audit-module builds complete 2,776,
2,778, and 2,788 jobs respectively. The union of the public root, root audit,
and all 15 maintained audit modules completes 2,792 jobs.

The final integrated metadata audit replaced 792 obsolete `direct release
endpoint pending` descriptions with `direct release endpoint not selected`.
Those declarations were already covered by their named transitive consumers;
no root/local target or parser count changed.

## Current post-repair audit result

The expanded public-root audit uses Lean 4.31.0 and mathlib v4.31.0. Every one
of the 557 public-root endpoints, all 15 local existing-results endpoints, all
four local projective-input endpoints, all 16 local approximation endpoints,
all 20 local simulation endpoints, all 33 local Stage 8 endpoints, all 11 local
Stage 7 endpoints, all seven local Stage 6 endpoints, all 18 local Stage 5 endpoints,
and the retained local Stage 4C diagnostics individually depends on a subset
of the following exact three-item union:

- `propext` — propositional extensionality;
- `Classical.choice` — mathlib's classical constructions on finite types; and
- `Quot.sound` — quotient equality used by standard library/mathlib APIs.

No project-specific axiom appears.  Lean-source scans also find no `sorry`,
`admit`, `sorryAx`, declaration-level `axiom` or `opaque`, or `unsafe`
declaration in `QuaternionicComputing/`.

The exact parser over every emitted axiom block reproduces this three-item
union. No additional axiom is inferred from a focused build alone. The
expanded parser reads 554 nonempty and three
axiom-free root blocks. The local existing-results audit has
15 nonempty blocks and no axiom-free block; the local projective-input audit
has four nonempty blocks and no axiom-free block. The local approximation audit
has 16 nonempty blocks and no axiom-free block. The local simulation audit has 19
nonempty blocks and one axiom-free block; all 20 resolve without an unknown
identifier or `sorryAx` output.

The Stage 11 and final Stage 12 stable leaves, non-root audits, public root, and
axiom audit pass warning-as-error compilation. The executable release audit
passes; independent closure review remains. Finite scalar encoding, rounding,
accumulated circuit error,
approximate compiler construction, and runtime remain Goal 3 work rather than
missing Stage 10 axioms.

This result does not mean the developments are constructive or axiom-free in a
minimal-foundation sense.  It means the completed public results introduce no
unexplained assumption beyond the standard Lean/mathlib foundations listed
above.  The unresolved mathematical claims in `Traceability.md` are omitted or
weakened explicitly rather than encoded as axioms.

## Maintenance rule

When a new main theorem is promoted through `QuaternionicComputing.lean`, add a
corresponding `#print axioms` command to `AxiomAudit.lean`, rebuild the audit,
and update this report if a dependency outside the three-item release set
appears.
