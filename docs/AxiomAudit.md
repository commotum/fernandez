# Axiom Audit

## Executable audit

The audit source is `QuaternionicComputing/AxiomAudit.lean` and imports only
the public root. It now runs 330 `#print axioms` commands (305 at the Stage 4C
checkpoint and 286 at the Stage 4B checkpoint). Representative endpoint
categories include:

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
  bottom marginal distribution, canonical-column and arbitrary-pure-top orbit
  consumers, the exact `±1` ordinary-real-ray boundary, and empty/nonempty
  no-lift classification;
- real/complex global operator phase, input-column phase, output-row phase,
  projective action, evaluator-backed circuit relations, and their sided
  composition and measurement implications;
- quaternionic central sign, input-right phase, output-left phase, raw and
  normalized projective action, evaluator-backed circuit relations, the
  dimension-at-least-two central kernel, and the full-unit-quaternion rank-one
  exception;
- gate placement, chronological circuits, schedules, ordering witnesses, and
  basis preparation;
- certified basis-permutation implementations, certified unitary
  operator/circuit bundles, certified-only same-basis behavior, scalar-sided
  phase/measurement equivalences, and the all-input XOR consumer;
- exact fixed-order and scheduled simulations;
- count, arity, depth, dense-description, conditional compilation, finite
  distribution, event, and deterministic postprocessing results; and
- the non-product and product-input diagnostics.

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
bringing the Stage 4C executable root total to 305 commands; the public root does not
import the diagnostic leaf.

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

## Release result

The Stage 5 release audit completed successfully under Lean 4.31.0 and
mathlib v4.31.0. Every one of the 330 public-root endpoints, all 18 local
Stage 5 diagnostic endpoints, and the retained local Stage 4C diagnostics
depended on a subset of exactly:

- `propext` — propositional extensionality;
- `Classical.choice` — mathlib's classical constructions on finite types; and
- `Quot.sound` — quotient equality used by standard library/mathlib APIs.

No project-specific axiom appears.  Lean-source scans also find no `sorry`,
`admit`, `sorryAx`, declaration-level `axiom` or `opaque`, or `unsafe`
declaration in `QuaternionicComputing/`.

Warning-as-error compilation and a parser over every emitted axiom block
reproduced exactly this three-item union. No additional axiom was inferred
from a focused build alone.

The completed Stage 5 core, circuit, and non-root diagnostic leaves also pass
warning-as-error compilation. All 18 local Stage 5 endpoints reproduce the
same exact three-item union and introduce no project-specific axiom.

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
