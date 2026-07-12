# Axiom Audit

## Executable audit

The audit source is `QuaternionicComputing/AxiomAudit.lean` and imports only
the public root. It now runs 305 `#print axioms` commands (286 at the Stage 4B
checkpoint). The Stage 4C audit scope covers representative endpoints from
every public layer, including:

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
contain a separate `Empty` specialization. The 305-command public-root count
does not fold these diagnostic-only commands into it.

`State/RayAudit.lean` is likewise non-root. Four aggregate consumers cover all
40 stable Stage 4A declarations, while seven local axiom prints sample those
aggregates and the concrete rebit `-1`, qubit `I`, and quaterbit right-`j`
constructor equalities. The 305-command root count includes eight independent
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
bringing the executable root total to 305 commands; the public root does not
import the diagnostic leaf.

## Release result

The Stage 4C release audit completed successfully under Lean 4.31.0 and
mathlib v4.31.0. Every one of the 305 public-root endpoints and all 12 local
Stage 4C diagnostic endpoints depended on a subset of exactly:

- `propext` — propositional extensionality;
- `Classical.choice` — mathlib's classical constructions on finite types; and
- `Quot.sound` — quotient equality used by standard library/mathlib APIs.

No project-specific axiom appears.  Lean-source scans also find no `sorry`,
`admit`, `sorryAx`, declaration-level `axiom` or `opaque`, or `unsafe`
declaration in `QuaternionicComputing/`.

Warning-as-error compilation and a parser over every emitted axiom block
reproduced exactly this three-item union. No additional axiom was inferred
from a focused build alone.

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
