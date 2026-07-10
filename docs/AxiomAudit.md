# Axiom Audit

## Executable audit

The audit source is `QuaternionicComputing/AxiomAudit.lean`.  It imports only
the public root and runs 201 `#print axioms` commands covering representative
endpoints from every public layer:

- quaternion scalar decomposition and phase correction;
- both primary matrix embeddings, Equation 63 direct realification, group
  images, determinants, and explicit nonimage witnesses;
- normalized states, phase equivalence, state embeddings, and measurements;
- exact operator/circuit equality and the distinct fixed-input, basis-input,
  pure-input, distribution, event, and deterministic-pushforward relations;
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

## Release result

The release audit completed successfully under Lean 4.31.0 and mathlib
v4.31.0.  Every audited endpoint depends on a subset of only:

- `propext` — propositional extensionality;
- `Classical.choice` — mathlib's classical constructions on finite types; and
- `Quot.sound` — quotient equality used by standard library/mathlib APIs.

No project-specific axiom appears.  Lean-source scans also find no `sorry`,
`admit`, `sorryAx`, declaration-level `axiom` or `opaque`, or `unsafe`
declaration in `QuaternionicComputing/`.

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
