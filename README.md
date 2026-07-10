# Quaternionic Computing — Lean 4 formalization

This repository is reconstructing and independently verifying José M.
Fernandez and William A. Schneeberger's paper *Quaternionic Computing*
(`quant-ph/0307017v2`) as a reusable Lean library.

The source extraction is in `Fernandez/fernandez-2003.md`.  The staged goal and
execution protocol are in `goal-1/0-plan.md` and `goal-1/0-loop.md`.

The project is pinned to Lean 4.31.0 and mathlib v4.31.0.  Once dependencies are
available, build it with:

```sh
lake build
```

The public import is:

```lean
import QuaternionicComputing
```

Traceability, mathematical conventions, corrections, and downstream usage will
be expanded alongside the formalization.  No completed module may contain
`sorry`, `admit`, or an unexplained project-specific axiom.
