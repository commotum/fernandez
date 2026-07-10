# Quaternionic Computing — Lean 4 formalization

This repository is reconstructing and independently verifying José M.
Fernandez and William A. Schneeberger's paper *Quaternionic Computing*
(`quant-ph/0307017v2`) as a reusable Lean library.

The source extraction is in `Fernandez/fernandez-2003.md`.  The staged goal and
execution protocol are in `goal-1/0-plan.md` and `goal-1/0-loop.md`.
Lean-changing stages also follow the authoritative incremental workflow in
`BUILD-PLAN.md`.

The project is pinned to Lean 4.31.0 and mathlib v4.31.0.  Once dependencies are
available, build it with:

```sh
lake build
```

The public import is:

```lean
import QuaternionicComputing
```

Narrow consumers can instead import one of the current leaves:

```lean
import QuaternionicComputing.Scalar.Quaternion
import QuaternionicComputing.Matrix.Realification
import QuaternionicComputing.Matrix.Complexification
import QuaternionicComputing.Matrix.Unitary
import QuaternionicComputing.Matrix.Determinant
```

The matrix layer currently exports dimension-safe, injective, multiplicative,
adjoint-preserving embeddings on sum indices.  Complex unitaries realify to
special orthogonal matrices.  Quaternionic unitaries complexify injectively to
complex unitary and symplectic matrices; the available formal proof narrows
their determinant to `1` or `-1`, while selecting the positive sign remains a
documented paper-proof obligation that is not needed by the simulation.

See `docs/Traceability.md`, `docs/Corrections.md`,
`docs/Conventions.md`, and `docs/Architecture.md` for exact source mappings and
mathematical conventions.  No completed module may contain `sorry`, `admit`,
or an unexplained project-specific axiom.
