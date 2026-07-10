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
import QuaternionicComputing.State.Basic
import QuaternionicComputing.State.Realification
import QuaternionicComputing.State.Complexification
import QuaternionicComputing.State.Unitary
import QuaternionicComputing.Circuit.Placement
import QuaternionicComputing.Circuit.AddedWire
import QuaternionicComputing.Circuit.Basic
import QuaternionicComputing.Circuit.Realification
import QuaternionicComputing.Circuit.Complexification
import QuaternionicComputing.Circuit.Cost
import QuaternionicComputing.Simulation.ComplexToReal
import QuaternionicComputing.Simulation.QuaternionToComplex
import QuaternionicComputing.Simulation.QuaternionToReal
```

The matrix layer currently exports dimension-safe, injective, multiplicative,
adjoint-preserving embeddings on sum indices.  Complex unitaries realify to
special orthogonal matrices.  Quaternionic unitaries complexify injectively to
complex unitary and symplectic matrices; the available formal proof narrows
their determinant to `1` or `-1`, while selecting the positive sign remains a
documented paper-proof obligation that is not needed by the simulation.

The state layer supplies explicitly normalized finite real, complex, and
quaternionic states, repairs quaternionic phase to act on the right, proves
both representation-column evolution identities, and proves pointwise bottom
computational-basis weight preservation for every normalized pure top
rebit/qubit.

The circuit layer supplies locality-certified gates on arbitrary finite wire
types, noncommutative-safe placement on arbitrary injected supports, explicit
chronological evaluation, unitarity preservation, and a concrete quaternionic
order check.  One-gate realification and complexification reuse one shared
distinguished top wire, commute with actual contextual placement, preserve
local unitarity, and increase local arity by exactly one.

The simulation layer proves corrected constructive forms of the paper's
Theorems 2 and 4 for arbitrary ordered finite circuits.  It separately exports
whole-operator embedding, all canonical and arbitrary-pure-top state evolution
laws, and equality of normalized bottom computational-basis probabilities.
Abstract gate count is unchanged, width grows by exactly one, and every local
gate grows by exactly one wire; maximum-arity theorems handle the empty circuit
explicitly.  Composing the two translations proves the corrected
quaternion-to-real corollary with two added wires and exact `+2` arity.

See `docs/Traceability.md`, `docs/Corrections.md`,
`docs/Conventions.md`, and `docs/Architecture.md` for exact source mappings and
mathematical conventions.  No completed module may contain `sorry`, `admit`,
or an unexplained project-specific axiom.
