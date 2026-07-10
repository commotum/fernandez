# Goal 1 Continuation Prompt

```text
Work autonomously through goal-1/0-plan.md using the execution protocol in
goal-1/0-loop.md.

The objective is to independently reconstruct the important mathematics of
Fernandez and Schneeberger's “Quaternionic Computing” as a reusable Lean 4 and
mathlib library. Prove the central real and quaternionic circuit simulation
results; verify every claim used; identify, repair, and document errors; and
give every important paper claim a traceable final disposition.

Never use sorry, admit, sorryAx, unjustified project axioms, vacuous hypotheses,
or definitions engineered to make the result tautological. Keep dimensions,
scalar sides, noncommutative multiplication order, adjoints, normalization,
gate placement, and the distinction between state/operator equality and
observable equality explicit. Do not silently weaken or change a source claim.

At each iteration, inspect actual files and tests; update current facts; choose
the first incomplete stage; create or refresh only its stage file; implement and
verify that stage; record commands and evidence; update traceability and
corrections; fold results into the plan; and continue. Convert blockers into
experiments, smaller obligations, alternate representations, counterexamples,
or explicit unresolved work.

Completion means the original objective is actually achieved: the pinned
project builds without placeholders, main exports pass an explained axiom
audit, documentation supports downstream reuse, and all open issues are carried
forward explicitly rather than hidden.
```

