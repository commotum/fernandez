module

public import QuaternionicComputing.Circuit.Basic

/-!
# Closure laws for locally unitary ordered circuits

This narrow leaf records that appending two chronological circuits whose
stored local gates are all unitary again yields a locally unitary circuit.
It is independent of any scalar-specific state or ray semantics.
-/

@[expose] public noncomputable section

namespace QuaternionicComputing.Circuit.OrderedCircuit.IsLocallyUnitary

universe u v

variable {R : Type u} {W : Type v}
variable [Semiring R] [StarRing R] [Fintype W]
variable {C D : OrderedCircuit R W}

/-- Appending two locally unitary chronological circuits preserves local unitarity. -/
theorem append (hC : C.IsLocallyUnitary) (hD : D.IsLocallyUnitary) :
    (C ++ D).IsLocallyUnitary := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · exact hD g hg

end QuaternionicComputing.Circuit.OrderedCircuit.IsLocallyUnitary
