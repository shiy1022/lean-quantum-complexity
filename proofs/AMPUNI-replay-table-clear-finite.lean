import «AMPUNI-replay-table-clear-all-run»
import «AMPUNI-output-entry-finite»

set_option autoImplicit false

namespace ShiTMReplayTableClear

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

instance : Fintype Phase where
  elems := {.width, .base, .widthMirror, .baseMirror, .done}
  complete := by
    intro p
    cases p <;> simp

/-- The table-clearing controller itself has finite control and the same
input/output alphabet as the enclosing transducer. -/
def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Phase
  main := .width
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMReplayTableClear
