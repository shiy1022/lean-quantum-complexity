import «AMPUNI-output-entry-machine»
import «AMPUNI-retained-finite»

set_option autoImplicit false

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The full header/output/table/parser control graph has finite alphabets. -/
def finite_entry_machine : Fintype TopK × Fintype Label ×
    (∀ k : TopK, Fintype (TopGam k)) := by
  exact ⟨inferInstance, inferInstance, fun k => inferInstance⟩

/-- This is the internal Cell-alphabet machine. Boolean input/output adapters
and total polynomial-time packaging remain separate obligations. -/
def internalMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := headerLabel .inputLength
  ΛFin := finite_entry_machine.2.1
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMOutputEntry
