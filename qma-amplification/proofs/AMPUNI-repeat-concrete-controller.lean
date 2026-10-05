import «AMPUNI-repeat-controller-final»
import «AMPUNI-repeat-fueled-machine»
import «AMPUNI-normalized-boolean-quadratic»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatConcrete

abbrev source (k : Nat) : Turing.FinTM2 :=
  ShiTMRepeatFueled.finiteMachine
    ShiTMNormalizedEntry.booleanMachine (Equiv.refl Bool) k

def terminal (k : Nat) : (source k).Λ :=
  ShiTMFueledAssembly.bodyLabel (.inr (.inr ()))

theorem terminal_halt (k : Nat) :
    (source k).m (terminal k) = .halt := by
  rfl

/-- A finite loop controller for the concrete QMA amplifier, with four
additional Boolean stacks. Its initial configuration still needs the unary
header and round counter to be loaded before a variable-round run. -/
def preloadedMachine (k : Nat) : Turing.FinTM2 := by
  letI : DecidableEq (source k).K := (source k).kDecidableEq
  letI : DecidableEq (source k).Λ := Classical.decEq _
  letI : Fintype (source k).K := (source k).kFin
  letI : Fintype (source k).Λ := (source k).ΛFin
  exact {
    K := (source k).K ⊕ ShiTMRepeatController.Aux
    kDecidableEq := inferInstance
    kFin := inferInstance
    k₀ := .inl (source k).k₀
    k₁ := .inl (source k).k₁
    Γ := ShiTMRepeatController.Gam (source k).Γ
    Λ := ShiTMRepeatController.Label (source k).Λ
    main := ShiTMRepeatController.body false (source k).main
    ΛFin := inferInstance
    σ := (source k).σ
    initialState := (source k).initialState
    σFin := (source k).σFin
    Γk₀Fin := (source k).Γk₀Fin
    m := ShiTMRepeatController.machine
      (source k).m (source k).main (terminal k)
      (source k).k₀ (source k).k₁ id id
  }

end ShiTMRepeatConcrete
