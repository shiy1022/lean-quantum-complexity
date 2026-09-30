import «AMPUNI-readout-wire-lookup»
import «AMPUNI-readout-index-load»
import «AMPUNI-piece-controller-frame-finish»
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadoutCopy
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev core := ShiTMReadoutLookup.core
def slot (copy : Fin 3) : Fin 4 := ⟨copy.val, by omega⟩
abbrev destination (copy : Fin 3) := ShiTMReadoutLookup.destination (slot copy)
abbrev Label := Fin 3 ⊕ (ShiTMPieceController.Label ⊕
  (ShiTMReadoutIndexLoad.Label ⊕ ShiTMReadoutLookup.Label))
def clearLabel (k : Fin 3) : Label := .inl k
def tableLabel (l : ShiTMPieceController.Label) : Label := .inr (.inl l)
def indexLabel (l : ShiTMReadoutIndexLoad.Label) : Label := .inr (.inr (.inl l))
def lookupLabel (l : ShiTMReadoutLookup.Label) : Label := .inr (.inr (.inr l))
abbrev clearPort (copy : Fin 3) (k : Fin 3) : TopK :=
  core (if k = 0 then 1 else if k = 1 then 2 else ⟨copy.val+4, by omega⟩)

def afterClear (copy : Fin 3) (k : Fin 3) : Label :=
  if k = 0 then clearLabel 1 else if k = 1 then clearLabel 2
  else tableLabel (.dispatch copy 0)

def machine (copy : Fin 3) : Label → Stmt TopGam Label Sig
  | .inl k => .pop (clearPort copy k) pop (.branch isSome
      (.goto (fun _ => clearLabel k)) (.goto (fun _ => afterClear copy k)))
  | .inr (.inl l) => if l = .finished copy then .goto (fun _ => indexLabel .clear)
      else ShiTMSubroutine.stmt tableLabel (ShiTMPieceController.machine l)
  | .inr (.inr (.inl l)) => if l = .finished then .goto (fun _ => lookupLabel .wire)
      else ShiTMSubroutine.stmt indexLabel (ShiTMReadoutIndexLoad.machine l)
  | .inr (.inr (.inr l)) =>
      ShiTMSubroutine.stmt lookupLabel (ShiTMReadoutLookup.machine (slot copy) l)

def run (copy : Fin 3) : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run (machine copy)

def finiteMachine (copy : Fin 3) : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMReadoutIndexLoad.archive
  k₁ := destination copy
  Γ := TopGam
  Λ := Label
  main := clearLabel 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine copy

theorem clear_run (copy : Fin 3) (k : Fin 3) (xs : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j)) (hs : S (clearPort copy k) = xs) :
    (run copy)^[xs.length+1] (some ⟨some (clearLabel k), v, S⟩) =
      some ⟨some (afterClear copy k), none, Function.update S (clearPort copy k) []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, ShiTMSubroutine.run, machine, clearLabel, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
      have hfirst : run copy (some ⟨some (clearLabel k), v, S⟩) =
          some ⟨some (clearLabel k), some x, Function.update S (clearPort copy k) xs⟩ := by
        simp [run, ShiTMSubroutine.run, machine, clearLabel, step, stepAux, hs, pop, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih (some x) (Function.update S (clearPort copy k) xs) (by simp)

theorem table_run (copy : Fin 3) (n : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMPieceController.run^[n] (some ⟨some (.dispatch copy 0), v, S⟩) =
      some ⟨some (.finished copy), v', U⟩) :
    (run copy)^[n] (some ⟨some (tableLabel (.dispatch copy 0)), v, S⟩) =
      some ⟨some (tableLabel (.finished copy)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMPieceController.machine (machine copy)
    tableLabel (.finished copy) rfl (by intro l hl; simp [machine, tableLabel, hl])
    n _ _ rfl hr

theorem index_run (copy : Fin 3) (n : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReadoutIndexLoad.run^[n] (some ⟨some .clear, v, S⟩) =
      some ⟨some .finished, v', U⟩) :
    (run copy)^[n] (some ⟨some (indexLabel .clear), v, S⟩) =
      some ⟨some (indexLabel .finished), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReadoutIndexLoad.machine (machine copy)
    indexLabel .finished rfl (by intro l hl; simp [machine, indexLabel, hl])
    n _ _ rfl hr

theorem lookup_run (copy : Fin 3) (n : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : (ShiTMReadoutLookup.run (slot copy))^[n] (some ⟨some .wire, v, S⟩) =
      some ⟨some .finished, v', U⟩) :
    (run copy)^[n] (some ⟨some (lookupLabel .wire), v, S⟩) =
      some ⟨some (lookupLabel .finished), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMReadoutLookup.machine (slot copy)) (machine copy)
    lookupLabel .finished rfl (by intro l _; rfl) n _ _ rfl hr

end ShiTMReadoutCopy
