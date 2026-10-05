import «AMPUNI-boolean-output-final»
import «AMPUNI-boolean-io-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMBooleanWrapper
open ShiTMLayoutMachine (Cell Sig bit)
open ShiTMRetainedTop
open ShiTMBooleanIO (K Gam input output source scratch accumulator)

variable {L : Type} [DecidableEq L] [Fintype L]
abbrev Label (L : Type) := ShiTMBooleanIO.Label ⊕ (L ⊕ ShiTMBooleanFinal.Label)
def bodyLabel (l : L) : Label L := .inr (.inl l)
def finalLabel (l : ShiTMBooleanFinal.Label) : Label L := .inr (.inr l)

def bodyMachine (M : L → Stmt TopGam L Sig) : L → Stmt Gam L Sig := ShiTMIOFrame.machine M

def machine (M : L → Stmt TopGam L Sig) (main terminal : L) : Label L → Stmt Gam (Label L) Sig
  | .inl .ready => .goto (fun _ => bodyLabel main)
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMBooleanIO.machine l)
  | .inr (.inl l) => if l = terminal then .goto (fun _ => finalLabel (.inl .writeOutput))
      else ShiTMSubroutine.stmt bodyLabel (bodyMachine M l)
  | .inr (.inr l) => ShiTMSubroutine.stmt finalLabel (ShiTMBooleanFinal.machine l)

def run (M : L → Stmt TopGam L Sig) (main terminal : L) :
    Option (Cfg Gam (Label L) Sig) → Option (Cfg Gam (Label L) Sig) :=
  ShiTMSubroutine.run (machine M main terminal)

def finiteMachine (M : L → Stmt TopGam L Sig) (main terminal : L) : Turing.FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := input
  k₁ := output
  Γ := Gam
  Λ := Label L
  main := .inl .readInput
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine M main terminal

abbrev cellSource : TopK := .inl (.inl (11 : Fin 14))
abbrev cellOutput : TopK := .inl (.inl (13 : Fin 14))
def initialTop (xs : List Bool) : ∀ k, List (TopGam k) :=
  Function.update (fun _ => []) cellSource (xs.map bit)
def initialIO (xs : List Bool) : ∀ k, List (Gam k) :=
  Function.update (fun _ => []) input xs
def loadedIO (xs : List Bool) : ∀ k, List (Gam k) :=
  ShiTMIOFrame.extendStacks (initialTop xs) (fun _ => [])

theorem loadedIO_eq (xs : List Bool) :
    loadedIO xs = Function.update (fun k : K => ([] : List (Gam k))) source (xs.map bit) := by
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = cellSource
      · subst k; simp [loadedIO, initialTop, ShiTMIOFrame.extendStacks]
      · have hn : (Sum.inl k : K) ≠ source := by simpa using hk
        simp [loadedIO, initialTop, ShiTMIOFrame.extendStacks, hk, hn]
  | inr b => simp [loadedIO, ShiTMIOFrame.extendStacks]

theorem loader_run (M : L → Stmt TopGam L Sig) (main terminal : L) (xs : List Bool) :
    (run M main terminal)^[2*xs.length+2]
      (some ⟨some (.inl .readInput), none, initialIO xs⟩) =
      some ⟨some (.inl .ready), none, loadedIO xs⟩ := by
  obtain ⟨U, hr, hi, ht, hs, hf⟩ := ShiTMBooleanIO.input_run xs none (initialIO xs)
    (by simp [initialIO]) (by simp [initialIO]) (by simp [initialIO])
  have hU : U = loadedIO xs := by
    rw [loadedIO_eq]
    funext k
    by_cases hki : k = input
    · subst k; simpa using hi
    by_cases hks : k = source
    · subst k; simpa using hs
    rw [hf k hki hks]
    simp [initialIO, hki, hks]
  rw [hU] at hr
  have h := ShiTMSubroutine.run_to_terminal ShiTMBooleanIO.machine (machine M main terminal)
    Sum.inl .ready rfl (by intro l hl; cases l <;> simp_all [machine])
    (2*xs.length+2) (some ⟨some .readInput, none, initialIO xs⟩)
    ⟨some .ready, none, loadedIO xs⟩ rfl hr
  simpa only [run, Option.map_some, ShiTMSubroutine.cfg, Option.map_some] using h

theorem body_run (M : L → Stmt TopGam L Sig) (main terminal : L)
    (hterminal : M terminal = .halt) (xs : List Bool) (steps : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hr : (ShiTMSubroutine.run M)^[steps] (some ⟨some main, none, initialTop xs⟩) =
      some ⟨some terminal, v, S⟩) :
    (run M main terminal)^[steps] (some ⟨some (bodyLabel main), none, loadedIO xs⟩) =
      some ⟨some (bodyLabel terminal), v, ShiTMIOFrame.extendStacks S (fun _ => [])⟩ := by
  have h := ShiTMIOFrame.run_iter_frame M (fun _ => []) steps
    (some ⟨some main, none, initialTop xs⟩)
  change (ShiTMSubroutine.run (bodyMachine M))^[steps]
      (some ⟨some main, none, loadedIO xs⟩) =
      ((ShiTMSubroutine.run M)^[steps] (some ⟨some main, none, initialTop xs⟩)).map
        (ShiTMIOFrame.cfg (fun _ => [])) at h
  rw [hr] at h
  have hh : bodyMachine M terminal = .halt := by
    simp [bodyMachine, ShiTMIOFrame.machine, hterminal, ShiTMIOFrame.stmt]
  have hl := ShiTMSubroutine.run_to_terminal (bodyMachine M) (machine M main terminal)
    bodyLabel terminal hh (by intro l hl; simp [machine, bodyLabel, hl]) steps
    (some ⟨some main, none, loadedIO xs⟩)
    ⟨some terminal, v, ShiTMIOFrame.extendStacks S (fun _ => [])⟩ rfl h
  simpa only [run, Option.map_some, ShiTMSubroutine.cfg, Option.map_some] using hl

end ShiTMBooleanWrapper
