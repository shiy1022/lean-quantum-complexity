import «AMPUNI-fanout-prepare-run»
import «AMPUNI-mark-block-run»
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadoutScratch
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev core (k : Fin 14) : TopK := .inl (.inl k)
abbrev Label := ShiTMFanoutPrepare.Label ⊕ ((Bool × ShiTMPieceEntry.EntryLabel) ⊕ Fin 3)
def prepLabel (l : ShiTMFanoutPrepare.Label) : Label := .inl l
def addLabel (second : Bool) (l : ShiTMPieceEntry.EntryLabel) : Label := .inr (.inl (second, l))
def localLabel (k : Fin 3) : Label := .inr (.inr k)
def source (second : Bool) : Fin 4 := if second then 2 else 0

def machine : Label → Stmt TopGam Label Sig
  | .inl l => if l = .finished then .goto (fun _ => addLabel false (.inr .copy))
      else ShiTMSubroutine.stmt prepLabel (ShiTMFanoutPrepare.machine true l)
  | .inr (.inl (second, l)) => if l = .inr .done then
      .goto (fun _ => if second then localLabel 0 else addLabel true (.inr .copy))
      else ShiTMSubroutine.stmt (addLabel second) (ShiTMPieceEntry.machineAt (source second) 2 l)
  | .inr (.inr k) => if k = 0 then
      .pop (core 7) pop (.branch isSome (.goto (fun _ => localLabel 0))
        (.push (core 2) (cst .mark) (.goto (fun _ => localLabel 1))))
      else if k = 1 then .pop (core 2) pop (.branch isSome
        (.push (core 7) get (.goto (fun _ => localLabel 1)))
        (.goto (fun _ => localLabel 2)))
      else .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inr 0
  k₁ := core 7
  Γ := TopGam
  Λ := Label
  main := prepLabel (.clear 0)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem prep_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : (ShiTMFanoutPrepare.run true)^[steps] (some ⟨some (.clear 0), v, S⟩) =
      some ⟨some .finished, v', U⟩) :
    run^[steps] (some ⟨some (prepLabel (.clear 0)), v, S⟩) =
      some ⟨some (prepLabel .finished), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMFanoutPrepare.machine true) machine prepLabel
    .finished rfl (by intro l hl; simp [machine, prepLabel, hl]) steps _ _ rfl hr

theorem add_run (second : Bool) (n : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hs : S (.inr (source second)) = List.replicate n Cell.mark)
    (ht : S (core 3) = []) :
    ∃ U : ∀ k, List (TopGam k),
      run^[2*n+2] (some ⟨some (addLabel second (.inr .copy)), v, S⟩) =
        some ⟨some (addLabel second (.inr .done)), none, U⟩
      ∧ U (core 2) = List.replicate n Cell.mark ++ S (core 2)
      ∧ ∀ k, k ≠ core 2 → U k = S k := by
  obtain ⟨U, hr, hu, hd, h3, hf⟩ := ShiTMPieceEntry.mark_block_run_at (source second) 2 (by decide) n v S hs ht
  refine ⟨U, ?_, hd, ?_⟩
  · exact ShiTMSubroutine.run_to_terminal (ShiTMPieceEntry.machineAt (source second) 2) machine
      (addLabel second) (.inr .done) rfl (by intro l hl; simp [machine, addLabel, hl]) _ _ _ rfl hr
  · intro k hk
    by_cases hks : k = .inr (source second)
    · subst k; exact hu.trans hs.symm
    by_cases hk3 : k = core 3
    · subst k; exact h3.trans ht.symm
    exact hf k hks hk hk3

theorem clear_run (xs : List Cell) (v : Sig) (S : ∀ k, List (TopGam k))
    (hs : S (core 7) = xs) :
    run^[xs.length+1] (some ⟨some (localLabel 0), v, S⟩) =
      some ⟨some (localLabel 1), none,
        Function.update (Function.update S (core 7) []) (core 2) (Cell.mark :: S (core 2))⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, ShiTMSubroutine.run, machine, localLabel, step, stepAux, hs, pop, isSome, cst, core]
  | cons x xs ih =>
      have hfirst : run (some ⟨some (localLabel 0), v, S⟩) =
          some ⟨some (localLabel 0), some x, Function.update S (core 7) xs⟩ := by
        simp [run, ShiTMSubroutine.run, machine, localLabel, step, stepAux, hs, pop, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa [core] using ih (some x) (Function.update S (core 7) xs) (by simp)

theorem transfer_run (n : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hs : S (core 2) = List.replicate n Cell.mark) :
    ∃ U : ∀ k, List (TopGam k),
      run^[n+1] (some ⟨some (localLabel 1), v, S⟩) = some ⟨some (localLabel 2), none, U⟩
      ∧ U (core 2) = []
      ∧ U (core 7) = List.replicate n Cell.mark ++ S (core 7)
      ∧ ∀ k, k ≠ core 2 → k ≠ core 7 → U k = S k := by
  induction n generalizing v S with
  | zero =>
      have he : S (core 2) = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro k _ _; rfl⟩
      simp [run, ShiTMSubroutine.run, machine, localLabel, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S (core 2) = Cell.mark :: List.replicate n Cell.mark := by simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S (core 2) (List.replicate n Cell.mark))
        (core 7) (Cell.mark :: S (core 7))
      have hfirst : run (some ⟨some (localLabel 1), v, S⟩) =
          some ⟨some (localLabel 1), some Cell.mark, T⟩ := by
        simp [run, ShiTMSubroutine.run, machine, localLabel, step, stepAux, hm, pop, isSome, ShiTMLayoutMachine.get, T, core]
      obtain ⟨U, hr, h2, h7, hf⟩ := ih (some Cell.mark) T (by simp [T, core])
      refine ⟨U, ?_, h2, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]; exact hr
      · rw [h7]; simp [T, List.replicate_add, List.append_assoc]
      · intro k hk2 hk7; rw [hf k hk2 hk7]; simp [T, hk2, hk7]

end ShiTMReadoutScratch
