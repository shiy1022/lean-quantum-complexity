import «AMPUNI-boolean-cleanup»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMBooleanFinal
open ShiTMLayoutMachine (Cell Sig isSome)
open ShiTMBooleanIO

abbrev Label := ShiTMBooleanIO.Label ⊕ ShiTMBooleanCleanup.PC

def machine : Label → Stmt Gam Label Sig
  | .inl .done => .goto (fun _ => .inr 0)
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMBooleanIO.machine l)
  | .inr pc => ShiTMSubroutine.stmt Sum.inr (ShiTMBooleanCleanup.machine pc)

def run : Option (Cfg Gam Label Sig) → Option (Cfg Gam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := input
  k₁ := output
  Γ := Gam
  Λ := Label
  main := .inl .writeOutput
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

private theorem cleanup_cost_le (S U : ∀ j, List (Gam j))
    (ha : U accumulator = [])
    (hf : ∀ j, j ≠ accumulator → j ≠ output → U j = S j) :
    ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U ≤
      ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo S := by
  have hsum : ∀ xs : List K, (∀ j ∈ xs, j ≠ output) →
      (xs.map (fun j => (U j).length)).sum ≤ (xs.map (fun j => (S j).length)).sum := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons k xs ih =>
        intro hx
        have hk : (U k).length ≤ (S k).length := by
          by_cases hka : k = accumulator
          · subst k; simp [ha]
          · rw [hf k hka (hx k (by simp))]
        have ht := ih (fun j hj => hx j (by simp [hj]))
        simp only [List.map_cons, List.sum_cons]
        omega
  unfold ShiTMBooleanCleanup.suffixCost
  have h := hsum ShiTMBooleanCleanup.todo (fun j hj => (ShiTMBooleanCleanup.mem_todo j).mp hj)
  omega

/-- Convert the reversed Cell accumulator to forward Boolean output, drain
all other stacks, reset the variable, and reach the exact canonical haltList.
This is a finalization subroutine, not yet a whole-input normalizer theorem. -/
theorem final_output_run (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (ha : S accumulator = (xs.map ShiTMLayoutMachine.bit).reverse) (ho : S output = []) :
    ∃ steps : Nat,
      steps ≤ xs.length + ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo S + 3 ∧
      run^[steps] (some ⟨some (.inl .writeOutput), v, S⟩) =
        some (Turing.haltList finiteMachine xs) := by
  obtain ⟨U, hw, hua, huo, huf⟩ := ShiTMBooleanIO.output_run xs v S ha ho
  have hw' := ShiTMSubroutine.run_to_terminal ShiTMBooleanIO.machine machine Sum.inl
    .done rfl (by intro l hl; cases l <;> simp_all [machine]) (xs.length+1)
    (some ⟨some .writeOutput, v, S⟩) ⟨some .done, none, U⟩ rfl hw
  simp only [Option.map_some, ShiTMSubroutine.cfg, Option.map_some] at hw'
  have hh : run^[1] (some ⟨some (.inl .done), none, U⟩) =
      some ⟨some (.inr 0), none, U⟩ := by rfl
  have hc := ShiTMBooleanCleanup.cleanup_run none U
  have hl := ShiTMSubroutine.run_iter_lift ShiTMBooleanCleanup.machine machine Sum.inr
    (by intro l; rfl) (ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1)
    (some ⟨some 0, none, U⟩)
  change (ShiTMBooleanCleanup.run)^[ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1]
      (some ⟨some 0, none, U⟩) = _ at hc
  change run^[ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1]
      ((some ⟨some 0, none, U⟩).map (ShiTMSubroutine.cfg Sum.inr)) =
      ((ShiTMBooleanCleanup.run)^[ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1]
        (some ⟨some 0, none, U⟩)).map (ShiTMSubroutine.cfg Sum.inr) at hl
  rw [hc] at hl
  have hc' : run^[ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1]
      (some ⟨some (.inr 0), none, U⟩) = some (Turing.haltList finiteMachine xs) := by
    have heq : ShiTMSubroutine.cfg (Sum.inr : ShiTMBooleanCleanup.PC → Label)
        (Turing.haltList ShiTMBooleanCleanup.finiteMachine (U output)) =
        Turing.haltList finiteMachine xs := by
      rw [huo]
      rfl
    change run^[ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1]
        (some ⟨some (.inr 0), none, U⟩) =
        some (ShiTMSubroutine.cfg (Sum.inr : ShiTMBooleanCleanup.PC → Label)
          (Turing.haltList ShiTMBooleanCleanup.finiteMachine (U output))) at hl
    rw [heq] at hl
    exact hl
  let steps := (xs.length+1)+1+(ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo U+1)
  refine ⟨steps, ?_, ?_⟩
  · have hbound := cleanup_cost_le S U hua huf
    dsimp [steps]; omega
  · have hwh := ShiTMFanout.iterTwo run _ _ _ _ _ hw' hh
    exact ShiTMFanout.iterTwo run _ _ _ _ _ hwh hc'

end ShiTMBooleanFinal
