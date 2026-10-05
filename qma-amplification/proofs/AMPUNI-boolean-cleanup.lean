import «AMPUNI-boolean-io-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
open scoped Classical
namespace ShiTMBooleanCleanup
open ShiTMLayoutMachine (Cell Sig isSome)
open ShiTMBooleanIO

def todo : List K := (Finset.univ.erase output).toList
abbrev PC := Fin (todo.length+1)
def nextPC (pc : PC) : PC :=
  ⟨(pc.val+1)%(todo.length+1), Nat.mod_lt _ (by omega)⟩
def commandAt (pc : PC) : Option K := (todo.drop pc.val).head?

theorem todo_nodup : todo.Nodup := Finset.nodup_toList _
@[simp] theorem mem_todo (k : K) : k ∈ todo ↔ k ≠ output := by simp [todo]

/-- Clear every stack except the Boolean output, then reset the finite
variable and halt. This includes the input stack and all retained archives. -/
def machine (pc : PC) : Stmt Gam PC Sig :=
  match commandAt pc with
  | some k => .pop k (fun _ x => x.map (fun _ => Cell.mark))
      (.branch isSome (.goto (fun _ => pc)) (.goto (fun _ => nextPC pc)))
  | none => .load (fun _ => none) .halt

def run : Option (Cfg Gam PC Sig) → Option (Cfg Gam PC Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := input
  k₁ := output
  Γ := Gam
  Λ := PC
  main := 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem clear_run (pc : PC) (k : K) (xs : List (Gam k)) (v : Sig)
    (S : ∀ j, List (Gam j)) (hc : commandAt pc = some k) (hs : S k = xs) :
    run^[xs.length+1] (some ⟨some pc, v, S⟩) =
      some ⟨some (nextPC pc), none, Function.update S k []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, machine, hc, step, stepAux, hs, isSome]
  | cons x xs ih =>
      have hfirst : run (some ⟨some pc, v, S⟩) =
          some ⟨some pc, some Cell.mark, Function.update S k xs⟩ := by
        simp [run, machine, hc, step, stepAux, hs, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih (some Cell.mark) (Function.update S k xs) (by simp)

private theorem active_suffix (pc : PC) (k : K) (xs : List K)
    (hs : todo.drop pc.val = k :: xs) :
    commandAt pc = some k ∧ (nextPC pc).val = pc.val+1 ∧ todo.drop (nextPC pc).val = xs := by
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_cons] at hlen
  have hn : (nextPC pc).val = pc.val+1 := by apply Nat.mod_eq_of_lt; omega
  refine ⟨by simp [commandAt, hs], hn, ?_⟩
  rw [hn, ← List.drop_drop, hs]; rfl

def suffixCost (xs : List K) (S : ∀ j, List (Gam j)) : Nat :=
  (xs.map (fun k => (S k).length)).sum + xs.length

theorem suffix_run (xs : List K) (pc : PC) (v : Sig) (S : ∀ j, List (Gam j))
    (hs : todo.drop pc.val = xs) (hnd : xs.Nodup) :
    ∃ (U : ∀ j, List (Gam j)) (v' : Sig) (pc' : PC),
      run^[suffixCost xs S] (some ⟨some pc, v, S⟩) = some ⟨some pc', v', U⟩
      ∧ pc'.val = pc.val+xs.length
      ∧ ∀ j, U j = if j ∈ xs then [] else S j := by
  induction xs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, by intro j; simp⟩
  | cons k xs ih =>
      obtain ⟨hc, hn, hs'⟩ := active_suffix pc k xs hs
      have hk : k ∉ xs := (List.nodup_cons.mp hnd).1
      let T := Function.update S k []
      have hfirst := clear_run pc k (S k) v S hc rfl
      obtain ⟨U, w, pc', hrest, hp, hf⟩ :=
        ih (nextPC pc) none T hs' (List.nodup_cons.mp hnd).2
      have hmap : xs.map (fun j => (T j).length) = xs.map (fun j => (S j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjk : j ≠ k := by intro he; subst j; exact hk hj
        simp [T, hjk]
      have hcost : (S k).length+1+suffixCost xs T = suffixCost (k::xs) S := by
        simp only [suffixCost, hmap, List.map_cons, List.sum_cons, List.length_cons]
        omega
      refine ⟨U, w, pc', ?_, ?_, ?_⟩
      · have h := ShiTMFanout.iterTwo run _ _ _ _ _ hfirst hrest
        simpa only [hcost] using h
      · rw [hn] at hp
        simp only [List.length_cons]
        omega
      · intro j
        rw [hf]
        by_cases hjk : j = k
        · subst j; simp [hk, T]
        · simp [hjk, T]

/-- Cleanup reaches the exact `haltList` shape: only Boolean output remains,
the control label is halted, and the finite variable is reset to initialState. -/
theorem cleanup_run (v : Sig) (S : ∀ j, List (Gam j)) :
    run^[suffixCost todo S+1] (some ⟨some 0, v, S⟩) =
      some (Turing.haltList finiteMachine (S output)) := by
  obtain ⟨U, v', pc', hr, hp, hf⟩ := suffix_run todo 0 v S (by simp) todo_nodup
  have hc : commandAt pc' = none := by
    simp only [Fin.val_zero, Nat.zero_add] at hp
    simp [commandAt, hp]
  have hdone : run^[1] (some ⟨some pc', v', U⟩) =
      some ⟨none, none, U⟩ := by simp [run, machine, hc, step, stepAux]
  have heq : (⟨none, none, U⟩ : Cfg Gam PC Sig) = Turing.haltList finiteMachine (S output) := by
    change (⟨none, none, U⟩ : Cfg Gam PC Sig) = ⟨none, none, _⟩
    congr 1
    funext j
    rw [hf]
    by_cases hj : j = output
    · subst j; simp [finiteMachine] <;> rfl
    · simp [finiteMachine, hj]
  have hall := ShiTMFanout.iterTwo run _ _ _ _ _ hr hdone
  rw [heq] at hall
  exact hall

end ShiTMBooleanCleanup
