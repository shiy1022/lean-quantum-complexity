import «AMPUNI-run-stack-growth»
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
open scoped Classical
namespace ShiTMGenericCleanup
variable {K sig : Type} [DecidableEq K] [Fintype K] {Gam : K → Type}
variable (output : K) (initial : sig)

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

def todo : List K := (Finset.univ.erase output).toList
abbrev PC := Fin ((todo output).length+1)
def nextPC (pc : (PC output)) : (PC output) :=
  ⟨(pc.val+1)%((todo output).length+1), Nat.mod_lt _ (by omega)⟩
def commandAt (pc : (PC output)) : Option K := ((todo output).drop pc.val).head?

theorem todo_nodup : (todo output).Nodup := Finset.nodup_toList _
@[simp] theorem mem_todo (k : K) : k ∈ (todo output) ↔ k ≠ output := by simp [todo]

/-- Clear every stack except the Boolean output, then reset the finite
variable and halt. This includes the input stack and all retained archives. -/
def machine (pc : (PC output)) : Stmt Gam (PC output) (sig × Bool) :=
  match (commandAt output) pc with
  | some k => .pop k (fun w x => (w.1, x.isSome))
      (.branch Prod.snd (.goto (fun _ => pc)) (.goto (fun _ => (nextPC output) pc)))
  | none => .load (fun _ => (initial, false)) .halt

def run : Option (Cfg Gam (PC output) (sig × Bool)) → Option (Cfg Gam (PC output) (sig × Bool)) :=
  fun c => c.bind (step (machine output initial))

theorem clear_run (pc : (PC output)) (k : K) (xs : List (Gam k)) (v : (sig × Bool))
    (S : ∀ j, List (Gam j)) (hc : (commandAt output) pc = some k) (hs : S k = xs) :
    (run output initial)^[xs.length+1] (some ⟨some pc, v, S⟩) =
      some ⟨some ((nextPC output) pc), (v.1, false), Function.update S k []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, machine, hc, step, stepAux, hs, Prod.snd]
  | cons x xs ih =>
      have hfirst : (run output initial) (some ⟨some pc, v, S⟩) =
          some ⟨some pc, (v.1, true), Function.update S k xs⟩ := by
        simp [run, machine, hc, step, stepAux, hs, Prod.snd]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih ((v.1, true)) (Function.update S k xs) (by simp)

private theorem active_suffix (pc : (PC output)) (k : K) (xs : List K)
    (hs : (todo output).drop pc.val = k :: xs) :
    (commandAt output) pc = some k ∧ ((nextPC output) pc).val = pc.val+1 ∧ (todo output).drop ((nextPC output) pc).val = xs := by
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_cons] at hlen
  have hn : ((nextPC output) pc).val = pc.val+1 := by apply Nat.mod_eq_of_lt; omega
  refine ⟨by simp [commandAt, hs], hn, ?_⟩
  rw [hn, ← List.drop_drop, hs]; rfl

def suffixCost (xs : List K) (S : ∀ j, List (Gam j)) : Nat :=
  (xs.map (fun k => (S k).length)).sum + xs.length

theorem suffix_run (xs : List K) (pc : (PC output)) (v : (sig × Bool)) (S : ∀ j, List (Gam j))
    (hs : (todo output).drop pc.val = xs) (hnd : xs.Nodup) :
    ∃ (U : ∀ j, List (Gam j)) (v' : (sig × Bool)) (pc' : (PC output)),
      (run output initial)^[suffixCost xs S] (some ⟨some pc, v, S⟩) = some ⟨some pc', v', U⟩
      ∧ pc'.val = pc.val+xs.length
      ∧ ∀ j, U j = if j ∈ xs then [] else S j := by
  induction xs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, by intro j; simp⟩
  | cons k xs ih =>
      obtain ⟨hc, hn, hs'⟩ := active_suffix output pc k xs hs
      have hk : k ∉ xs := (List.nodup_cons.mp hnd).1
      let T := Function.update S k []
      have hfirst := clear_run output initial pc k (S k) v S hc rfl
      obtain ⟨U, w, pc', hrest, hp, hf⟩ :=
        ih ((nextPC output) pc) (v.1, false) T hs' (List.nodup_cons.mp hnd).2
      have hmap : xs.map (fun j => (T j).length) = xs.map (fun j => (S j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjk : j ≠ k := by intro he; subst j; exact hk hj
        simp [T, hjk]
      have hcost : (S k).length+1+suffixCost xs T = suffixCost (k::xs) S := by
        simp only [suffixCost, hmap, List.map_cons, List.sum_cons, List.length_cons]
        omega
      refine ⟨U, w, pc', ?_, ?_, ?_⟩
      · have h := iterTwo (run output initial) _ _ _ _ _ hfirst hrest
        simpa only [hcost] using h
      · rw [hn] at hp
        simp only [List.length_cons]
        omega
      · intro j
        rw [hf]
        by_cases hjk : j = k
        · subst j; simp [hk, T]
        · simp [hjk, T]

/-- Drain every non-output stack and reset both the source state and clock flag. -/
theorem cleanup_run (v : sig × Bool) (S : ∀ j, List (Gam j)) :
    (run output initial)^[suffixCost (todo output) S+1]
      (some ⟨some 0, v, S⟩) =
        some ⟨none, (initial, false), Function.update (fun _ => []) output (S output)⟩ := by
  obtain ⟨U, v', pc', hr, hp, hf⟩ :=
    suffix_run output initial (todo output) 0 v S (by simp) (todo_nodup output)
  have hc : commandAt output pc' = none := by
    simp only [Fin.val_zero, Nat.zero_add] at hp
    simp [commandAt, hp]
  have hdone : (run output initial)^[1] (some ⟨some pc', v', U⟩) =
      some ⟨none, (initial, false), U⟩ := by simp [run, machine, hc, step, stepAux]
  have heq : U = Function.update (fun _ => []) output (S output) := by
    funext j
    rw [hf]
    by_cases hj : j = output
    · subst j; simp [mem_todo]
    · simp [mem_todo, hj]
  have hall := iterTwo (run output initial) _ _ _ _ _ hr hdone
  rw [heq] at hall
  exact hall

/-- Cleanup is linear in the stored data plus the fixed number of stacks. -/
theorem cleanup_cost_le (S : ∀ j, List (Gam j)) :
    suffixCost (todo output) S+1 ≤ ShiTMStackGrowth.size S+Fintype.card K+1 := by
  have hs : ((todo output).map (fun k => (S k).length)).sum ≤ ShiTMStackGrowth.size S := by
    rw [todo, Finset.sum_map_toList]
    exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have hl : (todo output).length ≤ Fintype.card K := by
    simpa [todo] using Finset.card_le_card (Finset.erase_subset (Finset.univ : Finset K) output)
  unfold suffixCost
  omega

end ShiTMGenericCleanup
