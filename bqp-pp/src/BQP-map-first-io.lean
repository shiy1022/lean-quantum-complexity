import «BQP-map-first-runs»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2

theorem iterate_chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (h : f^[a] x = y) (h' : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

def pair (x w : List Bool) : List (Bool ⊕ Bool) := x.map Sum.inl ++ w.map Sum.inr

theorem init_eq (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (s : List (Bool ⊕ Bool)) : initList (machine tm ea eb) s =
    cfg tm (.inl .scan) (tm.initialState,none) (fun _ => []) s [] [] [] := by
  apply congrArg (fun S => (⟨some (.inl .scan), (tm.initialState,none), S⟩ :
    Cfg (framed tm).Γ (Label tm) (State tm)))
  funext k
  cases k with
  | inl k => simp [initList, machine, framed, mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [initList, machine, framed, mapStacks, ShiTMStackFrame.extendStacks, extras] <;> rfl

theorem source_init_stk (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ xs = (initList tm xs).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, h]

theorem input_prefix (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (x w : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[2*x.length+w.length+2]
      (some (initList (machine tm ea eb) (pair x w))) =
    some (embed tm (extras [] [] w.reverse []) (initList tm (x.map ea.symm))) := by
  obtain ⟨v, hx⟩ := scan_left_run tm ea eb x (tm.initialState,none) (fun _ => [])
    (w.map Sum.inr) [] [] []
  obtain ⟨v', hw⟩ := scan_right_run tm ea eb w v (fun _ => []) [] [] [] x.reverse
  simp only [List.append_nil] at hx hw
  have hs := iterate_chain _ _ _ _ _ _ hx hw
  have hn := scan_nil tm ea eb v' (fun _ => []) [] [] w.reverse x.reverse
  have ht := iterate_chain _ _ _ _ (x.length+w.length) 1 hs hn
  have hr := restoreInput_run tm ea eb x.reverse (v'.1,none) (fun _ => []) [] [] w.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hall := iterate_chain _ _ _ _ _ _ ht hr
  rw [show (x.length+w.length+1)+(x.length+1) = 2*x.length+w.length+2 by omega] at hall
  rw [init_eq]
  simpa only [pair, source_init_stk, cfg, embed, ShiTMHaltRouting.cfg,
    ShiTMStateFrame.cfg, ShiTMStackFrame.cfg, mapStacks, initList, Option.elim_some] using hall

theorem final_stacks (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (o : List (Bool ⊕ Bool)) :
    (⟨none, (tm.initialState,none), mapStacks tm (fun _ => []) [] o [] []⟩ :
      Cfg (framed tm).Γ (Label tm) (State tm)) = haltList (machine tm ea eb) o := by
  apply congrArg (fun S => (⟨none, (tm.initialState,none), S⟩ :
    Cfg (framed tm).Γ (Label tm) (State tm)))
  funext k
  cases k with
  | inl k => simp [haltList, machine, framed, mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [haltList, machine, framed, mapStacks, ShiTMStackFrame.extendStacks, extras] <;> rfl

theorem output_suffix (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (y w : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[w.length+2*y.length+3]
      (some (embed tm (extras [] [] w.reverse []) (haltList tm (y.map eb.symm)))) =
    some (haltList (machine tm ea eb) (pair y w)) := by
  let S := (haltList tm (y.map eb.symm)).stk
  have hw := restoreWitness_run tm ea eb w.reverse (tm.initialState,none) S [] [] []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hw
  have hr := reverseResult_run tm ea eb (y.map eb.symm) (tm.initialState,none) S
    [] (w.map Sum.inr) [] [] (by simp [S, haltList])
  have hs : Function.update S tm.k₁ [] = (fun _ => []) := by
    funext k
    by_cases h : k = tm.k₁
    · subst k; simp
    · simp [S, haltList, h]
  simp only [List.length_map, hs, List.append_nil, List.map_reverse,
    List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id_fun', id_eq] at hr
  have he := emitResult_run tm ea eb y.reverse (tm.initialState,none) (fun _ => [])
    [] (w.map Sum.inr) []
  simp only [List.length_reverse, List.reverse_reverse, final_stacks tm ea eb] at he
  have ht := iterate_chain _ _ _ _ _ _ hw hr
  have hall := iterate_chain _ _ _ _ _ _ ht he
  rw [show (w.length+1+(y.length+1))+(y.length+1) = w.length+2*y.length+3 by omega] at hall
  have hin : embed tm (extras [] [] w.reverse []) (haltList tm (y.map eb.symm)) =
      cfg tm (.inl .restoreWitness) (tm.initialState,none) S [] [] w.reverse [] := by rfl
  rw [hin]
  exact hall

end BQPMapFirst
