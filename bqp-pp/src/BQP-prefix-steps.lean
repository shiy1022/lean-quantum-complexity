import «BQP-prefix-machine»
import «BQP-short-machine-prefix»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPPrefixMachine
open Turing Turing.TM2

 def prefixStacks (tm : FinTM2) (s a : List (tm.Γ tm.k₀)) : ∀ k, List ((framed tm).Γ k) :=
  ShiTMStackFrame.extendStacks (BQPShortMachine.inputStacks tm s) (fun _ => a)

@[simp] theorem stacks_input (tm : FinTM2) (s a : List (tm.Γ tm.k₀)) :
    prefixStacks tm s a (.inl tm.k₀) = s := by
  simp [prefixStacks, ShiTMStackFrame.extendStacks]
@[simp] theorem stacks_aux (tm : FinTM2) (s a : List (tm.Γ tm.k₀)) :
    prefixStacks tm s a (.inr ()) = a := rfl
@[simp] theorem stacks_update_input (tm : FinTM2) (s a t : List (tm.Γ tm.k₀)) :
    Function.update (prefixStacks tm s a) (.inl tm.k₀) t = prefixStacks tm t a := by
  funext k
  cases k with
  | inl k =>
      by_cases h : k = tm.k₀
      · subst k; simp [prefixStacks, ShiTMStackFrame.extendStacks]
      · have hn : (Sum.inl k : tm.K ⊕ Unit) ≠ .inl tm.k₀ := by simpa using h
        simp [prefixStacks, ShiTMStackFrame.extendStacks, hn,
          BQPShortMachine.inputStacks, initList, h]
  | inr u => cases u; simp [prefixStacks, ShiTMStackFrame.extendStacks]
@[simp] theorem stacks_update_aux (tm : FinTM2) (s a t : List (tm.Γ tm.k₀)) :
    Function.update (prefixStacks tm s a) (.inr ()) t = prefixStacks tm s t := by
  funext k
  cases k with
  | inl k => simp [prefixStacks, ShiTMStackFrame.extendStacks]
  | inr u => cases u; simp [prefixStacks, ShiTMStackFrame.extendStacks]

def cfg (tm : FinTM2) (l : Label tm) (v : State tm)
    (s a : List (tm.Γ tm.k₀)) : Cfg (framed tm).Γ (Label tm) (State tm) :=
  ⟨some l, v, prefixStacks tm s a⟩

 theorem scan_left (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (v : State tm)
    (s a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v (ea.symm (.inl b) :: s) a)) =
    some (cfg tm (.inl .scan) (v.1, some (ea.symm (.inl b))) s
      (ea.symm (.inl b) :: a)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem scan_right (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (v : State tm)
    (s a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v (ea.symm (.inr b) :: s) a)) =
    some (cfg tm (.inl (.second b)) (v.1, some (ea.symm (.inr b))) s a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem scan_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v [] a)) =
    some (cfg tm (.inl .rejectInput) (v.1, none) [] a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem second_right (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (b d : Bool) (v : State tm)
    (s a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl (.second b)) v (ea.symm (.inr d) :: s) a)) =
    some (cfg tm (.inl (if b == d then .restore else .rejectInput))
      (v.1, some (ea.symm (.inr d))) s a) := by
  cases b <;> cases d <;> simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem second_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (v : State tm) (a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl (.second b)) v [] a)) =
    some (cfg tm (.inl .rejectInput) (v.1, none) [] a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem restore_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (b : tm.Γ tm.k₀)
    (s a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restore) v s (b :: a))) =
    some (cfg tm (.inl .restore) (v.1, some b) (b :: s) a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem restore_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (s : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restore) v s [])) =
    some (embed tm (initList tm s)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]
  rfl

 theorem rejectInput_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (b : tm.Γ tm.k₀)
    (s a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .rejectInput) v (b :: s) a)) =
    some (cfg tm (.inl .rejectInput) (v.1, some b) s a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem rejectInput_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .rejectInput) v [] a)) =
    some (cfg tm (.inl .rejectAux) (v.1, none) [] a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem rejectAux_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) (b : tm.Γ tm.k₀)
    (a : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .rejectAux) v [] (b :: a))) =
    some (cfg tm (.inl .rejectAux) (v.1, some b) [] a) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]

 theorem stacks_empty (tm : FinTM2) (k : (framed tm).K) : prefixStacks tm [] [] k = [] := by
  cases k <;> simp [prefixStacks, ShiTMStackFrame.extendStacks]

 theorem rejectAux_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (v : State tm) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .rejectAux) v [] [])) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, stacks_update_input tm, stacks_update_aux tm]
  congr 1
  simp only [stacks_empty]
  change _ = (⟨none, (tm.initialState, none), (haltList (machine tm ea eb) [eb.symm false]).stk⟩ :
    Cfg (framed tm).Γ (Label tm) (State tm))
  congr 1
  funext k
  by_cases h : k = .inl tm.k₁
  · subst k; simp [haltList, machine, framed] <;> rfl
  · simp [Function.update_of_ne h, stacks_empty, haltList, machine, framed, h]

end BQPPrefixMachine
