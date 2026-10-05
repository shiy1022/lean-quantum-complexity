import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2

namespace ShiTMSubroutine
variable {K A B V : Type} [DecidableEq K] {G : K → Type}

def stmt (f : A → B) : Stmt G A V → Stmt G B V
  | .push k g q => .push k g (stmt f q)
  | .peek k g q => .peek k g (stmt f q)
  | .pop k g q => .pop k g (stmt f q)
  | .load g q => .load g (stmt f q)
  | .branch g p q => .branch g (stmt f p) (stmt f q)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

def cfg (f : A → B) (c : Cfg G A V) : Cfg G B V :=
  ⟨c.l.map f, c.var, c.stk⟩

def run (M : A → Stmt G A V) : Option (Cfg G A V) → Option (Cfg G A V) :=
  fun c => c.bind (step M)

theorem stepAux_lift (f : A → B) (q : Stmt G A V) (v : V)
    (S : ∀ k, List (G k)) :
    stepAux (stmt f q) v S = cfg f (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih => exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih => exact ih (g v (S k).head?) S
  | pop k g q ih => exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih => exact ih (g v) S
  | branch g p q ihp ihq =>
      simp only [stmt, stepAux]
      cases g v
      · exact ihq v S
      · exact ihp v S
  | goto g => rfl
  | halt => rfl

private theorem iterate_none (M : A → Stmt G A V) (n : Nat) :
    (run M)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- A subroutine ending at its active halt label can be embedded into a
larger machine that replaces that label by a handoff. No extra steps are
charged until the handoff itself is executed. -/
theorem run_to_terminal (small : A → Stmt G A V) (big : B → Stmt G B V)
    (f : A → B) (terminal : A) (hterm : small terminal = .halt)
    (hbody : ∀ l, l ≠ terminal → big (f l) = stmt f (small l))
    (n : Nat) (c : Option (Cfg G A V)) (d : Cfg G A V)
    (hd : d.l = some terminal) (hr : (run small)^[n] c = some d) :
    (run big)^[n] (c.map (cfg f)) = some (cfg f d) := by
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map (cfg f)) hr
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hr ⊢
      cases c with
      | none =>
          change (run small)^[n] none = some d at hr
          rw [iterate_none] at hr
          cases hr
      | some c =>
          rcases c with ⟨l, v, S⟩
          cases l with
          | none =>
              change (run small)^[n] none = some d at hr
              rw [iterate_none] at hr
              cases hr
          | some l =>
              by_cases hl : l = terminal
              · subst l
                have hs : run small (some ⟨some terminal, v, S⟩) =
                    some ⟨none, v, S⟩ := by simp [run, step, hterm, stepAux]
                rw [hs] at hr
                cases n with
                | zero =>
                    have heq := congrArg Cfg.l (Option.some.inj hr)
                    simp [hd] at heq
                | succ n =>
                    rw [Function.iterate_succ_apply] at hr
                    change (run small)^[n] none = some d at hr
                    rw [iterate_none] at hr
                    cases hr
              · have hs : run big ((some ⟨some l, v, S⟩).map (cfg f)) =
                    (run small (some ⟨some l, v, S⟩)).map (cfg f) := by
                  simp [run, cfg, step, hbody l hl, stepAux_lift]
                rw [hs]
                exact ih _ hr

end ShiTMSubroutine
