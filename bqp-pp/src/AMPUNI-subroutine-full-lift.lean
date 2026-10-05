import «AMPUNI-subroutine-lift»

set_option autoImplicit false
open Turing Turing.TM2
namespace ShiTMSubroutine
variable {K A B V : Type} [DecidableEq K] {G : K → Type}

/-- Exact relabeling of a complete run, including its halted configuration. -/
theorem run_lift (small : A → Stmt G A V) (big : B → Stmt G B V) (f : A → B)
    (hbody : ∀ l, big (f l) = stmt f (small l)) (c : Option (Cfg G A V)) :
    run big (c.map (cfg f)) = (run small c).map (cfg f) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l => simp [run, cfg, step, hbody, stepAux_lift]

theorem run_iter_lift (small : A → Stmt G A V) (big : B → Stmt G B V) (f : A → B)
    (hbody : ∀ l, big (f l) = stmt f (small l)) (n : Nat) (c : Option (Cfg G A V)) :
    (run big)^[n] (c.map (cfg f)) = ((run small)^[n] c).map (cfg f) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_lift small big f hbody]
      exact ih _

end ShiTMSubroutine
