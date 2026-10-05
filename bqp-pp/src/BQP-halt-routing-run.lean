import «AMPUNI-halt-routing»

set_option autoImplicit false
namespace ShiTMHaltRouting
open Turing Turing.TM2
variable {K L R V : Type} {G : K → Type} [DecidableEq K]

private theorem iterate_none (M : L → Stmt G L V) (n : ℕ) :
    (ShiTMSubroutine.run M)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Lift an entire finite source run, converting its terminal halt into an
active continuation. No property of the continuation body is assumed. -/
theorem run_to_some (small : L → Stmt G L V) (big : R → Stmt G R V)
    (f : L → R) (exitLabel : R)
    (hbody : ∀ l, big (f l) = stmt f exitLabel (small l))
    (n : ℕ) (c : Option (Cfg G L V)) (d : Cfg G L V)
    (hr : (ShiTMSubroutine.run small)^[n] c = some d) :
    (ShiTMSubroutine.run big)^[n] (c.map (cfg f exitLabel)) =
      some (cfg f exitLabel d) := by
  induction n generalizing c with
  | zero => exact congrArg (Option.map (cfg f exitLabel)) hr
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hr ⊢
      cases c with
      | none =>
          change (ShiTMSubroutine.run small)^[n] none = some d at hr
          rw [iterate_none] at hr
          cases hr
      | some c =>
          rcases c with ⟨l,v,S⟩
          cases l with
          | none =>
              change (ShiTMSubroutine.run small)^[n] none = some d at hr
              rw [iterate_none] at hr
              cases hr
          | some l =>
              have hs : ShiTMSubroutine.run big
                  ((some (⟨some l,v,S⟩ : Cfg G L V)).map (cfg f exitLabel)) =
                  (ShiTMSubroutine.run small (some ⟨some l,v,S⟩)).map (cfg f exitLabel) := by
                simp [ShiTMSubroutine.run, cfg, step, hbody, stepAux_route]
              rw [hs]
              exact ih _ hr

end ShiTMHaltRouting
