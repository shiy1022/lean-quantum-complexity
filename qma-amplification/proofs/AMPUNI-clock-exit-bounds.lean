import «AMPUNI-clock-exit»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMClockExit
open ShiTMTypedTimeout
variable {K L sig : Type} [DecidableEq K] {Gam : K → Type}

/-- Every fuelled execution reaches cleanup, including arbitrary malformed
source states, source halts, and fuel exhaustion. Cleanup is not executed yet. -/
theorem reaches_exit (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool))
    (fuel : List Bool) (c : Cfg Gam L sig) :
    ∃ (steps : Nat) (rest : List Bool) (v : sig) (S : ∀ k, List (Gam k)),
      (run M onExit)^[steps] (some (cfg fuel c)) =
        some ⟨some timeout, (v, false), liftStk rest S⟩ ∧
      steps ≤ 2*fuel.length+1 ∧ rest.length ≤ fuel.length := by
  induction fuel generalizing c with
  | nil =>
      rcases c with ⟨_ | l, v, S⟩
      · exact ⟨0, [], v, S, rfl, by simp, by simp⟩
      · exact ⟨1, [], v, S, empty_fuel M onExit l v S, by simp, by simp⟩
  | cons x fuel ih =>
      rcases c with ⟨_ | l, v, S⟩
      · exact ⟨0, x::fuel, v, S, rfl, by omega, le_rfl⟩
      · obtain ⟨t, rest, w, U, hr, ht, hf⟩ := ih (stepAux (M l) v S)
        refine ⟨t+2, rest, w, U, ?_, ?_, ?_⟩
        · rw [Function.iterate_add_apply, two_steps M onExit l v S x fuel]
          exact hr
        · simp only [List.length_cons]
          omega
        · simp only [List.length_cons]
          omega

private theorem iterate_none {A : Type} (f : Option A → Option A) (hf : f none = none) :
    ∀ n : Nat, f^[n] none = none
  | 0 => rfl
  | n+1 => by rw [Function.iterate_succ_apply, hf]; exact iterate_none f hf n

/-- Exact source executions are preserved up to their final configuration,
with unused fuel retained and source halts redirected to cleanup. -/
theorem exact_run (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool)) :
    ∀ (steps : Nat) (c d : Cfg Gam L sig) (fuel : List Bool),
      (fun z : Option (Cfg Gam L sig) => z.bind (step M))^[steps] (some c) = some d →
      (run M onExit)^[2*steps]
        (some (cfg (List.replicate steps true ++ fuel) c)) = some (cfg fuel d) := by
  intro steps
  induction steps with
  | zero =>
      intro c d fuel h
      have he : c = d := by simpa using h
      subst d
      rfl
  | succ steps ih =>
      intro c d fuel h
      rcases c with ⟨_ | l, v, S⟩
      · rw [Function.iterate_succ_apply] at h
        have hz : (some ({l := none, var := v, stk := S} : Cfg Gam L sig)).bind (step M) = none := rfl
        rw [hz, iterate_none _ (by rfl) steps] at h
        contradiction
      · have htail :
            (fun z : Option (Cfg Gam L sig) => z.bind (step M))^[steps]
              (some (stepAux (M l) v S)) = some d := by
          rw [Function.iterate_succ_apply] at h
          exact h
        have hr := ih (stepAux (M l) v S) d fuel htail
        rw [show 2*(steps+1) = 2*steps+2 by omega, Function.iterate_add_apply]
        rw [List.replicate_succ, List.cons_append, two_steps]
        exact hr

end ShiTMClockExit
