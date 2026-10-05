import «AMPUNI-constructive-loader-actual»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private theorem stepAux_pushFinal (k : Nat)
    (q : Stmt (ShiTMRepeatController.Gam G) (Label L)
      (Option Bool × (Bool × W)))
    (v : Option Bool × (Bool × W))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j)) :
    stepAux (pushFinal k q) v S =
      stepAux q v
        (Function.update S
          (.inr ShiTMRepeatController.counter)
          (List.replicate k true ++
            S (.inr ShiTMRepeatController.counter))) := by
  induction k generalizing S with
  | zero => simp [pushFinal]
  | succ k ih =>
      simp only [pushFinal, stepAux]
      rw [ih]
      congr 1
      funext j
      by_cases hj : j = Sum.inr ShiTMRepeatController.counter
      · subst j
        simp
        calc
          List.replicate k true ++
              (true :: S (.inr ShiTMRepeatController.counter)) =
              (List.replicate k true ++ [true]) ++
                S (.inr ShiTMRepeatController.counter) := by
                  simp [List.append_assoc]
          _ = List.replicate (k + 1) true ++
                S (.inr ShiTMRepeatController.counter) := by
                  rw [List.replicate_add]
                  rfl
      · simp [hj]

/-- The active loader finish instruction adds the fixed offset and enters
the controller's prefix-restoration phase in one TM2 step. -/
theorem loader_finish_step
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (v : Option Bool × (Bool × W))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j)) :
    ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput)
      (some ⟨some (loader .done), v, S⟩) =
    some ⟨some (controller
      (ShiTMRepeatController.phase true .separator)),
      v,
      Function.update S (.inr ShiTMRepeatController.counter)
        (List.replicate (ShiTMScaledLog.scheduleOffset p) true ++
          S (.inr ShiTMRepeatController.counter))⟩ := by
  simp [ShiTMSubroutine.run, machine, loader, step,
    stepAux_pushFinal, stepAux]

end ShiTMConstructiveIntegrated
