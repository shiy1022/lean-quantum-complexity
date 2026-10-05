import «AMPUNI-constructive-loader-finish»
import «AMPUNI-repeat-controller-prefix»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- After the logarithmic loader finishes, one offset step followed by the
existing header-restoration run reaches the first source-machine body with
the raw unary prefix restored and the full preloaded counter. -/
theorem finish_to_first_body
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat) (code : List (G input))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (parity : Bool) (w : W)
    (hi : S (.inl input) = code)
    (hh : S (.inr (ShiTMRepeatController.header true)) =
      List.replicate n true)
    (hm : S (.inr (ShiTMRepeatController.header false)) = [])
    (hscratch : S (.inr ShiTMRepeatController.scratch) = [])
    (hc : S (.inr ShiTMRepeatController.counter) =
      List.replicate
        (p.natDegree * Nat.log 2 (n + 1)) true) :
    ∃ S' : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[n + 3]
        (some ⟨some (loader .done), (none, (parity, w)), S⟩) =
        some ⟨some (controller
          (ShiTMRepeatController.body false entry)),
          (none, (parity, w)), S'⟩ ∧
      S' (.inl input) =
        (List.replicate n true).map encodeInput ++
          encodeInput false :: code ∧
      S' (.inr (ShiTMRepeatController.header true)) = [] ∧
      S' (.inr (ShiTMRepeatController.header false)) =
        List.replicate n true ∧
      S' (.inr ShiTMRepeatController.scratch) = [] ∧
      S' (.inr ShiTMRepeatController.counter) =
        List.replicate
          (ShiQMAConstructiveSchedule.rounds p n - 1) true ∧
      (∀ j : K, j ≠ input → S' (.inl j) = S (.inl j)) := by
  let T := Function.update S (.inr ShiTMRepeatController.counter)
    (List.replicate (ShiTMScaledLog.scheduleOffset p) true ++
      S (.inr ShiTMRepeatController.counter))
  have hTi : T (.inl input) = code := by simp [T, hi]
  have hTh : T (.inr (ShiTMRepeatController.header true)) =
      List.replicate n true := by
    simpa [T, ShiTMRepeatController.header,
      ShiTMRepeatController.counter] using hh
  have hTm : T (.inr (ShiTMRepeatController.header false)) = [] := by
    simpa [T, ShiTMRepeatController.header,
      ShiTMRepeatController.counter] using hm
  obtain ⟨S', hp, hi', hh', hm', hs', hc', hother⟩ :=
    ShiTMRepeatController.prefix_to_body
      M entry terminal input output decodeOutput encodeInput
      true n code T none (parity, w) hTi hTh hTm
  have hlift := ShiTMSubroutine.run_iter_lift
    (ShiTMRepeatController.machine M entry terminal
      input output decodeOutput encodeInput)
    (machine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
    controller (by intro l; rfl) (n + 2)
    (some ⟨some (ShiTMRepeatController.phase true .separator),
      (none, (parity, w)), T⟩)
  rw [hp] at hlift
  refine ⟨S', ?_, hi', hh', hm', ?_, ?_, hother⟩
  · rw [show n + 3 = (n + 2) + 1 by omega,
      Function.iterate_add_apply _ (n + 2) 1]
    simp only [Function.iterate_one]
    rw [loader_finish_step]
    simpa [ShiTMSubroutine.cfg] using hlift
  · exact hs'.trans (by simpa [T, ShiTMRepeatController.scratch,
      ShiTMRepeatController.counter] using hscratch)
  · have hn : ShiTMScaledLog.scheduleOffset p +
        p.natDegree * Nat.log 2 (n + 1) =
        ShiQMAConstructiveSchedule.rounds p n - 1 := by
      dsimp [ShiTMScaledLog.scheduleOffset,
        ShiQMAConstructiveSchedule.rounds,
        ShiQMAConstructiveSchedule.exponentBudget]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hc']
    simp [T, hc, ← List.replicate_add, hn]

end ShiTMConstructiveIntegrated
