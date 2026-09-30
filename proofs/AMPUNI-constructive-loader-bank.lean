import «AMPUNI-constructive-loader-valid-prefix»
import «AMPUNI-repeat-loop-induction»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- The complete constructive startup reaches exactly the four-stack
bank invariant consumed by the previously checked repetition loop. -/
theorem valid_prefix_to_preloaded_bank
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (htrue : decodeInput (encodeInput true) = true)
    (hfalse : decodeInput (encodeInput false) = false)
    (n : Nat) (code : List (G input))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (v : Option Bool) (w : W)
    (hi : S (.inl input) =
      List.replicate n (encodeInput true) ++
        encodeInput false :: code)
    (hbase : ∀ j : K, j ≠ input → S (.inl j) = [])
    (h0 : S (.inr (ShiTMRepeatController.header false)) = [])
    (h1 : S (.inr (ShiTMRepeatController.header true)) = [])
    (hs : S (.inr ShiTMRepeatController.scratch) = [])
    (hc : S (.inr ShiTMRepeatController.counter) = []) :
    ∃ parity : Bool,
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[
            2 * n + 3 +
              (ShiTMUnaryLogCost.work (n + 1) + n + 3)]
        (some ⟨some scan, (v, (true, w)), S⟩) =
      some (ShiTMSubroutine.cfg controller
        (ShiTMRepeatController.loopInput entry input
          (parity, w)
          ((List.replicate n true).map encodeInput ++
            encodeInput false :: code)
          false n
          (ShiQMAConstructiveSchedule.rounds p n - 1))) := by
  obtain ⟨parity, S', hr, hi', hh1', hh0', hs', hc', ho'⟩ :=
    valid_prefix_to_first_body p M entry terminal input output
      decodeInput decodeOutput encodeInput htrue hfalse
      n code S v w hi h0 h1 hs hc
  have hS : S' = ShiTMStackFrame.extendStacks
      (ShiTMRepeatController.sourceInput input
        ((List.replicate n true).map encodeInput ++
          encodeInput false :: code))
      (ShiTMRepeatController.bank false n
        (ShiQMAConstructiveSchedule.rounds p n - 1)) := by
    funext j
    cases j with
    | inl j =>
        by_cases hj : j = input
        · subst j
          simpa [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.sourceInput] using hi'
        · rw [ho' j hj, hbase j hj]
          simp [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.sourceInput, hj]
    | inr j =>
        fin_cases j
        · simpa [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.bank,
            ShiTMRepeatController.scratch] using hs'
        · simpa [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.bank,
            ShiTMRepeatController.header] using hh0'
        · simpa [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.bank,
            ShiTMRepeatController.header] using hh1'
        · simpa [ShiTMStackFrame.extendStacks,
            ShiTMRepeatController.bank,
            ShiTMRepeatController.counter] using hc'
  refine ⟨parity, ?_⟩
  rw [hr, hS]
  rfl

end ShiTMConstructiveIntegrated
