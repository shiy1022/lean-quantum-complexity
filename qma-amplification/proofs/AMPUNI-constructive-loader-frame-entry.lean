import «AMPUNI-constructive-loader-seed»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- With clean auxiliary stacks, the seed step gives precisely the
framed initial configuration required by the checked logarithm run. -/
theorem seed_to_framed_loader
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat)
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (hs : S (.inr ShiTMRepeatController.scratch) =
      List.replicate n true)
    (h0 : S (.inr (ShiTMRepeatController.header false)) = [])
    (h1 : S (.inr (ShiTMRepeatController.header true)) =
      List.replicate n true)
    (hc : S (.inr ShiTMRepeatController.counter) = [])
    (w : W) :
    ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput)
      (some ⟨some seed, (none, (true, w)), S⟩) =
    some (ShiTMSubroutine.cfg loader
      (ShiTMScaledLogControllerFrame.cfg
        (fun j => S (.inl j)) (List.replicate n true) w
        (ShiTMUnaryLog.cfg (.scan false) false none true
          (List.replicate (n + 1) true) [] []))) := by
  rw [actual_seed_step]
  congr 1
  dsimp [ShiTMSubroutine.cfg, ShiTMScaledLogControllerFrame.cfg,
    ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
    ShiTMScaledLogAux.cfg, ShiTMUnaryLog.cfg]
  congr 1
  funext j
  cases j with
  | inl j => simp [ShiTMStackFrame.extendStacks]
  | inr j =>
      fin_cases j
      · simpa [ShiTMStackFrame.extendStacks,
          ShiTMScaledLogAux.embedStacks,
          ShiTMUnaryLog.storeFn,
          ShiTMRepeatController.scratch,
          ShiTMRepeatController.header,
          List.replicate_succ] using hs
      · simpa [ShiTMStackFrame.extendStacks,
          ShiTMScaledLogAux.embedStacks,
          ShiTMUnaryLog.storeFn,
          ShiTMRepeatController.scratch,
          ShiTMRepeatController.header] using h0
      · simpa [ShiTMStackFrame.extendStacks,
          ShiTMScaledLogAux.embedStacks,
          ShiTMUnaryLog.storeFn,
          ShiTMRepeatController.scratch,
          ShiTMRepeatController.header] using h1
      · simpa [ShiTMStackFrame.extendStacks,
          ShiTMScaledLogAux.embedStacks,
          ShiTMUnaryLog.storeFn,
          ShiTMRepeatController.scratch,
          ShiTMRepeatController.header,
          ShiTMRepeatController.counter] using hc

end ShiTMConstructiveIntegrated
