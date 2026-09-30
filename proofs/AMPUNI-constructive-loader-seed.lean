import «AMPUNI-constructive-loader-scan»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- A one-token seed changes the scanned length `n` into `n + 1`, so the
logarithm loader also works at zero input length. -/
theorem actual_seed_step
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (v : Option Bool) (parity : Bool) (w : W)
    (S : ∀ j, List (ShiTMRepeatController.Gam G j)) :
    ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput)
      (some ⟨some seed, (v, (parity, w)), S⟩) =
      some ⟨some (loader (.scan false)), (v, (parity, w)),
        Function.update S (.inr ShiTMRepeatController.scratch)
          (true :: S (.inr ShiTMRepeatController.scratch))⟩ := by
  simp [ShiTMSubroutine.run, machine, seed, loader, step, stepAux]

end ShiTMConstructiveIntegrated
