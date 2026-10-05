import «AMPUNI-constructive-loader-prefix»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- The concrete integrated program duplicates the scanned unary header
into the loader source stack and the controller's preserved header bank. -/
theorem actual_duplicate_header
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat)
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (v : Option Bool) (parity : Bool) (w : W)
    (hh : S (.inr (ShiTMRepeatController.header false)) =
      List.replicate n true)
    (hs : S (.inr ShiTMRepeatController.scratch) = [])
    (hm : S (.inr (ShiTMRepeatController.header true)) = []) :
    ∃ S' : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[n + 1]
        (some ⟨some duplicate, (v, (parity, w)), S⟩) =
        some ⟨some seed, (none, (parity, w)), S'⟩ ∧
      S' (.inr (ShiTMRepeatController.header false)) = [] ∧
      S' (.inr ShiTMRepeatController.scratch) =
        List.replicate n true ∧
      S' (.inr (ShiTMRepeatController.header true)) =
        List.replicate n true ∧
      S' (.inr ShiTMRepeatController.counter) =
        S (.inr ShiTMRepeatController.counter) ∧
      (∀ j : K, S' (.inl j) = S (.inl j)) := by
  apply ShiTMRepeatLoaderPrep.duplicate_length_header
    (machine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
    duplicate seed n S v (parity, w)
  · rfl
  · exact hh
  · exact hs
  · exact hm

end ShiTMConstructiveIntegrated
