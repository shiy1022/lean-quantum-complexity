import «AMPUNI-repeat-loop-bank»
import «AMPUNI-repeat-controller-final»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- After the last body call, an empty counter triggers final cleanup. All
auxiliary stacks are empty at halt and every source stack is preserved. -/
theorem terminal_to_clean_halt
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (n : Nat)
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (haux : ∀ h : Aux, S (.inr h) = bank b n 0 h) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[n + 2]
        (some ⟨some (body b terminal), (v, w), S⟩) =
          some ⟨none, (none, w), S'⟩ ∧
      (∀ j : K, S' (.inl j) = S (.inl j)) ∧
      (∀ h : Aux, S' (.inr h) = []) := by
  let P := machine M entry terminal input output decodeOutput encodeInput
  let S₁ := Function.update S (.inr counter) []
  have hc : S (.inr counter) = [] := by
    rw [haux, bank_counter]
    rfl
  have hterm : ShiTMSubroutine.run P
      (some ⟨some (body b terminal), (v, w), S⟩) =
        some ⟨some (phase b .clearHeader), (none, w), S₁⟩ := by
    exact terminal_done M entry terminal input output decodeOutput
      encodeInput b S v w hc
  have hh₁ : S₁ (.inr (header b)) = List.replicate n true := by
    cases b with
    | false => simpa [S₁, bank, header, counter] using haux 1
    | true => simpa [S₁, bank, header, counter] using haux 2
  let S₂ := Function.update S₁ (.inr (header b)) []
  have hclear :
      (ShiTMSubroutine.run P)^[n + 1]
        (some ⟨some (phase b .clearHeader), (none, w), S₁⟩) =
          some ⟨none, (none, w), S₂⟩ := by
    simpa only [List.length_replicate, S₂] using
      clear_header_run M entry terminal input output decodeOutput
        encodeInput b (List.replicate n true) S₁ none w hh₁
  have hbase (j : K) : S₂ (.inl j) = S (.inl j) := by
    simp [S₂, S₁]
  have haux₂ (h : Aux) : S₂ (.inr h) = [] := by
    fin_cases h <;> cases b <;>
      simp [S₂, S₁, bank, header, counter, scratch, haux] at *
  refine ⟨S₂, ?_, hbase, haux₂⟩
  rw [show n + 2 = (n + 1) + 1 by omega,
    Function.iterate_add_apply]
  change (ShiTMSubroutine.run P)^[n + 1]
    (ShiTMSubroutine.run P
      (some ⟨some (body b terminal), (v, w), S⟩)) = _
  rw [hterm, hclear]

end ShiTMRepeatController
