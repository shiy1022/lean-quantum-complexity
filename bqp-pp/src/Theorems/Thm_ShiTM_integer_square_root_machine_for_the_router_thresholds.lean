-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.integer_square_root_machine_for_the_router_thresholds`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_integer_square_root_machine_for_the_router_thresholds`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace ShiTM

theorem integer_square_root_machine_for_the_router_thresholds :
    -- (1) THE INTEGER-SQUARE-ROOT MACHINE.  ONE `FinTM2`, seven `Bool` stacks and
    -- THIRTEEN labels, whose input port carries the unary code of `h` and whose output
    -- port carries the `(h + 7)`-bit little-endian expansion of
    -- `S = Nat.sqrt (2 * 4 ^ (h + 3)) = ⌊2 ^ (h + 3) * √2⌋` -- the quantity from which
    -- `RF-BUILDc`'s five thresholds `A`, `2A`, `2A + 2S`, `2A + 4S`, `2A + 4S + 16` are
    -- built and which `ROUTER-1b` compares against but takes as GIVEN.  The step count is
    -- `2 * h * h + 27 * h + 67`: QUADRATIC in `h`, not `2 ^ h`, because the algorithm is
    -- the digit-by-digit (restoring) square root -- `h + 3` iterations, one output bit
    -- each -- and not repeated subtraction of odd numbers.  The bit encoder is
    -- ∀-QUANTIFIED and pinned only by its two defining equations, so any consumer's own
    -- encoder (in particular `ROUTER-1b`'s `bits`) may be substituted.
    (∃ (tm : Turing.FinTM2) (ei : tm.Γ tm.k₀ ≃ Bool) (eo : tm.Γ tm.k₁ ≃ Bool),
      (∀ bits : ℕ → ℕ → List Bool,
          (∀ n : ℕ, bits 0 n = []) →
          (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2)) →
          ∀ h : ℕ, Nonempty (Turing.TM2OutputsInTime tm
            (List.map ei.invFun (List.replicate h true ++ [false]))
            (Option.some (List.map eo.invFun
              (bits (h + 7) (Nat.sqrt (2 * 4 ^ (h + 3))))))
            (2 * h * h + 27 * h + 67)))
      -- (2) THE REJECT PATH, and with it TOTALITY.  The SAME machine halts on EVERY input
      -- that is not a well-formed unary code -- no terminator, or junk after it -- with
      -- EMPTY output, inside `2 * |w| + 4` steps, every stack drained and the register
      -- back at its initial value.  Nothing is left undefined on malformed input.
    ∧ (∀ w : List Bool, (∀ h : ℕ, w ≠ List.replicate h true ++ [false]) →
          Nonempty (Turing.TM2OutputsInTime tm (List.map ei.invFun w)
            (Option.some ([] : List (tm.Γ tm.k₁))) (2 * w.length + 4))))
    -- (3) NON-VACUITY, INSIDE THE THEOREM.  At `h = 0` and `h = 1` the computed value is
    -- exhibited: `⌊8√2⌋ = 11` on seven bits and `⌊16√2⌋ = 22` on eight, two genuinely
    -- different non-empty strings -- so the accept outputs are neither degenerate nor
    -- confusable with the reject output.
  ∧ (∃ bits : ℕ → ℕ → List Bool,
      (∀ n : ℕ, bits 0 n = [])
    ∧ (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2))
    ∧ Nat.sqrt (2 * 4 ^ (0 + 3)) = 11
    ∧ Nat.sqrt (2 * 4 ^ (1 + 3)) = 22
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3)))
        = [true, true, false, true, false, false, false]
    ∧ bits (1 + 7) (Nat.sqrt (2 * 4 ^ (1 + 3)))
        = [false, true, true, false, true, false, false, false]
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3))) ≠ []
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3)))
        ≠ bits (1 + 7) (Nat.sqrt (2 * 4 ^ (1 + 3)))) := by
  sorry

end ShiTM
