-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow ShiClass ShiBQP

namespace ShiBQP

theorem gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one :
    -- (1) ANY per-gate predicate counts at most the gate count.
    (∀ (n : ℕ) (p : Instr n → Bool) (c : Layered n),
        c.flatten.countP p ≤ (c.map List.length).sum)
    -- (2) and for a well-formed circuit the gate count is at most depth times width.
  ∧ (∀ (n : ℕ) (c : Layered n), (∀ l ∈ c, LayerOk l) →
        (c.map List.length).sum ≤ depth c * n)
    -- (3) hence for a well-formed family with depth/ancilla bound `q`, every gate-predicate
    -- count is at most the EXPLICIT polynomial `q * (X + q + 1)`, evaluated at `n`.
  ∧ (∀ F : Family, WellFormed F → ∀ q : Polynomial ℕ,
        (∀ n : ℕ, depth (F.circ n) ≤ q.eval n) → (∀ n : ℕ, F.anc n ≤ q.eval n) →
        ∀ (p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool) (n : ℕ),
          (F.circ n).flatten.countP (p n) ≤ (q * (Polynomial.X + q + 1)).eval n)
    -- (4) POLYNOMIAL DOMINATION.
  ∧ (∀ r : Polynomial ℕ, ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n → 3 * r.eval n + 10 ≤ n ^ k)
    -- (5) and the `n ≥ 2` side condition in (4) is FORCED: at `n = 0` and `n = 1` the
    -- inequality fails for EVERY `r` and EVERY `k`.
  ∧ (∀ (r : Polynomial ℕ) (k : ℕ),
        ¬ (3 * r.eval 0 + 10 ≤ 0 ^ k) ∧ ¬ (3 * r.eval 1 + 10 ≤ 1 ^ k))
    -- (6) COMBINED: for a well-formed, poly-bounded family, ONE `k` works for every
    -- input length `n ≥ 2`.
  ∧ (∀ F : Family, WellFormed F → PolyBounded F →
        ∀ p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool, ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
          3 * ((F.circ n).flatten.countP (p n)) + 10 ≤ n ^ k)
    -- (7) the Hadamard instance of (6), spelled out.
  ∧ (∀ F : Family, WellFormed F → PolyBounded F → ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
        3 * ((F.circ n).flatten.countP
              (fun g => match g with | Instr.h _ => true | _ => false)) + 10 ≤ n ^ k) := by
  sorry

end ShiBQP
