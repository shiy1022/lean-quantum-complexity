import «AMPUNI-constructive-valid-rounds»
import «AMPUNI-constructive-cost-polynomial»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section
namespace ShiTMConstructiveConcrete
open ShiClassQMA ShiClassQMAU ShiQMAVariableRounds ShiQMAConstructiveSchedule Polynomial

/-- On every valid input, the complete finite machine, including its round
counter loader, halts with the intended encoding within one polynomial
bound. The final parity bit is arbitrary; the clock's cleanup resets it. -/
theorem constructive_valid_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ k : Nat, ∃ T : Polynomial ℕ, ∀ n : Nat,
      ∃ steps : Nat, ∃ v : (finiteMachine k p).σ,
      ∃ S : ∀ j, List ((finiteMachine k p).Γ j),
        (ShiTMSubroutine.run (finiteMachine k p).m)^[steps]
          (some (Turing.initList (finiteMachine k p)
            (ShiBQP.encNat n ++ encQMAFamilyAt F n))) =
          some ⟨none, v, S⟩ ∧
        S (finiteMachine k p).k₁ =
          encQMAFamilyAt (constructiveFamily F p) n ∧
        steps ≤ T.eval n := by
  obtain ⟨k, C, hvalid⟩ := constructive_valid_rounds
  obtain ⟨T, hT⟩ := constructive_preloadedCost_polyBounded F p C hwell hpoly
  refine ⟨k, T + Polynomial.C 7 * X + Polynomial.C 14, ?_⟩
  intro n
  let raw := ShiBQP.encNat n ++ encQMAFamilyAt F n
  let S₀ := (Turing.initList (finiteMachine k p) raw).stk
  have hi : S₀ (.inl (source k).k₀) = raw := by
    simp [S₀, Turing.initList, finiteMachine] <;> rfl
  have hbase : ∀ j : (source k).K, j ≠ (source k).k₀ →
      S₀ (.inl j) = [] := by
    intro j hj
    simp [S₀, Turing.initList, finiteMachine, hj]
  have haux : ∀ h : ShiTMRepeatController.Aux, S₀ (.inr h) = [] := by
    intro h
    simp [S₀, Turing.initList, finiteMachine]
  obtain ⟨times, htimes, t, parity, S, hr, hout, _, _, hcost⟩ :=
    hvalid F p n S₀ hi hbase haux
  refine ⟨2 * n + 3 + (ShiTMUnaryLogCost.work (n + 1) + n + 3) + t,
    (none, (parity, (source k).initialState.2)), S, ?_, hout, ?_⟩
  · exact hr
  · have ht := hcost.trans (hT n times htimes)
    have hwork := ShiTMUnaryLogCost.work_le_linear (n + 1)
    simp only [eval_add, eval_mul, eval_C, eval_X]
    omega

end ShiTMConstructiveConcrete
