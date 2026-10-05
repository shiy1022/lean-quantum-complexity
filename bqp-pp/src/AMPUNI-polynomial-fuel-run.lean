import «AMPUNI-polynomial-fuel-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPolynomialFuel
open ShiTMFuel

/-- Exact time for the remaining multiplication stages and their transfers. -/
def work : Nat → Nat → Nat → Nat
  | 0, n, m => m * (2 * n + 3) + 2
  | r + 1, n, m =>
      m * (2 * n + 3) + 2 + (m * (n + 1) + 1) + work r n (m * (n + 1))

theorem stages_run (d k r : Nat) (hr : r ≤ d) (m : Nat)
    (xs : List Bool) (v : State) :
    (run d k)^[work r xs.length m]
      (some (cfg (stage ⟨r, by omega⟩ .outer) v xs [] (List.replicate m true) [])) =
      some (cfg done none xs [] []
        (List.replicate (m * (xs.length + 1) ^ (r + 1)) true)) := by
  induction r generalizing m v with
  | zero =>
      have hs := stage_run d k ⟨0, by omega⟩ m xs v
      have he : (run d k)^[1]
          (some (cfg (stage ⟨0, by omega⟩ .done) none xs [] []
            (List.replicate (m * (xs.length + 1)) true))) =
          some (cfg done none xs [] []
            (List.replicate (m * (xs.length + 1)) true)) := rfl
      have h := ShiTMFuel.iterTwo (run d k) _ _ _ _ _ hs he
      simpa [work, Nat.add_assoc] using h
  | succ r ih =>
      let i : Fin (d + 1) := ⟨r + 1, by omega⟩
      let b := m * (xs.length + 1)
      have hs := stage_run d k i m xs v
      have he : (run d k)^[1]
          (some (cfg (stage i .done) none xs [] [] (List.replicate b true))) =
          some (cfg (transfer i) none xs [] [] (List.replicate b true)) := by
        simp [run, ShiTMSubroutine.run, cfg, stage, machine, step, stepAux, i]
      have ht := transfer_run d k i (List.replicate b true) xs [] none
      simp only [List.length_replicate, List.append_nil] at ht
      have hi := ih (by omega) b none
      have hprev : previous i = (⟨r, by omega⟩ : Fin (d + 1)) := by
        apply Fin.ext
        simp [previous, i]
      rw [hprev] at ht
      have h := ShiTMFuel.iterTwo (run d k) _ _ _ _ _
        (ShiTMFuel.iterTwo (run d k) _ _ _ _ _
          (ShiTMFuel.iterTwo (run d k) _ _ _ _ _ hs he) ht) hi
      have hf : b * (xs.length + 1) ^ (r + 1) =
          m * (xs.length + 1) ^ (r + 1 + 1) := by
        dsimp [b]
        rw [pow_succ]
        ring
      simpa only [work, hf, show m * (2 * xs.length + 3) + 1 + 1 =
        m * (2 * xs.length + 3) + 2 by omega] using h

/-- Construct a monomial fuel supply from arbitrary raw Boolean input,
restoring the input exactly and emptying all work stacks. -/
theorem fuel_run (d k : Nat) (xs : List Bool) :
    (run d k)^[1 + work d xs.length k]
      (some (cfg init none xs [] [] [])) =
      some (cfg done none xs [] []
        (List.replicate (k * (xs.length + 1) ^ (d + 1)) true)) := by
  exact ShiTMFuel.iterTwo (run d k) _ _ _ _ _
    (show (run d k)^[1] _ = _ from init_step d k xs)
    (stages_run d k d le_rfl k xs none)

end ShiTMPolynomialFuel
