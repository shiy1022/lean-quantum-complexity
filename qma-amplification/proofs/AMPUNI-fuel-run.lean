import «AMPUNI-fuel-loops»
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuel

theorem iterTwo {A : Type} (f : A → A) (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) : f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

theorem outer_cons (k : Nat) (v : State) (b : Bool) (xs ctr fuel : List Bool) :
    run k (some (cfg .outer v xs [] (b::ctr) fuel)) =
      some (cfg .scan (some b) xs [] ctr (List.replicate k true++fuel)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, stepAux_pushFuel]

theorem outer_nil (k : Nat) (v : State) (xs fuel : List Bool) :
    run k (some (cfg .outer v xs [] [] fuel)) =
      some (cfg .done none xs [] [] fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]

/-- One outer iteration adds k times (input length + 1) fuel tokens and
restores the original input, including its bit order. -/
theorem round_run (k : Nat) (v : State) (b : Bool) (xs ctr fuel : List Bool) :
    (run k)^[2*xs.length+3] (some (cfg .outer v xs [] (b::ctr) fuel)) =
      some (cfg .outer none xs [] ctr
        (List.replicate (k*(xs.length+1)) true++fuel)) := by
  have h₀ : (run k)^[1] (some (cfg .outer v xs [] (b::ctr) fuel)) =
      some (cfg .scan (some b) xs [] ctr (List.replicate k true++fuel)) :=
    outer_cons k v b xs ctr fuel
  have h₁ := scan_run k xs [] ctr (List.replicate k true++fuel) (some b)
  simp only [List.append_nil, replicate_append] at h₁
  have h₂ := restore_run k .restore .outer rfl xs.reverse [] ctr
    (List.replicate (k*xs.length+k) true++fuel) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h := iterTwo (run k) _ _ _ _ _ (iterTwo (run k) _ _ _ _ _ h₀ h₁) h₂
  have ht : 1+(xs.length+1)+(xs.length+1) = 2*xs.length+3 := by omega
  simpa only [ht, Nat.mul_add, Nat.mul_one] using h

theorem outer_run (k m : Nat) (xs fuel : List Bool) (v : State) :
    (run k)^[m*(2*xs.length+3)+1]
      (some (cfg .outer v xs [] (List.replicate m true) fuel)) =
      some (cfg .done none xs [] []
        (List.replicate (m*(k*(xs.length+1))) true++fuel)) := by
  induction m generalizing fuel v with
  | zero => simpa using outer_nil k v xs fuel
  | succ m ih =>
      have h₀ := round_run k v true xs (List.replicate m true) fuel
      have h₁ := ih (List.replicate (k*(xs.length+1)) true++fuel) none
      have h := iterTwo (run k) _ _ _ _ _ h₀ h₁
      simpa [List.replicate_succ, replicate_append, Nat.succ_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem prepare_run (k : Nat) (xs fuel : List Bool) (v : State) :
    (run k)^[2*xs.length+3] (some (cfg .init v xs [] [] fuel)) =
      some (cfg .outer none xs [] (List.replicate (xs.length+1) true) fuel) := by
  have h₀ : (run k)^[1] (some (cfg .init v xs [] [] fuel)) =
      some (cfg .count v xs [] [true] fuel) := init_step k v xs [] [] fuel
  have h₁ := count_run k xs [] [true] fuel v
  simp only [List.append_nil, ← List.replicate_succ'] at h₁
  have h₂ := restore_run k .restoreInit .outer rfl xs.reverse []
    (List.replicate (xs.length+1) true) fuel none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h := iterTwo (run k) _ _ _ _ _ (iterTwo (run k) _ _ _ _ _ h₀ h₁) h₂
  have ht : 1+(xs.length+1)+(xs.length+1) = 2*xs.length+3 := by omega
  simpa only [ht] using h

/-- Raw Boolean input generates exactly the quadratic fuel budget. The two
work stacks are empty at exit and the original input is unchanged. -/
theorem fuel_run (k : Nat) (xs : List Bool) :
    (run k)^[(xs.length+2)*(2*xs.length+3)+1]
      (some (cfg .init none xs [] [] [])) =
      some (cfg .done none xs [] [] (List.replicate (k*(xs.length+1)^2) true)) := by
  have h₀ := prepare_run k xs [] none
  have h₁ := outer_run k (xs.length+1) xs [] none
  have h := iterTwo (run k) _ _ _ _ _ h₀ h₁
  have ht : 2*xs.length+3+((xs.length+1)*(2*xs.length+3)+1) =
      (xs.length+2)*(2*xs.length+3)+1 := by ring
  have hf : (xs.length+1)*(k*(xs.length+1)) = k*(xs.length+1)^2 := by ring
  simpa only [ht, hf, List.append_nil] using h

theorem fuel_cost_bound (xs : List Bool) :
    (xs.length+2)*(2*xs.length+3)+1 ≤ 7*(xs.length+1)^2 := by
  nlinarith

end ShiTMFuel
