import «AMPUNI-scaled-log-pass»
import «AMPUNI-unary-log-cost»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2 ShiTMUnaryLog
namespace ShiTMScaledLog

private theorem counter_append (copies k : Nat)
    (ctr : List Bool) :
    List.replicate (copies * k) true ++
        (List.replicate copies true ++ ctr) =
      List.replicate (copies * (k + 1)) true ++ ctr := by
  rw [← List.append_assoc, ← List.replicate_add]
  congr 1

/-- The scaled finite machine adds `copies` unary tokens per productive
halving pass; the same linear work bound applies. -/
theorem full_run (copies offset n : Nat) (b : Bool)
    (v : Option Bool) (ctr : List Bool) :
    ∃ direction parity : Bool,
      (run copies offset)^[ShiTMUnaryLogCost.work n]
        (some (cfg (.scan b) b v true
          (List.replicate n true) [] ctr)) =
      some (cfg .done direction none parity [] []
        (List.replicate (copies * Nat.log 2 n) true ++ ctr)) := by
  induction n using Nat.strong_induction_on generalizing b v ctr with
  | h n ih =>
      obtain ⟨parity, hpass⟩ :=
        half_pass copies offset b n v ctr
      by_cases hsmall : n < 2
      · have hzero : n / 2 = 0 := by omega
        have hlog := ShiTMUnaryLogCost.log_zero_of_small hsmall
        refine ⟨b, parity, ?_⟩
        rw [ShiTMUnaryLogCost.work_small hsmall,
          show n + 2 = 1 + (n + 1) by omega,
          Function.iterate_add_apply, hpass, hzero]
        simpa [hlog] using
          check_empty copies offset b none parity ctr
      · have hn : 2 ≤ n := by omega
        have hlt : n / 2 < n :=
          Nat.div_lt_self (by omega) (by decide)
        have hpos : 0 < n / 2 := Nat.div_pos hn (by decide)
        have hrep : List.replicate (n / 2) true =
            true :: List.replicate (n / 2 - 1) true := by
          cases hq : n / 2 with
          | zero => simp [hq] at hpos
          | succ k => rfl
        have hstart :
            (run copies offset)^[n + 2]
              (some (cfg (.scan b) b v true
                (List.replicate n true) [] ctr)) =
            some (cfg (.scan (!b)) (!b) (some true) true
              (List.replicate (n / 2) true) []
                (List.replicate copies true ++ ctr)) := by
          rw [show n + 2 = 1 + (n + 1) by omega,
            Function.iterate_add_apply, hpass, hrep]
          simpa only [Function.iterate_one] using
            check_nonempty copies offset b none parity
              (List.replicate (n / 2 - 1) true) ctr
        obtain ⟨direction, parity', hrest⟩ :=
          ih (n / 2) hlt (!b) (some true)
            (List.replicate copies true ++ ctr)
        refine ⟨direction, parity', ?_⟩
        rw [ShiTMUnaryLogCost.work_large hn,
          show n + 2 + ShiTMUnaryLogCost.work (n / 2) =
            ShiTMUnaryLogCost.work (n / 2) + (n + 2) by omega,
          Function.iterate_add_apply, hstart, hrest,
          ShiTMUnaryLogCost.log_step hn]
        exact congrArg
          (fun xs => some (cfg .done direction none parity' [] [] xs))
          (counter_append copies (Nat.log 2 (n / 2)) ctr)

end ShiTMScaledLog
