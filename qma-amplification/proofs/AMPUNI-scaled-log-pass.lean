import «AMPUNI-scaled-log-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2 ShiTMUnaryLog
namespace ShiTMScaledLog

theorem pairs_run (copies offset : Nat) (b : Bool) (k : Nat)
    (v : Option Bool) (xs ys ctr : List Bool) :
    (run copies offset)^[2 * k]
      (some (cfg (.scan b) b v true
        (List.replicate (2 * k) true ++ xs) ys ctr)) =
      some (cfg (.scan b) b (if k = 0 then v else some true) true
        xs (List.replicate k true ++ ys) ctr) := by
  induction k generalizing v ys with
  | zero => simp [cfg]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        Function.iterate_add_apply]
      have hrep : List.replicate (2 * k + 2) true =
          true :: true :: List.replicate (2 * k) true := by
        rw [show 2 * k + 2 = 2 + 2 * k by omega,
          List.replicate_add]
        rfl
      rw [hrep]
      change (run copies offset)^[2 * k]
        (run copies offset
          (run copies offset
            (some (cfg (.scan b) b v true
              (true :: true ::
                (List.replicate (2 * k) true ++ xs)) ys ctr)))) = _
      rw [scan_first, scan_second, ih]
      simp only [if_false, Nat.succ_ne_zero]
      simp [List.replicate_succ', List.append_assoc]

theorem even_pass (copies offset : Nat) (b : Bool) (k : Nat)
    (v : Option Bool) (ctr : List Bool) :
    (run copies offset)^[2 * k + 1]
      (some (cfg (.scan b) b v true
        (List.replicate (2 * k) true) [] ctr)) =
      some (cfg (.check b) b none false []
        (List.replicate k true) ctr) := by
  rw [show 2 * k + 1 = 1 + 2 * k by omega,
    Function.iterate_add_apply]
  simpa using congrArg (run copies offset)
      (pairs_run copies offset b k v [] [] ctr) |>.trans
    (scan_end copies offset b _ true _ _)

theorem odd_pass (copies offset : Nat) (b : Bool) (k : Nat)
    (v : Option Bool) (ctr : List Bool) :
    (run copies offset)^[2 * k + 2]
      (some (cfg (.scan b) b v true
        (List.replicate (2 * k + 1) true) [] ctr)) =
      some (cfg (.check b) b none true []
        (List.replicate k true) ctr) := by
  have hrep : List.replicate (2 * k + 1) true =
      List.replicate (2 * k) true ++ [true] := by
    rw [List.replicate_add]
    rfl
  rw [show 2 * k + 2 = 2 + 2 * k by omega,
    Function.iterate_add_apply, hrep, pairs_run]
  simp only [List.append_nil]
  change run copies offset
    (run copies offset
      (some (cfg (.scan b) b _ true [true]
        (List.replicate k true) ctr))) = _
  rw [scan_first, scan_end]
  rfl

theorem half_pass (copies offset : Nat) (b : Bool) (n : Nat)
    (v : Option Bool) (ctr : List Bool) :
    ∃ parity : Bool,
      (run copies offset)^[n + 1]
        (some (cfg (.scan b) b v true (List.replicate n true) [] ctr)) =
      some (cfg (.check b) b none parity []
        (List.replicate (n / 2) true) ctr) := by
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    refine ⟨false, ?_⟩
    simpa only [← hn] using
      even_pass copies offset b (n / 2) v ctr
  · have hn : n = 2 * (n / 2) + 1 := by omega
    refine ⟨true, ?_⟩
    have ht : 2 * (n / 2) + 2 = n + 1 := by omega
    simpa only [← hn, ht] using
      odd_pass copies offset b (n / 2) v ctr

end ShiTMScaledLog
