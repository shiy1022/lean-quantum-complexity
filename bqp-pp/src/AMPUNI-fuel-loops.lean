import «AMPUNI-fuel-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuel

private theorem iterStep (k n : Nat) (a b c : Cfg Gam Label State)
    (h : run k (some a) = some b) (hr : (run k)^[n] (some b) = some c) :
    (run k)^[n+1] (some a) = some c := by
  rw [Function.iterate_succ_apply, h, hr]

theorem count_cons (k : Nat) (v : State) (b : Bool) (xs tmp ctr fuel : List Bool) :
    run k (some (cfg .count v (b::xs) tmp ctr fuel)) =
      some (cfg .count (some b) xs (b::tmp) (true::ctr) fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]

theorem count_nil (k : Nat) (v : State) (tmp ctr fuel : List Bool) :
    run k (some (cfg .count v [] tmp ctr fuel)) =
      some (cfg .restoreInit none [] tmp ctr fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]

theorem count_run (k : Nat) (xs tmp ctr fuel : List Bool) (v : State) :
    (run k)^[xs.length+1] (some (cfg .count v xs tmp ctr fuel)) =
      some (cfg .restoreInit none [] (xs.reverse++tmp)
        (List.replicate xs.length true++ctr) fuel) := by
  induction xs generalizing tmp ctr v with
  | nil => simpa using count_nil k v tmp ctr fuel
  | cons b xs ih =>
      have h := iterStep k (xs.length+1) _ _ _ (count_cons k v b xs tmp ctr fuel)
        (ih (b::tmp) (true::ctr) (some b))
      simpa [List.reverse_cons, List.replicate_succ', List.append_assoc] using h

theorem restore_cons (k : Nat) (again next : Label)
    (hm : machine k again = restoreTo again next)
    (v : State) (b : Bool) (xs tmp ctr fuel : List Bool) :
    run k (some (cfg again v xs (b::tmp) ctr fuel)) =
      some (cfg again (some b) (b::xs) tmp ctr fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, step, hm, restoreTo, stepAux]

theorem restore_nil (k : Nat) (again next : Label)
    (hm : machine k again = restoreTo again next)
    (v : State) (xs ctr fuel : List Bool) :
    run k (some (cfg again v xs [] ctr fuel)) =
      some (cfg next none xs [] ctr fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, step, hm, restoreTo, stepAux]

theorem restore_run (k : Nat) (again next : Label)
    (hm : machine k again = restoreTo again next)
    (tmp xs ctr fuel : List Bool) (v : State) :
    (run k)^[tmp.length+1] (some (cfg again v xs tmp ctr fuel)) =
      some (cfg next none (tmp.reverse++xs) [] ctr fuel) := by
  induction tmp generalizing xs v with
  | nil => simpa using restore_nil k again next hm v xs ctr fuel
  | cons b tmp ih =>
      have h := iterStep k (tmp.length+1) _ _ _
        (restore_cons k again next hm v b xs tmp ctr fuel) (ih (b::xs) (some b))
      simpa [List.reverse_cons, List.append_assoc] using h

theorem scan_cons (k : Nat) (v : State) (b : Bool) (xs tmp ctr fuel : List Bool) :
    run k (some (cfg .scan v (b::xs) tmp ctr fuel)) =
      some (cfg .scan (some b) xs (b::tmp) ctr (List.replicate k true++fuel)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, stepAux_pushFuel]

theorem scan_nil (k : Nat) (v : State) (tmp ctr fuel : List Bool) :
    run k (some (cfg .scan v [] tmp ctr fuel)) =
      some (cfg .restore none [] tmp ctr fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]

theorem replicate_append (a b : Nat) (fuel : List Bool) :
    List.replicate a true ++ (List.replicate b true ++ fuel) =
      List.replicate (a+b) true ++ fuel := by
  rw [← List.append_assoc, ← List.replicate_add]

theorem scan_run (k : Nat) (xs tmp ctr fuel : List Bool) (v : State) :
    (run k)^[xs.length+1] (some (cfg .scan v xs tmp ctr fuel)) =
      some (cfg .restore none [] (xs.reverse++tmp) ctr
        (List.replicate (k*xs.length) true++fuel)) := by
  induction xs generalizing tmp fuel v with
  | nil => simpa using scan_nil k v tmp ctr fuel
  | cons b xs ih =>
      have h := iterStep k (xs.length+1) _ _ _ (scan_cons k v b xs tmp ctr fuel)
        (ih (b::tmp) (List.replicate k true++fuel) (some b))
      simpa [List.reverse_cons, List.append_assoc, replicate_append, Nat.mul_add] using h

end ShiTMFuel
