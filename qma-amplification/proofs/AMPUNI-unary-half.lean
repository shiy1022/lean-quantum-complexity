import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMUnaryHalf

inductive Stack where
  | source | target
  deriving DecidableEq

inductive Label where
  | scan | done
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.source, .target]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan, .done]
  (by intro l; cases l <;> simp)

abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool × Bool

def storeFn (source target : List Bool) : ∀ k : Stack, List (Gam k)
  | .source => source
  | .target => target

@[simp] theorem update_source (xs ys zs : List Bool) :
    Function.update (storeFn xs ys) .source zs = storeFn zs ys := by
  funext k; cases k <;> simp [storeFn]

@[simp] theorem update_target (xs ys zs : List Bool) :
    Function.update (storeFn xs ys) .target zs = storeFn xs zs := by
  funext k; cases k <;> simp [storeFn]

/-- Pop a unary source; push one target token for each even-numbered pop. -/
def machine : Label → Stmt Gam Label State
  | .scan => .pop .source (fun v x => (x, !v.2))
      (.branch (fun v => v.1.isSome)
        (.branch (fun v => v.2)
          (.push .target (fun _ => true) (.goto (fun _ => .scan)))
          (.goto (fun _ => .scan)))
        (.goto (fun _ => .done)))
  | .done => .halt

abbrev run := ShiTMSubroutine.run machine
def cfg (l : Label) (register : Option Bool) (parity : Bool)
    (source target : List Bool) :
    Cfg Gam Label State :=
  ⟨some l, (register, parity), storeFn source target⟩

theorem scan_first (v : Option Bool) (xs ys : List Bool) :
    run (some (cfg .scan v true (true :: xs) ys)) =
      some (cfg .scan (some true) false xs ys) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem scan_second (v : Option Bool) (xs ys : List Bool) :
    run (some (cfg .scan v false (true :: xs) ys)) =
      some (cfg .scan (some true) true xs (true :: ys)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem scan_end (v : Option Bool) (parity : Bool) (ys : List Bool) :
    run (some (cfg .scan v parity [] ys)) =
      some (cfg .done none (!parity) [] ys) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

/-- Exactly two input pops per produced unary token. -/
theorem pairs_run (k : Nat) (v : Option Bool) (xs ys : List Bool) :
    run^[2 * k]
      (some (cfg .scan v true (List.replicate (2 * k) true ++ xs) ys)) =
        some (cfg .scan (if k = 0 then v else some true) true xs
          (List.replicate k true ++ ys)) := by
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
      change run^[2 * k]
        (run (run (some (cfg .scan v true
          (true :: true :: (List.replicate (2 * k) true ++ xs)) ys)))) = _
      rw [scan_first, scan_second, ih]
      simp only [if_false, Nat.succ_ne_zero]
      simp [List.replicate_succ', List.append_assoc]

theorem even_run (k : Nat) (v : Option Bool) (ys : List Bool) :
    run^[2 * k + 1]
      (some (cfg .scan v true (List.replicate (2 * k) true) ys)) =
        some (cfg .done none false [] (List.replicate k true ++ ys)) := by
  rw [show 2 * k + 1 = 1 + 2 * k by omega,
    Function.iterate_add_apply]
  simpa using congrArg run (pairs_run k v [] ys) |>.trans
    (scan_end _ true _)

theorem odd_run (k : Nat) (v : Option Bool) (ys : List Bool) :
    run^[2 * k + 2]
      (some (cfg .scan v true (List.replicate (2 * k + 1) true) ys)) =
        some (cfg .done none true [] (List.replicate k true ++ ys)) := by
  have hrep : List.replicate (2 * k + 1) true =
      List.replicate (2 * k) true ++ [true] := by
    rw [show 2 * k + 1 = 2 * k + 1 by rfl, List.replicate_add]
    rfl
  rw [show 2 * k + 2 = 2 + 2 * k by omega,
    Function.iterate_add_apply, hrep, pairs_run]
  change run (run (some (cfg .scan _ true [true]
    (List.replicate k true ++ ys)))) = _
  rw [scan_first, scan_end]
  rfl

/-- A complete pass computes unary floor division by two in exactly `n+1`
machine steps; the final step observes the empty source stack. -/
theorem half_run (n : Nat) (v : Option Bool) (ys : List Bool) :
    ∃ parity : Bool,
      run^[n + 1]
        (some (cfg .scan v true (List.replicate n true) ys)) =
          some (cfg .done none parity []
            (List.replicate (n / 2) true ++ ys)) := by
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    refine ⟨false, ?_⟩
    simpa only [← hn] using even_run (n / 2) v ys
  · have hn : n = 2 * (n / 2) + 1 := by omega
    refine ⟨true, ?_⟩
    have ht : 2 * (n / 2) + 2 = n + 1 := by omega
    simpa only [← hn, ht] using odd_run (n / 2) v ys

end ShiTMUnaryHalf
