import «AMPUNI-unary-log-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2 ShiTMUnaryLog
namespace ShiTMScaledLog

/-- A fixed number of pushes is one TM2 statement step. -/
def pushCounter : Nat → Stmt Gam Label State → Stmt Gam Label State
  | 0, q => q
  | k + 1, q => .push .counter (fun _ => true) (pushCounter k q)

theorem update_counter (b : Bool) (src dst ctr zs : List Bool) :
    Function.update (storeFn b src dst ctr) .counter zs =
      storeFn b src dst zs := by
  cases b <;> funext k <;> cases k <;> simp [storeFn]

@[simp] theorem get_other (b : Bool) (src dst ctr : List Bool) :
    storeFn b src dst ctr (other b) = dst := by
  cases b <;> rfl

@[simp] theorem update_other (b : Bool) (src dst ctr zs : List Bool) :
    Function.update (storeFn b src dst ctr) (other b) zs =
      storeFn b src zs ctr := by
  cases b <;> funext k <;> cases k <;> simp [storeFn, other, data]

theorem stepAux_pushCounter (k : Nat) (q : Stmt Gam Label State)
    (v : State) (b : Bool) (src dst ctr : List Bool) :
    stepAux (pushCounter k q) v (storeFn b src dst ctr) =
      stepAux q v
        (storeFn b src dst (List.replicate k true ++ ctr)) := by
  induction k generalizing ctr with
  | zero => rfl
  | succ k ih =>
      simp only [pushCounter, stepAux, update_counter]
      rw [ih]
      congr 2
      simp only [List.replicate_succ', List.append_assoc,
        List.cons_append, List.nil_append]
      cases b <;> simp [storeFn]

/-- Each productive halving pass adds `copies` counter tokens. The final
step adds `offset` tokens and halts with a reset finite state. -/
def machine (copies offset : Nat) : Label → Stmt Gam Label State
  | .scan b => ShiTMUnaryLog.machine (.scan b)
  | .check b => .pop (other b) (fun v x => (x, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (other b) (fun _ => true)
          (pushCounter copies
            (.load (fun v => (v.1, true))
              (.goto (fun _ => .scan (!b))))))
        (.goto (fun _ => .done)))
  | .done => .load (fun _ => (none, true))
      (pushCounter offset .halt)

abbrev run (copies offset : Nat) :=
  ShiTMSubroutine.run (machine copies offset)

theorem scan_first (copies offset : Nat) (b : Bool)
    (v : Option Bool) (xs ys ctr : List Bool) :
    run copies offset
      (some (cfg (.scan b) b v true (true :: xs) ys ctr)) =
      some (cfg (.scan b) b (some true) false xs ys ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine,
      ShiTMUnaryLog.machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem scan_second (copies offset : Nat) (b : Bool)
    (v : Option Bool) (xs ys ctr : List Bool) :
    run copies offset
      (some (cfg (.scan b) b v false (true :: xs) ys ctr)) =
      some (cfg (.scan b) b (some true) true xs (true :: ys) ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine,
      ShiTMUnaryLog.machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem scan_end (copies offset : Nat) (b : Bool)
    (v : Option Bool) (parity : Bool) (ys ctr : List Bool) :
    run copies offset
      (some (cfg (.scan b) b v parity [] ys ctr)) =
      some (cfg (.check b) b none (!parity) [] ys ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine,
      ShiTMUnaryLog.machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem check_nonempty (copies offset : Nat) (b : Bool)
    (v : Option Bool) (parity : Bool) (ys ctr : List Bool) :
    run copies offset
      (some (cfg (.check b) b v parity [] (true :: ys) ctr)) =
      some (cfg (.scan (!b)) (!b) (some true) true
        (true :: ys) [] (List.replicate copies true ++ ctr)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine,
    step, stepAux, get_other, update_other]
  rw [stepAux_pushCounter]
  simp [stepAux]
  cases b <;> rfl

theorem check_empty (copies offset : Nat) (b : Bool)
    (v : Option Bool) (parity : Bool) (ctr : List Bool) :
    run copies offset
      (some (cfg (.check b) b v parity [] [] ctr)) =
      some (cfg .done b none parity [] [] ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine,
      step, stepAux, storeFn, data, other] <;>
    (funext k; cases k <;> simp)

end ShiTMScaledLog
