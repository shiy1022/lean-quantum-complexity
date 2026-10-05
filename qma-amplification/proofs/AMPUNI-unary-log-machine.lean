import «AMPUNI-unary-log-cost»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMUnaryLog

inductive Stack where
  | a | b | counter
  deriving DecidableEq

inductive Label where
  | scan (direction : Bool)
  | check (direction : Bool)
  | done
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.a, .b, .counter]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList
  [.scan false, .scan true, .check false, .check true, .done]
  (by intro l; cases l with
    | scan b => cases b <;> simp
    | check b => cases b <;> simp
    | done => simp)

abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool × Bool

def data (b : Bool) : Stack := if b then .b else .a
def other (b : Bool) : Stack := data (!b)

def storeFn (b : Bool) (source target counter : List Bool) :
    ∀ k : Stack, List (Gam k) :=
  match b with
  | false => fun
      | .a => source
      | .b => target
      | .counter => counter
  | true => fun
      | .a => target
      | .b => source
      | .counter => counter

/-- The two data stacks alternate roles after each productive pass. The
counter receives one token exactly when a halving pass produced a token. -/
def machine : Label → Stmt Gam Label State
  | .scan b => .pop (data b) (fun v x => (x, !v.2))
      (.branch (fun v => v.1.isSome)
        (.branch (fun v => v.2)
          (.push (other b) (fun _ => true)
            (.goto (fun _ => .scan b)))
          (.goto (fun _ => .scan b)))
        (.goto (fun _ => .check b)))
  | .check b => .pop (other b) (fun v x => (x, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (other b) (fun _ => true)
          (.push .counter (fun _ => true)
            (.load (fun v => (v.1, true))
              (.goto (fun _ => .scan (!b))))))
        (.goto (fun _ => .done)))
  | .done => .load (fun _ => (none, true))
      (.push .counter (fun _ => true)
        (.push .counter (fun _ => true)
          (.push .counter (fun _ => true) .halt)))

abbrev run := ShiTMSubroutine.run machine
def cfg (l : Label) (b : Bool) (register : Option Bool)
    (parity : Bool) (source target counter : List Bool) :
    Cfg Gam Label State :=
  ⟨some l, (register, parity), storeFn b source target counter⟩

theorem scan_first (b : Bool) (v : Option Bool)
    (xs ys ctr : List Bool) :
    run (some (cfg (.scan b) b v true (true :: xs) ys ctr)) =
      some (cfg (.scan b) b (some true) false xs ys ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem scan_second (b : Bool) (v : Option Bool)
    (xs ys ctr : List Bool) :
    run (some (cfg (.scan b) b v false (true :: xs) ys ctr)) =
      some (cfg (.scan b) b (some true) true xs (true :: ys) ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem scan_end (b : Bool) (v : Option Bool) (parity : Bool)
    (ys ctr : List Bool) :
    run (some (cfg (.scan b) b v parity [] ys ctr)) =
      some (cfg (.check b) b none (!parity) [] ys ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem check_nonempty (b : Bool) (v : Option Bool)
    (parity : Bool) (ys ctr : List Bool) :
    run (some (cfg (.check b) b v parity [] (true :: ys) ctr)) =
      some (cfg (.scan (!b)) (!b) (some true) true
        (true :: ys) [] (true :: ctr)) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

theorem check_empty (b : Bool) (v : Option Bool)
    (parity : Bool) (ctr : List Bool) :
    run (some (cfg (.check b) b v parity [] [] ctr)) =
      some (cfg .done b none parity [] [] ctr) := by
  cases b <;>
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
      storeFn, data, other] <;>
    (funext k; cases k <;> simp)

end ShiTMUnaryLog
