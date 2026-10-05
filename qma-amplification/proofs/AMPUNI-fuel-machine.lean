import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuel

inductive Stack where
  | input | scratch | counter | fuel
  deriving DecidableEq
inductive Label where
  | init | count | restoreInit | outer | scan | restore | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input, .scratch, .counter, .fuel]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList
  [.init, .count, .restoreInit, .outer, .scan, .restore, .done]
  (by intro l; cases l <;> simp)
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool

def storeFn (xs tmp ctr fuel : List Bool) : ∀ k : Stack, List (Gam k)
  | .input => xs
  | .scratch => tmp
  | .counter => ctr
  | .fuel => fuel

@[simp] theorem stacks_input (xs tmp ctr fuel : List Bool) : storeFn xs tmp ctr fuel .input = xs := rfl
@[simp] theorem stacks_scratch (xs tmp ctr fuel : List Bool) : storeFn xs tmp ctr fuel .scratch = tmp := rfl
@[simp] theorem stacks_counter (xs tmp ctr fuel : List Bool) : storeFn xs tmp ctr fuel .counter = ctr := rfl
@[simp] theorem stacks_fuel (xs tmp ctr fuel : List Bool) : storeFn xs tmp ctr fuel .fuel = fuel := rfl

@[simp] theorem update_input (xs tmp ctr fuel ys : List Bool) :
    Function.update (storeFn xs tmp ctr fuel) .input ys = storeFn ys tmp ctr fuel := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_scratch (xs tmp ctr fuel ys : List Bool) :
    Function.update (storeFn xs tmp ctr fuel) .scratch ys = storeFn xs ys ctr fuel := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_counter (xs tmp ctr fuel ys : List Bool) :
    Function.update (storeFn xs tmp ctr fuel) .counter ys = storeFn xs tmp ys fuel := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_fuel (xs tmp ctr fuel ys : List Bool) :
    Function.update (storeFn xs tmp ctr fuel) .fuel ys = storeFn xs tmp ctr ys := by
  funext k; cases k <;> simp [storeFn]

/-- A fixed number of pushes is a finite statement, not an extra loop. -/
def pushFuel : Nat → Stmt Gam Label State → Stmt Gam Label State
  | 0, q => q
  | k+1, q => .push .fuel (fun _ => true) (pushFuel k q)

theorem stepAux_pushFuel (k : Nat) (q : Stmt Gam Label State) (v : State)
    (xs tmp ctr fuel : List Bool) :
    stepAux (pushFuel k q) v (storeFn xs tmp ctr fuel) =
      stepAux q v (storeFn xs tmp ctr (List.replicate k true ++ fuel)) := by
  induction k generalizing fuel with
  | zero => rfl
  | succ k ih =>
      simp only [pushFuel, stepAux, stacks_fuel, update_fuel]
      rw [ih]
      congr 2
      simp only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

def restoreTo (again next : Label) : Stmt Gam Label State :=
  .pop .scratch (fun _ x => x)
    (.branch Option.isSome
      (.push .input (fun v => v.getD false) (.goto (fun _ => again)))
      (.goto (fun _ => next)))

def machine (k : Nat) : Label → Stmt Gam Label State
  | .init => .push .counter (fun _ => true) (.goto (fun _ => .count))
  | .count => .pop .input (fun _ x => x)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (.push .counter (fun _ => true) (.goto (fun _ => .count))))
        (.goto (fun _ => .restoreInit)))
  | .restoreInit => restoreTo .restoreInit .outer
  | .outer => .pop .counter (fun _ x => x)
      (.branch Option.isSome (pushFuel k (.goto (fun _ => .scan)))
        (.goto (fun _ => .done)))
  | .scan => .pop .input (fun _ x => x)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (pushFuel k (.goto (fun _ => .scan))))
        (.goto (fun _ => .restore)))
  | .restore => restoreTo .restore .outer
  | .done => .halt

abbrev run (k : Nat) := ShiTMSubroutine.run (machine k)
def cfg (l : Label) (v : State) (xs tmp ctr fuel : List Bool) : Cfg Gam Label State :=
  ⟨some l, v, storeFn xs tmp ctr fuel⟩

/-- The only variable-length work is counting, scanning, and restoring input. -/
theorem init_step (k : Nat) (v : State) (xs tmp ctr fuel : List Bool) :
    run k (some (cfg .init v xs tmp ctr fuel)) =
      some (cfg .count v xs tmp (true::ctr) fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]

end ShiTMFuel
