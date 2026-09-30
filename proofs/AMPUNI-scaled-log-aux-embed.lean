import «AMPUNI-scaled-log-entry»
import «AMPUNI-repeat-controller»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMScaledLogAux

open ShiTMUnaryLog
abbrev Aux := ShiTMRepeatController.Aux
abbrev Gam (_ : Aux) := Bool

def index : ShiTMUnaryLog.Stack → Aux
  | .a => ShiTMRepeatController.scratch
  | .b => ShiTMRepeatController.header false
  | .counter => ShiTMRepeatController.counter

/-- Embed the three loader stacks in the controller's four auxiliary
stacks. The active `true` header bank is kept separately and never touched. -/
def embedStacks (S : ∀ k : ShiTMUnaryLog.Stack,
    List (ShiTMUnaryLog.Gam k)) (header : List Bool) :
    ∀ h : Aux, List (Gam h) := fun h =>
  if h = ShiTMRepeatController.scratch then S .a
  else if h = ShiTMRepeatController.header false then S .b
  else if h = ShiTMRepeatController.header true then header
  else S .counter

@[simp] theorem get_index (S : ∀ k : ShiTMUnaryLog.Stack,
    List (ShiTMUnaryLog.Gam k)) (header : List Bool)
    (k : ShiTMUnaryLog.Stack) :
    embedStacks S header (index k) = S k := by
  cases k <;> simp [embedStacks, index,
    ShiTMRepeatController.scratch,
    ShiTMRepeatController.header,
    ShiTMRepeatController.counter]

private theorem update_index (S : ∀ k : ShiTMUnaryLog.Stack,
    List (ShiTMUnaryLog.Gam k)) (header : List Bool)
    (k : ShiTMUnaryLog.Stack) (xs : List Bool) :
    Function.update (embedStacks S header) (index k) xs =
      embedStacks (Function.update S k xs) header := by
  cases k <;> funext h <;> fin_cases h <;>
    simp [embedStacks, index, ShiTMRepeatController.scratch,
      ShiTMRepeatController.header, ShiTMRepeatController.counter]

def cfg (header : List Bool)
    (c : Cfg ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
      ShiTMUnaryLog.State) :
    Cfg Gam ShiTMUnaryLog.Label ShiTMUnaryLog.State :=
  ⟨c.l, c.var, embedStacks c.stk header⟩

def stmt : Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
    ShiTMUnaryLog.State →
    Stmt Gam ShiTMUnaryLog.Label ShiTMUnaryLog.State
  | .push k f q => .push (index k) f (stmt q)
  | .peek k f q => .peek (index k) f (stmt q)
  | .pop k f q => .pop (index k) f (stmt q)
  | .load f q => .load f (stmt q)
  | .branch f a b => .branch f (stmt a) (stmt b)
  | .goto f => .goto f
  | .halt => .halt

theorem stepAux_stmt (q : Stmt ShiTMUnaryLog.Gam
    ShiTMUnaryLog.Label ShiTMUnaryLog.State)
    (v : ShiTMUnaryLog.State)
    (S : ∀ k : ShiTMUnaryLog.Stack,
      List (ShiTMUnaryLog.Gam k)) (header : List Bool) :
    stepAux (stmt q) v (embedStacks S header) =
      cfg header (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [stmt, stepAux, get_index]
      rw [update_index]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simpa only [stmt, stepAux, get_index] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [stmt, stepAux, get_index]
      rw [update_index]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f a b iha ihb =>
      simp only [stmt, stepAux]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => rfl
  | halt => rfl

def machine (copies offset : Nat) :
    ShiTMUnaryLog.Label →
      Stmt Gam ShiTMUnaryLog.Label ShiTMUnaryLog.State :=
  fun l => stmt (ShiTMScaledLog.machine copies offset l)

theorem run_frame (copies offset : Nat) (header : List Bool)
    (c : Option (Cfg ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
      ShiTMUnaryLog.State)) :
    ShiTMSubroutine.run (machine copies offset) (c.map (cfg header)) =
      ((ShiTMScaledLog.run copies offset) c).map (cfg header) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt
            (ShiTMScaledLog.machine copies offset l)) v
            (embedStacks S header)) = _
          rw [stepAux_stmt]
          rfl

theorem run_iter_frame (copies offset : Nat) (header : List Bool)
    (n : Nat) (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    (ShiTMSubroutine.run (machine copies offset))^[n]
      (c.map (cfg header)) =
    (((ShiTMScaledLog.run copies offset)^[n] c).map (cfg header)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, run_frame]
      exact ih _

/-- The same stack embedding works for any program on the loader's three
stacks, including a version whose finish label is a return point. -/
def liftMachine (M : ShiTMUnaryLog.Label →
    Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
      ShiTMUnaryLog.State) :
    ShiTMUnaryLog.Label →
      Stmt Gam ShiTMUnaryLog.Label ShiTMUnaryLog.State :=
  fun l => stmt (M l)

theorem run_frame_any
    (M : ShiTMUnaryLog.Label →
      Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
        ShiTMUnaryLog.State)
    (header : List Bool)
    (c : Option (Cfg ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
      ShiTMUnaryLog.State)) :
    ShiTMSubroutine.run (liftMachine M) (c.map (cfg header)) =
      ((ShiTMSubroutine.run M) c).map (cfg header) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt (M l)) v
            (embedStacks S header)) = _
          rw [stepAux_stmt]
          rfl

theorem run_iter_frame_any
    (M : ShiTMUnaryLog.Label →
      Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
        ShiTMUnaryLog.State)
    (header : List Bool) (n : Nat)
    (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    (ShiTMSubroutine.run (liftMachine M))^[n]
      (c.map (cfg header)) =
    (((ShiTMSubroutine.run M)^[n] c).map (cfg header)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, run_frame_any]
      exact ih _

end ShiTMScaledLogAux
