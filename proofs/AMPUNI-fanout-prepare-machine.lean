import «AMPUNI-retained-finite»
import «AMPUNI-fanout-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMFanoutPrepare
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

abbrev port (k : Fin 3) : TopK := .inl (ShiTMFanout.port k)
abbrev source (h : Fin 3) : TopK := .inr ⟨h.val, by omega⟩
abbrev scratch : TopK := .inl ShiTMFanout.scratch

def countCoeff (h : Fin 3) : Nat := if h = 0 then 1 else 0
def baseCoeff (second : Bool) (h : Fin 3) : Nat :=
  if h = 1 then 3 else if second then 2 else 1
def seed (second : Bool) : Nat := if second then 2 else 1

inductive Label where
  | clear (k : Fin 3) | start | copy (h : Fin 3) | restore (h : Fin 3) | finished
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList
  [.clear 0, .clear 1, .clear 2, .start, .copy 0, .copy 1, .copy 2,
    .restore 0, .restore 1, .restore 2, .finished]
  (by intro l; cases l with
      | clear k => fin_cases k <;> simp
      | start => simp
      | copy h => fin_cases h <;> simp
      | restore h => fin_cases h <;> simp
      | finished => simp)

def afterClear (k : Fin 3) : Label :=
  if k = 0 then .clear 1 else if k = 1 then .clear 2 else .start

def afterField (h : Fin 3) : Label :=
  if h = 0 then .copy 1 else if h = 1 then .copy 2 else .finished

/-- Only fixed coefficients (at most three) are used by the machine. -/
def pushMarks (k : Fin 3) : Nat → Stmt TopGam Label Sig → Stmt TopGam Label Sig
  | 0, q => q
  | n+1, q => .push (port k) (cst .mark) (pushMarks k n q)

theorem pushMarks_step (k : Fin 3) (n : Nat) (q : Stmt TopGam Label Sig)
    (v : Sig) (S : ∀ j, List (TopGam j)) :
    stepAux (pushMarks k n q) v S =
      stepAux q v (Function.update S (port k)
        (List.replicate n Cell.mark ++ S (port k))) := by
  induction n generalizing S with
  | zero => simp [pushMarks]
  | succ n ih =>
      simp only [pushMarks, stepAux, cst]
      rw [ih]
      simp [List.replicate_add, List.append_assoc, Function.update_idem]

def machine (second : Bool) : Label → Stmt TopGam Label Sig
  | .clear k => .pop (port k) pop
      (.branch isSome (.goto (fun _ => .clear k)) (.goto (fun _ => afterClear k)))
  | .start => pushMarks 2 (seed second) (.goto (fun _ => .copy 0))
  | .copy h => .pop (source h) pop
      (.branch isSome
        (.push scratch (cst .mark)
          (pushMarks 0 (countCoeff h)
            (pushMarks 2 (baseCoeff second h) (.goto (fun _ => .copy h)))))
        (.goto (fun _ => .restore h)))
  | .restore h => .pop scratch pop
      (.branch isSome
        (.push (source h) (cst .mark) (.goto (fun _ => .restore h)))
        (.goto (fun _ => afterField h)))
  | .finished => .halt

def run (second : Bool) : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step (machine second))

def finiteMachine (second : Bool) : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := source 0
  k₁ := port 2
  Γ := TopGam
  Λ := Label
  main := .clear 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine second

/-- Clearing accepts arbitrary work-stack contents, not just unary marks. -/
theorem clear_run (second : Bool) (k : Fin 3) (xs : List (TopGam (port k)))
    (v : Sig) (S : ∀ j, List (TopGam j)) (hs : S (port k) = xs) :
    (run second)^[xs.length+1] (some ⟨some (.clear k), v, S⟩) =
      some ⟨some (afterClear k), none, Function.update S (port k) []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, machine, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
      have hfirst : run second (some ⟨some (.clear k), v, S⟩) =
          some ⟨some (.clear k), some x, Function.update S (port k) xs⟩ := by
        simp [run, machine, step, stepAux, hs, pop, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih (some x) (Function.update S (port k) xs) (by simp)

end ShiTMFanoutPrepare
