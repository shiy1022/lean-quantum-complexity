import «AMPUNI-readout-schedule»
import «AMPUNI-retained-finite»
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadout
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev PC := Fin 364
abbrev wire (h : Fin 4) : TopK := .inl (.inl ⟨h.val+4, by omega⟩)
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
abbrev output : TopK := .inl (.inl (13 : Fin 14))

theorem wire_ne_scratch (h : Fin 4) : wire h ≠ scratch := by fin_cases h <;> decide
theorem wire_ne_output (h : Fin 4) : wire h ≠ output := by fin_cases h <;> decide

def nextPC (pc : PC) : PC := ⟨(pc.val+1)%364, Nat.mod_lt _ (by decide)⟩
def commandAt (pc : PC) : Option Command := (program.drop pc.val).head?

inductive Label where
  | dispatch (pc : PC) | copy (pc : PC) (h : Fin 4)
  | restore (pc : PC) (h : Fin 4) | delimiter (pc : PC) | finished
  deriving DecidableEq, Fintype

def pushCells : List Cell → Stmt TopGam Label Sig → Stmt TopGam Label Sig
  | [], q => q
  | c :: cs, q => .push output (cst c) (pushCells cs q)

theorem pushCells_step (xs : List Cell) (q : Stmt TopGam Label Sig)
    (v : Sig) (S : ∀ j, List (TopGam j)) :
    stepAux (pushCells xs q) v S =
      stepAux q v (Function.update S output (xs.reverse ++ S output)) := by
  induction xs generalizing S with
  | nil => simp [pushCells]
  | cons c cs ih =>
      simp only [pushCells, stepAux, cst]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def machine : Label → Stmt TopGam Label Sig
  | .dispatch pc => match commandAt pc with
      | none => .goto (fun _ => .finished)
      | some (.inl k) => pushCells (unary k.val) (.goto (fun _ => .dispatch (nextPC pc)))
      | some (.inr h) => .goto (fun _ => .copy pc h)
  | .copy pc h => .pop (wire h) pop
      (.branch isSome
        (.push output (cst .mark) (.push scratch (cst .mark) (.goto (fun _ => .copy pc h))))
        (.goto (fun _ => .restore pc h)))
  | .restore pc h => .pop scratch pop
      (.branch isSome
        (.push (wire h) (cst .mark) (.goto (fun _ => .restore pc h)))
        (.goto (fun _ => .delimiter pc)))
  | .delimiter pc => .push output (cst .delim) (.goto (fun _ => .dispatch (nextPC pc)))
  | .finished => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := wire 0
  k₁ := output
  Γ := TopGam
  Λ := Label
  main := .dispatch 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMReadout
