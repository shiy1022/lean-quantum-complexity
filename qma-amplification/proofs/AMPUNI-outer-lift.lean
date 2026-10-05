import «AMPUNI-loop-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

abbrev OuterK := Fin 14 ⊕ Fin 2
abbrev OuterGam : OuterK → Type
  | .inl k => Gam k
  | .inr _ => Cell

inductive OuterControl where
  | circuitHeader
  | layerDriver
  | layerHeader
  | gateDriver
  | exit
deriving DecidableEq

abbrev OuterLabel := Label ⊕ OuterControl

def liftStacks (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell) :
    ∀ k : OuterK, List (OuterGam k)
  | .inl k => S k
  | .inr k => C k

def liftCfg (C : Fin 2 → List Cell) (c : Cfg Gam Label Sig) :
    Cfg OuterGam OuterLabel Sig :=
  { l := c.l.map Sum.inl, var := c.var, stk := liftStacks c.stk C }

def liftStmt : Stmt Gam Label Sig → Stmt OuterGam OuterLabel Sig
  | .push k f q => .push (.inl k) f (liftStmt q)
  | .peek k f q => .peek (.inl k) f (liftStmt q)
  | .pop k f q => .pop (.inl k) f (liftStmt q)
  | .load f q => .load f (liftStmt q)
  | .branch f q₁ q₂ => .branch f (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => .inl (f v))
  | .halt => .halt

/-- Placeholder control labels can be replaced by the nested driver; the instruction body
is already lifted without changing any transition. -/
def outerMachine : OuterLabel → Stmt OuterGam OuterLabel Sig
  | .inl l => liftStmt (loopMachine l)
  | .inr _ => .halt

def outerRun : Option (Cfg OuterGam OuterLabel Sig) →
    Option (Cfg OuterGam OuterLabel Sig) :=
  fun cf => cf.bind (step outerMachine)

private theorem liftStacks_update (S : ∀ k, List (Gam k))
    (C : Fin 2 → List Cell) (k : Fin 14) (v : List (Gam k)) :
    Function.update (liftStacks S C) (Sum.inl k) v =
      liftStacks (Function.update S k v) C := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst h
      simp [liftStacks]
    · have hs : (Sum.inl j : OuterK) ≠ Sum.inl k := by
        intro e
        exact h (Sum.inl.inj e)
      rw [Function.update_of_ne hs]
      change S j = Function.update S k v j
      rw [Function.update_of_ne h]
  | inr j =>
    have hs : (Sum.inr j : OuterK) ≠ Sum.inl k := by simp
    rw [Function.update_of_ne hs]
    rfl

theorem stepAux_liftStmt (q : Stmt Gam Label Sig) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell) :
    stepAux (liftStmt q) v (liftStacks S C) =
      liftCfg C (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftStmt, stepAux]
    rw [liftStacks_update]
    exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
    simp only [liftStmt, stepAux, liftStacks]
    exact ih (f v (S k).head?) S
  | pop k f q ih =>
    simp only [liftStmt, stepAux, liftStacks]
    rw [liftStacks_update]
    exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
    simp only [liftStmt, stepAux]
    exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, stepAux]
    cases h : f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem step_lift (C : Fin 2 → List Cell) (c : Cfg Gam Label Sig) :
    step outerMachine (liftCfg C c) =
      (step loopMachine c).map (liftCfg C) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftStmt (loopMachine l)) v (liftStacks S C)) =
        some (liftCfg C (stepAux (loopMachine l) v S))
      rw [stepAux_liftStmt]

theorem outerRun_lift (C : Fin 2 → List Cell)
    (cf : Option (Cfg Gam Label Sig)) :
    outerRun (cf.map (liftCfg C)) = (loopRun cf).map (liftCfg C) := by
  cases cf with
  | none => rfl
  | some c =>
    simp only [Option.map_some, outerRun, loopRun, Option.bind_some]
    exact step_lift C c

theorem outerRun_iter_lift (C : Fin 2 → List Cell) (n : Nat)
    (cf : Option (Cfg Gam Label Sig)) :
    outerRun^[n] (cf.map (liftCfg C)) =
      (loopRun^[n] cf).map (liftCfg C) := by
  induction n generalizing cf with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [outerRun_lift]
    exact ih (loopRun cf)

end ShiTMOuterLift
