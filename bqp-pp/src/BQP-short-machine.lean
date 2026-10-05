import «AMPUNI-state-frame»

/-! Concrete finite-prefix dispatcher for the three shortest instances.
This module constructs the machine and lifts its delegated runs. The prefix
execution and whole-machine polynomial bound remain to be established before
it can be used as a polynomial-time closure theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace BQPShortMachine
open Turing Turing.TM2

abbrev Label (tm : FinTM2) := Option (Bool ⊕ Bool) ⊕ tm.Λ
abbrev State (tm : FinTM2) := tm.σ × Option (tm.Γ tm.k₀)

def start (tm : FinTM2) : Label tm := .inl none
def second (tm : FinTM2) (b : Bool) : Label tm := .inl (some (.inl b))
def drain (tm : FinTM2) (b : Bool) : Label tm := .inl (some (.inr b))

def program (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool) :
    Label tm → Stmt tm.Γ (Label tm) (State tm)
  | .inl none =>
      .pop tm.k₀ (fun v a => (v.1, a))
        (.goto (fun v => match v.2.map ea with
          | some (.inl b) => second tm b
          | _ => drain tm c₀))
  | .inl (some (.inl b)) =>
      .pop tm.k₀ (fun v a => (v.1, a))
        (.branch (fun v => match v.2.map ea with
          | some (.inl _) => true
          | _ => false)
          (.push tm.k₀ (fun v => v.2.getD (ea.symm (.inl false)))
            (.push tm.k₀ (fun _ => ea.symm (.inl b))
              (.load (fun _ => (tm.initialState, none))
                (.goto (fun _ => .inr tm.main)))))
          (.goto (fun _ => drain tm (if b then c₂ else c₁))))
  | .inl (some (.inr b)) =>
      .pop tm.k₀ (fun v a => (v.1, a))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => drain tm b))
          (.push tm.k₁ (fun _ => eb.symm b)
            (.load (fun _ => (tm.initialState, none)) .halt)))
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMStateFrame.stmt (tm.m l))

def machine (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool) : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := tm.Γ
  Λ := Label tm
  main := start tm
  ΛFin := by
    letI := tm.ΛFin
    change Fintype (Option (Bool ⊕ Bool) ⊕ tm.Λ)
    infer_instance
  σ := State tm
  initialState := (tm.initialState, none)
  σFin := by
    letI := tm.σFin
    letI := tm.Γk₀Fin
    change Fintype (tm.σ × Option (tm.Γ tm.k₀))
    infer_instance
  Γk₀Fin := tm.Γk₀Fin
  m := program tm ea eb c₀ c₁ c₂

def embed (tm : FinTM2) (c : tm.Cfg) :
    Cfg tm.Γ (Label tm) (State tm) :=
  ShiTMSubroutine.cfg Sum.inr
    (ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀)) c)

/-- After restoring the inspected input symbols and clearing the auxiliary
register, the original checker runs for exactly its original number of steps. -/
theorem delegated_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool) (n : ℕ)
    (c : Option tm.Cfg) :
    (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[n] (c.map (embed tm)) =
      ((ShiTMSubroutine.run tm.m)^[n] c).map (embed tm) := by
  have hl := ShiTMSubroutine.run_iter_lift
    (ShiTMStateFrame.machine tm.m) (program tm ea eb c₀ c₁ c₂) Sum.inr
    (fun _ => rfl) n (c.map (ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀))))
  have hf := ShiTMStateFrame.run_iter_frame tm.m (none : Option (tm.Γ tm.k₀)) n c
  have he := congrArg
    (Option.map (ShiTMSubroutine.cfg (Sum.inr : tm.Λ → Label tm))) hf
  have hstart : (c.map (ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀)))).map
      (ShiTMSubroutine.cfg (Sum.inr : tm.Λ → Label tm)) = c.map (embed tm) := by
    cases c <;> rfl
  have hend : (((ShiTMSubroutine.run tm.m)^[n] c).map
      (ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀)))).map
      (ShiTMSubroutine.cfg (Sum.inr : tm.Λ → Label tm)) =
      ((ShiTMSubroutine.run tm.m)^[n] c).map (embed tm) := by
    cases (ShiTMSubroutine.run tm.m)^[n] c <;> rfl
  exact (congrArg ((ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[n]) hstart).symm.trans
    (hl.trans (he.trans hend))

theorem embedded_halt (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool) (out : List (tm.Γ tm.k₁)) :
    embed tm (haltList tm out) = haltList (machine tm ea eb c₀ c₁ c₂) out := rfl

/-- Delegation preserves the complete output contract, including empty work
stacks, the initial register value, and the original time bound. -/
def delegated_outputs (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool)
    (inp : List (tm.Γ tm.k₀)) (out : List (tm.Γ tm.k₁)) (t : ℕ)
    (h : TM2OutputsInTime tm inp (some out) t) :
    StateTransition.EvalsToInTime (machine tm ea eb c₀ c₁ c₂).step
      (embed tm (initList tm inp)) (some (haltList (machine tm ea eb c₀ c₁ c₂) out)) t := by
  refine { steps := h.steps, steps_le_m := h.steps_le_m, evals_in_steps := ?_ }
  have hr : (ShiTMSubroutine.run tm.m)^[h.steps] (some (initList tm inp)) =
      some (haltList tm out) := h.evals_in_steps
  have hd := delegated_run tm ea eb c₀ c₁ c₂ h.steps (some (initList tm inp))
  exact hd.trans (congrArg (Option.map (embed tm)) hr)

end BQPShortMachine
