import «AMPUNI-stack-frame»
import «AMPUNI-state-frame»
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPPrefixMachine
open Turing Turing.TM2

/-- One extra stack holds the reversed instance while two witness bits are read. -/
abbrev framed (tm : FinTM2) : FinTM2 where
  K := tm.K ⊕ Unit
  kDecidableEq := inferInstance
  kFin := by letI := tm.kFin; infer_instance
  k₀ := .inl tm.k₀
  k₁ := .inl tm.k₁
  Γ := ShiTMStackFrame.Gam tm.Γ (fun (_ : Unit) => tm.Γ tm.k₀)
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := tm.Γk₀Fin
  m := ShiTMStackFrame.machine tm.m

inductive Control
  | scan
  | second (b : Bool)
  | restore
  | rejectInput
  | rejectAux
  deriving DecidableEq, Fintype

abbrev Label (tm : FinTM2) := Control ⊕ tm.Λ
abbrev State (tm : FinTM2) := tm.σ × Option (tm.Γ tm.k₀)

def program (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) :
    Label tm → Stmt (framed tm).Γ (Label tm) (State tm)
  | .inl .scan =>
      .pop (.inl tm.k₀) (fun v a => (v.1, a))
        (.branch (fun v => match v.2.map ea with | some (.inl _) => true | _ => false)
          (.push (.inr ()) (fun v => v.2.getD (ea.symm (.inl false)))
            (.goto (fun _ => .inl .scan)))
          (.goto (fun v => match v.2.map ea with
            | some (.inr b) => .inl (.second b)
            | _ => .inl .rejectInput)))
  | .inl (.second b) =>
      .pop (.inl tm.k₀) (fun v a => (v.1, a))
        (.goto (fun v => match v.2.map ea with
          | some (.inr d) => if b == d then .inl .restore else .inl .rejectInput
          | _ => .inl .rejectInput))
  | .inl .restore =>
      .pop (.inr ()) (fun v a => (v.1, a))
        (.branch (fun v => v.2.isSome)
          (.push (.inl tm.k₀) (fun v => v.2.getD (ea.symm (.inl false)))
            (.goto (fun _ => .inl .restore)))
          (.load (fun _ => (tm.initialState, none)) (.goto (fun _ => .inr tm.main))))
  | .inl .rejectInput =>
      .pop (.inl tm.k₀) (fun v a => (v.1, a))
        (.goto (fun v => if v.2.isSome then .inl .rejectInput else .inl .rejectAux))
  | .inl .rejectAux =>
      .pop (.inr ()) (fun v a => (v.1, a))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .inl .rejectAux))
          (.push (.inl tm.k₁) (fun _ => eb.symm false)
            (.load (fun _ => (tm.initialState, none)) .halt)))
  | .inr l => ShiTMSubroutine.stmt Sum.inr
      (ShiTMStateFrame.stmt ((framed tm).m l))

def machine (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) : FinTM2 where
  K := (framed tm).K
  kDecidableEq := (framed tm).kDecidableEq
  kFin := (framed tm).kFin
  k₀ := (framed tm).k₀
  k₁ := (framed tm).k₁
  Γ := (framed tm).Γ
  Λ := Label tm
  main := .inl .scan
  ΛFin := by letI := tm.ΛFin; change Fintype (Control ⊕ tm.Λ); infer_instance
  σ := State tm
  initialState := (tm.initialState, none)
  σFin := by
    letI := tm.σFin
    letI := tm.Γk₀Fin
    change Fintype (tm.σ × Option (tm.Γ tm.k₀))
    infer_instance
  Γk₀Fin := tm.Γk₀Fin
  m := program tm ea eb

def embed (tm : FinTM2) (c : tm.Cfg) :
    Cfg (framed tm).Γ (Label tm) (State tm) :=
  ShiTMSubroutine.cfg Sum.inr
    (ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀))
      (ShiTMStackFrame.cfg (fun (_ : Unit) => ([] : List (tm.Γ tm.k₀))) c))

/-- Delegation preserves the original run exactly and leaves the new stack empty. -/
theorem delegated_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (n : ℕ) (c : Option tm.Cfg) :
    (ShiTMSubroutine.run (program tm ea eb))^[n] (c.map (embed tm)) =
      ((ShiTMSubroutine.run tm.m)^[n] c).map (embed tm) := by
  let f : tm.Cfg → (framed tm).Cfg := ShiTMStackFrame.cfg (fun (_ : Unit) => ([] : List (tm.Γ tm.k₀)))
  let g : (framed tm).Cfg → Cfg (framed tm).Γ tm.Λ (State tm) := ShiTMStateFrame.cfg (none : Option (tm.Γ tm.k₀))
  let j : Cfg (framed tm).Γ tm.Λ (State tm) →
      Cfg (framed tm).Γ (Label tm) (State tm) := ShiTMSubroutine.cfg (Sum.inr : tm.Λ → Label tm)
  have hs := ShiTMStackFrame.run_iter_frame tm.m
    (fun (_ : Unit) => ([] : List (tm.Γ tm.k₀))) n c
  have hv := ShiTMStateFrame.run_iter_frame (framed tm).m
    (none : Option (tm.Γ tm.k₀)) n (c.map f)
  have hl := ShiTMSubroutine.run_iter_lift
    (ShiTMStateFrame.machine (framed tm).m) (program tm ea eb) Sum.inr
    (fun _ => rfl) n ((c.map f).map g)
  have h := hl.trans ((congrArg (Option.map j) hv).trans
    (congrArg (fun d => (d.map g).map j) hs))
  have hstart : ((c.map f).map g).map j = c.map (embed tm) := by
    cases c <;> rfl
  have hend : ((((ShiTMSubroutine.run tm.m)^[n] c).map f).map g).map j =
      ((ShiTMSubroutine.run tm.m)^[n] c).map (embed tm) := by
    cases (ShiTMSubroutine.run tm.m)^[n] c <;> rfl
  exact (congrArg ((ShiTMSubroutine.run (program tm ea eb))^[n]) hstart).symm.trans
    (h.trans hend)


end BQPPrefixMachine
