import «BQP-halt-routing-run»
import «AMPUNI-stack-frame»
import «AMPUNI-state-frame»
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2

inductive Extra
  | input | output | witness | buffer
  deriving DecidableEq

instance : Fintype Extra := ⟨{.input, .output, .witness, .buffer}, by intro e; cases e <;> simp⟩

abbrev ExtraGam : Extra → Type
  | .input | .output => Bool ⊕ Bool
  | .witness | .buffer => Bool

abbrev framed (tm : FinTM2) : FinTM2 where
  K := tm.K ⊕ Extra
  kDecidableEq := inferInstance
  kFin := by letI := tm.kFin; infer_instance
  k₀ := .inl tm.k₀
  k₁ := .inl tm.k₁
  Γ := ShiTMStackFrame.Gam tm.Γ ExtraGam
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := tm.Γk₀Fin
  m := ShiTMStackFrame.machine tm.m

inductive Control
  | scan | restoreInput | restoreWitness | reverseResult | emitResult
  deriving DecidableEq

instance : Fintype Control :=
  ⟨{.scan, .restoreInput, .restoreWitness, .reverseResult, .emitResult}, by intro c; cases c <;> simp⟩

abbrev Label (tm : FinTM2) := Control ⊕ tm.Λ
abbrev State (tm : FinTM2) := tm.σ × Option (Bool ⊕ Bool)

def registerBit (tm : FinTM2) (v : State tm) : Bool :=
  Sum.elim id id (v.2.getD (.inl false))

def program (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) :
    Label tm → Stmt (framed tm).Γ (Label tm) (State tm)
  | .inl .scan =>
      .pop (.inr .input) (fun v a => (v.1,a))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => match v.2 with | some (.inl _) => true | _ => false)
            (.push (.inr .buffer) (registerBit tm) (.goto (fun _ => .inl .scan)))
            (.push (.inr .witness) (registerBit tm) (.goto (fun _ => .inl .scan))))
          (.goto (fun _ => .inl .restoreInput)))
  | .inl .restoreInput =>
      .pop (.inr .buffer) (fun v a => (v.1,a.map Sum.inl))
        (.branch (fun v => v.2.isSome)
          (.push (.inl tm.k₀) (fun v => ea.symm (registerBit tm v))
            (.goto (fun _ => .inl .restoreInput)))
          (.load (fun _ => (tm.initialState,none)) (.goto (fun _ => .inr tm.main))))
  | .inl .restoreWitness =>
      .pop (.inr .witness) (fun v a => (v.1,a.map Sum.inr))
        (.branch (fun v => v.2.isSome)
          (.push (.inr .output) (fun v => .inr (registerBit tm v))
            (.goto (fun _ => .inl .restoreWitness)))
          (.goto (fun _ => .inl .reverseResult)))
  | .inl .reverseResult =>
      .pop (.inl tm.k₁) (fun v a => (v.1,a.map (fun b => .inl (eb b))))
        (.branch (fun v => v.2.isSome)
          (.push (.inr .buffer) (registerBit tm) (.goto (fun _ => .inl .reverseResult)))
          (.goto (fun _ => .inl .emitResult)))
  | .inl .emitResult =>
      .pop (.inr .buffer) (fun v a => (v.1,a.map Sum.inl))
        (.branch (fun v => v.2.isSome)
          (.push (.inr .output) (fun v => .inl (registerBit tm v))
            (.goto (fun _ => .inl .emitResult)))
          (.load (fun _ => (tm.initialState,none)) .halt))
  | .inr l => ShiTMHaltRouting.stmt Sum.inr (.inl .restoreWitness)
      (ShiTMStateFrame.stmt ((framed tm).m l))

def machine (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) : FinTM2 where
  K := (framed tm).K
  kDecidableEq := (framed tm).kDecidableEq
  kFin := (framed tm).kFin
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := (framed tm).Γ
  Λ := Label tm
  main := .inl .scan
  ΛFin := by letI := tm.ΛFin; change Fintype (Control ⊕ tm.Λ); infer_instance
  σ := State tm
  initialState := (tm.initialState,none)
  σFin := by letI := tm.σFin; change Fintype (tm.σ × Option (Bool ⊕ Bool)); infer_instance
  Γk₀Fin := inferInstance
  m := program tm ea eb

def embed (tm : FinTM2) (A : ∀ e, List (ExtraGam e)) (c : tm.Cfg) :
    Cfg (framed tm).Γ (Label tm) (State tm) :=
  ShiTMHaltRouting.cfg Sum.inr (.inl .restoreWitness)
    (ShiTMStateFrame.cfg (none : Option (Bool ⊕ Bool)) (ShiTMStackFrame.cfg A c))

/-- Preserve all four added stacks while running the source computation; its
halt becomes a continuation at restoreWitness, without increasing its step count. -/
theorem delegated_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (A : ∀ e, List (ExtraGam e)) (n : ℕ) (c : Option tm.Cfg) (d : tm.Cfg)
    (h : (ShiTMSubroutine.run tm.m)^[n] c = some d) :
    (ShiTMSubroutine.run (program tm ea eb))^[n] (c.map (embed tm A)) =
      some (embed tm A d) := by
  let f : tm.Cfg → (framed tm).Cfg := ShiTMStackFrame.cfg A
  let g : (framed tm).Cfg → Cfg (framed tm).Γ tm.Λ (State tm) :=
    ShiTMStateFrame.cfg (none : Option (Bool ⊕ Bool))
  let j : Cfg (framed tm).Γ tm.Λ (State tm) → Cfg (framed tm).Γ (Label tm) (State tm) :=
    ShiTMHaltRouting.cfg Sum.inr (.inl .restoreWitness)
  have hs := (ShiTMStackFrame.run_iter_frame tm.m A n c).trans
    (congrArg (Option.map f) h)
  have hv := (ShiTMStateFrame.run_iter_frame (framed tm).m
    (none : Option (Bool ⊕ Bool)) n (c.map f)).trans (congrArg (Option.map g) hs)
  have hl := ShiTMHaltRouting.run_to_some (ShiTMStateFrame.machine (framed tm).m)
    (program tm ea eb) Sum.inr (.inl .restoreWitness) (fun _ => rfl)
    n ((c.map f).map g) (g (f d)) hv
  have he : (((c.map f).map g).map j) = c.map (embed tm A) := by cases c <;> rfl
  exact (congrArg ((ShiTMSubroutine.run (program tm ea eb))^[n]) he).symm.trans hl

end BQPMapFirst
