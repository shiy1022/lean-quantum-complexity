/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Embedding the checker machine into the host, with halt redirection (plan task S10).
-/
import Machine.Host

set_option autoImplicit false

/-!
# Embedded checker runs

A source program over stacks `κ`, labels `Λ` and state `σ` is translated statement by
statement into the host: stack `k` becomes `inl k`, the state is paired with the untouched
wrapper register, a `goto` is relabelled by `lab`, and `halt` becomes `goto after`. Wrapper
registers (`inr` stacks) are never touched by translated statements.

`emb r ext c` is the host image of a source configuration (a halted source configuration maps
to label `after`). One host step from the image of a running configuration is the image of
the source step; hence a source run that halts at step `n` is mirrored exactly for `n` steps,
and its host space is the source space plus the wrapper-register space.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

variable {κ : Type} [DecidableEq κ] {Γ : κ → Type} {Λ σ L : Type}

local notation "run" => ShiTMSubroutine.run

/-- Structural translation of source statements. -/
def tr (lab : Λ → L) (after : L) : Stmt Γ Λ σ → Stmt (HG Γ) L (σ × Reg)
  | .push k f q => .push (.inl k) (fun v => f v.1) (tr lab after q)
  | .peek k f q => .peek (.inl k) (fun v o => (f v.1 o, v.2)) (tr lab after q)
  | .pop k f q => .pop (.inl k) (fun v o => (f v.1 o, v.2)) (tr lab after q)
  | .load f q => .load (fun v => (f v.1, v.2)) (tr lab after q)
  | .branch f p q => .branch (fun v => f v.1) (tr lab after p) (tr lab after q)
  | .goto f => .goto (fun v => lab (f v.1))
  | .halt => .goto (fun _ => after)

/-- Host image of a source configuration. -/
def emb (lab : Λ → L) (after : L) (r : Reg) (ext : Ext → List Bool) (c : Cfg Γ Λ σ) :
    Cfg (HG Γ) L (σ × Reg) :=
  ⟨some (c.l.elim after lab), (c.var, r), join c.stk ext⟩

variable (lab : Λ → L) (after : L)

theorem stepAux_tr (q : Stmt Γ Λ σ) (s : σ) (r : Reg) (S : ∀ k, List (Γ k))
    (ext : Ext → List Bool) :
    stepAux (tr lab after q) (s, r) (join S ext) = emb lab after r ext (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
      change stepAux (tr lab after q) (s, r)
        (Function.update (join S ext) (.inl k) (f s :: join S ext (.inl k))) = _
      rw [join_inl, update_join_inl, ih]
      rfl
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      change stepAux (tr lab after q) (f s (join S ext (.inl k)).head?, r)
        (Function.update (join S ext) (.inl k) (join S ext (.inl k)).tail) = _
      rw [join_inl, update_join_inl, ih]
      rfl
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
      simp only [tr, stepAux]
      cases f s
      · exact ihq s S
      · exact ihp s S
  | goto f => rfl
  | halt => rfl

variable (M : L → Stmt (HG Γ) L (σ × Reg)) (m : Λ → Stmt Γ Λ σ)

/-- One host step from the image of a running source configuration. -/
theorem step_emb (hM : ∀ l, M (lab l) = tr lab after (m l)) (r : Reg) (ext : Ext → List Bool)
    (c : Cfg Γ Λ σ) (l : Λ) (hc : c.l = some l) :
    step M (emb lab after r ext c) = (step m c).map (emb lab after r ext) := by
  rcases c with ⟨_, s, S⟩
  cases hc
  simp only [emb, Option.elim, step, hM, stepAux_tr, Option.map_some]

/-- **Mirrored run.** A source run halting at step `n` is reproduced for `n` host steps. -/
theorem iterate_emb (hM : ∀ l, M (lab l) = tr lab after (m l)) (r : Reg) (ext : Ext → List Bool)
    (c d : Cfg Γ Λ σ) (n : ℕ) (hn : (run m)^[n] (some c) = some d) :
    ∀ t ≤ n, (run M)^[t] (some (emb lab after r ext c)) =
      ((run m)^[t] (some c)).map (emb lab after r ext) := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterate_run_succ', iterate_run_succ', ih (by omega)]
      obtain ⟨e, he⟩ := iterate_prefix m c d n t hn (by omega)
      rw [he]
      rcases e with ⟨el, s, S⟩
      cases el with
      | none =>
          exfalso
          have := iterate_after_halt m c _ t n he rfl (by omega)
          rw [hn] at this
          cases this
      | some l =>
          exact step_emb lab after M m hM r ext _ l rfl

theorem iterate_emb_halt (hM : ∀ l, M (lab l) = tr lab after (m l)) (r : Reg)
    (ext : Ext → List Bool) (c d : Cfg Γ Λ σ) (n : ℕ) (hn : (run m)^[n] (some c) = some d) :
    (run M)^[n] (some (emb lab after r ext c)) = some (emb lab after r ext d) := by
  rw [iterate_emb lab after M m hM r ext c d n hn n le_rfl, hn]
  rfl

omit [DecidableEq κ] in
theorem emb_halted (r : Reg) (ext : Ext → List Bool) (d : Cfg Γ Λ σ) (hd : Halted d) :
    emb lab after r ext d = ⟨some after, (d.var, r), join d.stk ext⟩ := by
  rcases d with ⟨_, s, S⟩
  cases hd
  rfl

variable [Fintype κ]

theorem size_emb (r : Reg) (ext : Ext → List Bool) (c : Cfg Γ Λ σ) :
    ShiTMStackGrowth.size (emb lab after r ext c).stk =
      ShiTMStackGrowth.size c.stk + extSize ext := size_join _ _

/-- **Checker-phase segment.** Host peak = source peak + wrapper-register space. -/
theorem seg_emb (hM : ∀ l, M (lab l) = tr lab after (m l)) (r : Reg) (ext : Ext → List Bool)
    (c d : Cfg Γ Λ σ) (n : ℕ) (hn : (run m)^[n] (some c) = some d) (B : ℕ)
    (hB : ∀ t ≤ n, ∀ e, (run m)^[t] (some c) = some e → ShiTMStackGrowth.size e.stk ≤ B) :
    Seg M (emb lab after r ext c) n (emb lab after r ext d) (B + extSize ext) := by
  refine ⟨iterate_emb_halt lab after M m hM r ext c d n hn, fun t ht e he => ?_⟩
  rw [iterate_emb lab after M m hM r ext c d n hn t ht] at he
  cases he' : (run m)^[t] (some c) with
  | none => rw [he'] at he; cases he
  | some e' =>
      rw [he'] at he
      cases he
      rw [size_emb]
      exact Nat.add_le_add_right (hB t ht e' he') _

end ShiPPPSPACE
