/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Configurations and segment bookkeeping for the enumerator run (plan tasks S13, S14).
-/
import Machine.Enumerator

set_option autoImplicit false

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Close an equation between host stacks `join chk (Function.update … R.get …)` and
`join chk R'.get` register by register. -/
macro "regs_eq" : tactic =>
  `(tactic| (congr 1; funext e; cases e <;> rfl))

/-! ### Segments without step counts -/

section SegE

variable {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}

/-- Some run segment from `c` to `d` stays within `B`. -/
def SegE (M : L → Stmt G L V) (c d : Cfg G L V) (B : ℕ) : Prop := ∃ n, Seg M c n d B

variable {M : L → Stmt G L V}

theorem Seg.toE {c d : Cfg G L V} {n B : ℕ} (h : Seg M c n d B) : SegE M c d B := ⟨n, h⟩

theorem SegE.trans {c d e : Cfg G L V} {B : ℕ} (h₁ : SegE M c d B) (h₂ : SegE M d e B) :
    SegE M c e B := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, h₂⟩ := h₂
  exact ⟨m + n, h₁.trans' h₂⟩

theorem SegE.mono {c d : Cfg G L V} {B B' : ℕ} (h : SegE M c d B) (hB : B ≤ B') :
    SegE M c d B' := by
  obtain ⟨n, h⟩ := h; exact ⟨n, h.mono hB⟩

theorem SegE.refl {c : Cfg G L V} {B : ℕ} (h : ShiTMStackGrowth.size c.stk ≤ B) :
    SegE M c c B := ⟨0, Seg.refl h⟩

theorem SegE.single {c d : Cfg G L V} {B : ℕ} (h : step M c = some d)
    (hc : ShiTMStackGrowth.size c.stk ≤ B) (hd : ShiTMStackGrowth.size d.stk ≤ B) :
    SegE M c d B := ⟨1, Seg.single h hc hd⟩

theorem SegE.cast {c d d' : Cfg G L V} {B : ℕ} (h : SegE M c d B) (e : d = d') :
    SegE M c d' B := e ▸ h

end SegE

/-! ### Wrapper-phase configurations -/

section Configs

variable {tm : FinTM2} {k : ℕ}

/-- Empty checker stacks. -/
def nochk (tm : FinTM2) : ∀ j : tm.K, List (tm.Γ j) := fun _ => []

/-- A host configuration with checker state at its initial value. -/
def wc (l : EL tm k) (r : Reg) (chk : ∀ j : tm.K, List (tm.Γ j)) (R : Regs) :
    Cfg (HG tm.Γ) (EL tm k) (tm.σ × Reg) :=
  ⟨some l, (tm.initialState, r), join chk R.get⟩

theorem size_wc (l : EL tm k) (r : Reg) (chk : ∀ j : tm.K, List (tm.Γ j)) (R : Regs) :
    ShiTMStackGrowth.size (wc l r chk R).stk = ShiTMStackGrowth.size chk + R.len := by
  rw [show (wc l r chk R).stk = join chk R.get from rfl, size_join, ← Regs.extSize_get]
  rfl

theorem size_nochk (tm : FinTM2) : ShiTMStackGrowth.size (nochk tm) = 0 := by
  simp [ShiTMStackGrowth.size, nochk]

end Configs

section Loops

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ (Bool ⊕ Bool)) (eout : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

local notation "M" => prog tm ein eout k

/-- A transfer loop between wrapper-phase configurations, given the closed form of its result
and space bounds at both ends. -/
theorem segE_loop {l next : EL tm k} {src : Ext} {ts : List (Tgt tm.Γ)}
    (hM : M l = loopStmt src ts l next) (hts : Avoids ts (.inr src)) (r : Reg)
    (chk chk' : ∀ j : tm.K, List (tm.Γ j)) (R R' : Regs)
    (hout : loopOut ts src (R.get src) (join chk R.get) = join chk' R'.get) (B : ℕ)
    (hin : ShiTMStackGrowth.size chk + R.len ≤ B) (hex : ShiTMStackGrowth.size chk' + R'.len ≤ B) :
    SegE M (wc l r chk R) (wc next (false, false) chk' R') B := by
  have h := loop_seg M src ts l next hM hts (R.get src) tm.initialState r (join chk R.get) rfl
  rw [hout] at h
  refine ⟨_, h.mono (max_le ?_ ?_)⟩
  · rw [size_join, show (∑ e, (R.get e).length) = R.len from Regs.extSize_get R]; exact hin
  · rw [size_join, show (∑ e, (R'.get e).length) = R'.len from Regs.extSize_get R']; exact hex

/-- One wrapper statement step. -/
theorem segE_step {l l' : EL tm k} {r r' : Reg} {chk chk' : ∀ j : tm.K, List (tm.Γ j)}
    {R R' : Regs} (h : step M (wc l r chk R) = some (wc l' r' chk' R')) (B : ℕ)
    (hin : ShiTMStackGrowth.size chk + R.len ≤ B) (hex : ShiTMStackGrowth.size chk' + R'.len ≤ B) :
    SegE M (wc l r chk R) (wc l' r' chk' R') B :=
  SegE.single h (by rw [size_wc]; exact hin) (by rw [size_wc]; exact hex)

end Loops

/-! ### Avoidance facts for the concrete target lists -/

section Avoid

variable {tm : FinTM2}

theorem avoids_one {i : tm.K ⊕ Ext} {f : Bool → HG tm.Γ i} {j : tm.K ⊕ Ext} (h : i ≠ j) :
    Avoids [⟨i, f⟩] j := by
  intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact h

theorem avoids_two {i₁ i₂ : tm.K ⊕ Ext} {f₁ : Bool → HG tm.Γ i₁} {f₂ : Bool → HG tm.Γ i₂}
    {j : tm.K ⊕ Ext} (h₁ : i₁ ≠ j) (h₂ : i₂ ≠ j) : Avoids [⟨i₁, f₁⟩, ⟨i₂, f₂⟩] j := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> assumption

theorem avoids_nil (j : tm.K ⊕ Ext) : Avoids ([] : List (Tgt tm.Γ)) j := by
  intro t ht; cases ht

end Avoid

end ShiPPPSPACE
