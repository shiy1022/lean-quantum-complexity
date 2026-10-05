/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The finite enumerator machine deciding a PP language in polynomial space (plan task S13).
-/
import Machine.Increment
import Machine.MajorityTest
import Machine.CheckerCall
import Machine.Regs

set_option autoImplicit false

/-!
# The enumerator

Parameters: the checker machine `tm` (from a `PolyTimeChecker` certificate) with its input
alphabet equivalence `ein : tm.Γ tm.k₀ ≃ Bool ⊕ Bool` and output equivalence
`eout : tm.Γ tm.k₁ ≃ Bool`, and the fixed exponent `k`. The finite control depends only on
these; `n`, `m = n^k`, the witness and the counter live on stacks.

* **INIT** (`lenA` … `clrN`): copy the input length to unary `nn` (input restored); seed
  `wit = [false]`; `k` hard-coded rounds multiply the unary `wit` by `n` (through `pq`);
  copy `wit` to `cnt` and add one cell, so `wit = 0^m`, `cnt = 0^(m+1)`; clear `nn`.
* **LOOP** (`prepA` … `incWov`): write `encodePair (x, w)` onto the checker input stack while
  restoring `wit` and `inp`; run the embedded checker (its halt jumps to `ans`); pop its
  answer; increment `cnt` on acceptance; increment `wit`; on witness overflow leave the loop.
* **FINAL** (`finA` … `finH`): clear `wit` and `inp`; scan `cnt` and push
  `2 * cnt > 2^m` onto `out`; halt.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Wrapper control labels. `k` hard-codes the number of multiplication rounds. -/
inductive WL (k : ℕ)
  | lenA | lenB | seed
  | mulPop (i : Fin k) | mulA (i : Fin k) | mulB (i : Fin k) | mulMove (i : Fin k)
  | cntA | cntB | cntOne | clrN
  | prepA | prepB | prepC | prepD
  | ans
  | incC | incCno | incCov | incW | incWno | incWov
  | finA | finB | scan (st : ScanSt) | finH
  deriving DecidableEq, Fintype

section Program

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ (Bool ⊕ Bool)) (eout : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

/-- Host labels: checker labels and wrapper labels. -/
abbrev EL := tm.Λ ⊕ WL k

/-- Host statements. -/
abbrev EStmt := Stmt (HG tm.Γ) (EL tm k) (tm.σ × Reg)

variable {tm k} in
/-- Wrapper label as a host label. -/
abbrev W (l : WL k) : EL tm k := .inr l

/-- Push the popped bit unchanged. -/
abbrev idT (e : Ext) : Tgt tm.Γ := ⟨.inr e, id⟩

/-- Push a constant `false` (unary counting). -/
abbrev falseT (e : Ext) : Tgt tm.Γ := ⟨.inr e, fun _ => false⟩

/-- Push the popped bit onto the checker input stack, tagged by `tag`. -/
abbrev chkT (tag : Bool → Bool ⊕ Bool) : Tgt tm.Γ := ⟨.inl tm.k₀, fun b => ein.symm (tag b)⟩

/-- Wrapper statements. -/
def wprog : WL k → EStmt tm k
  | .lenA => loopStmt .inp [idT tm .tmp] (W .lenA) (W .lenB)
  | .lenB => loopStmt .tmp [idT tm .inp, falseT tm .nn] (W .lenB) (W .seed)
  | .seed => .push (.inr .wit) (fun _ => false)
      (.goto fun _ => if h : 0 < k then W (.mulPop ⟨0, h⟩) else W .cntA)
  | .mulPop i => popBit .wit
      (.branch (fun v => v.2.2) (.goto fun _ => W (.mulA i)) (.goto fun _ => W (.mulMove i)))
  | .mulA i => loopStmt .nn [idT tm .tmp] (W (.mulA i)) (W (.mulB i))
  | .mulB i => loopStmt .tmp [idT tm .nn, falseT tm .pq] (W (.mulB i)) (W (.mulPop i))
  | .mulMove i => loopStmt .pq [falseT tm .wit] (W (.mulMove i))
      (if h : i.val + 1 < k then W (.mulPop ⟨i.val + 1, h⟩) else W .cntA)
  | .cntA => loopStmt .wit [idT tm .tmp] (W .cntA) (W .cntB)
  | .cntB => loopStmt .tmp [idT tm .wit, falseT tm .cnt] (W .cntB) (W .cntOne)
  | .cntOne => .push (.inr .cnt) (fun _ => false) (.goto fun _ => W .clrN)
  | .clrN => loopStmt .nn [] (W .clrN) (W .prepA)
  | .prepA => loopStmt .wit [idT tm .tmp] (W .prepA) (W .prepB)
  | .prepB => loopStmt .tmp [idT tm .wit, chkT tm ein Sum.inr] (W .prepB) (W .prepC)
  | .prepC => loopStmt .inp [idT tm .tmp] (W .prepC) (W .prepD)
  | .prepD => loopStmt .tmp [idT tm .inp, chkT tm ein Sum.inl] (W .prepD) (.inl tm.main)
  | .ans => .pop (.inl tm.k₁) (fun v o => (v.1, ((o.map eout).getD false, true)))
      (.branch (fun v => v.2.1) (.goto fun _ => W .incC) (.goto fun _ => W .incW))
  | .incC => incStmt .cnt .tmp (W .incC) (W .incCno) (W .incCov)
  | .incCno => loopStmt .tmp (moveTgt .cnt) (W .incCno) (W .incW)
  | .incCov => loopStmt .tmp (moveTgt .cnt) (W .incCov) (W .incW)
  | .incW => incStmt .wit .tmp (W .incW) (W .incWno) (W .incWov)
  | .incWno => loopStmt .tmp (moveTgt .wit) (W .incWno) (W .prepA)
  | .incWov => loopStmt .tmp (moveTgt .wit) (W .incWov) (W .finA)
  | .finA => loopStmt .wit [] (W .finA) (W .finB)
  | .finB => loopStmt .inp [] (W .finB) (W (.scan (false, false, false)))
  | .scan st => scanStmt .cnt .out (fun st => W (.scan st)) (W .finH) st
  | .finH => .halt

/-- The host program: translated checker statements and wrapper statements. -/
def prog : EL tm k → EStmt tm k
  | .inl l => tr Sum.inl (W .ans) (tm.m l)
  | .inr l => wprog tm ein eout k l

/-- **The enumerator** as a bundled finite machine. -/
def machine : FinTM2 where
  K := tm.K ⊕ Ext
  k₀ := .inr .inp
  k₁ := .inr .out
  Γ := HG tm.Γ
  Λ := EL tm k
  main := W .lenA
  σ := tm.σ × Reg
  initialState := (tm.initialState, (false, false))
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog tm ein eout k

end Program

end ShiPPPSPACE
