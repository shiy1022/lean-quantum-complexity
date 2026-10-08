import ReversibleFormulaConfiguration

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding ShiReversibleFormula

local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

noncomputable def pushedSymbol {tm : Turing.FinTM2} (k : tm.K) (f : tm.σ → tm.Γ k)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : pushSymbols (.push k f q) ⊆ machineSymbols tm) (v : tm.σ) : MachineSymbol tm := by
  classical
  refine ⟨⟨k, f v⟩, hq ?_⟩
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)

noncomputable def finiteStatement {tm : Turing.FinTM2} {capacity : Nat} :
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (pushSymbols q ⊆ machineSymbols tm) → FiniteCfg tm capacity → FiniteCfg tm capacity
  | .push k f q, hq, c => finiteStatement q
      (fun _a ha => hq (Finset.mem_union_right _ ha)) (c.push k (pushedSymbol k f q hq c.memory))
  | .peek k f q, hq, c => finiteStatement q hq (c.peek k f)
  | .pop k f q, hq, c => finiteStatement q hq (c.pop k f)
  | .load f q, hq, c => finiteStatement q hq (c.load f)
  | .branch f q r, hq, c => cond (f c.memory)
      (finiteStatement q (fun _a ha => hq (Finset.mem_union_left _ ha)) c)
      (finiteStatement r (fun _a ha => hq (Finset.mem_union_right _ ha)) c)
  | .goto f, _, c => c.goto f
  | .halt, _, c => c.halt

noncomputable def statementFormulas {tm : Turing.FinTM2} {capacity : Nat} {ι : Type} :
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (pushSymbols q ⊆ machineSymbols tm) → FormulaCfg tm capacity ι → FormulaCfg tm capacity ι
  | .push k f q, hq, p => statementFormulas q
      (fun _a ha => hq (Finset.mem_union_right _ ha)) (p.push k (pushedSymbol k f q hq))
  | .peek k f q, hq, p => statementFormulas q hq (p.peek k f)
  | .pop k f q, hq, p => statementFormulas q hq (p.pop k f)
  | .load f q, hq, p => statementFormulas q hq (p.load f)
  | .branch f q r, hq, p => FormulaCfg.mux (unaryTable f p.memory true)
      (statementFormulas q (fun _a ha => hq (Finset.mem_union_left _ ha)) p)
      (statementFormulas r (fun _a ha => hq (Finset.mem_union_right _ ha)) p)
  | .goto f, _, p => p.goto f
  | .halt, _, p => p.halt

/-- A whole actual statement tree is expanded into bounded-arity Boolean formulas. -/
theorem statementFormulas_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) : (statementFormulas q hq p).Denotes x (finiteStatement q hq c) := by
  induction q generalizing p c with
  | push k f q ih =>
    exact ih _ _ _ (p.push_denotes x c h k (pushedSymbol k f q hq))
  | peek k f q ih => exact ih _ _ _ (p.peek_denotes x c h k f)
  | pop k f q ih => exact ih _ _ _ (p.pop_denotes x c h k f)
  | load f q ih => exact ih _ _ _ (p.load_denotes x c h f)
  | branch f q r ihq ihr =>
    have hy := ihq (fun _a ha => hq (Finset.mem_union_left _ ha)) p c h
    have hn := ihr (fun _a ha => hq (Finset.mem_union_right _ ha)) p c h
    have hs : (unaryTable f p.memory true).eval x = f c.memory := by
      rw [eval_unaryTable f p.memory x c.memory true h.2.1]
      cases f c.memory <;> rfl
    simpa only [statementFormulas, finiteStatement, hs] using
      FormulaCfg.mux_denotes (unaryTable f p.memory true) _ _ x _ _ hy hn
  | goto f => exact p.goto_denotes x c h f
  | halt => exact p.halt_denotes x c h

end ShiReversibleTM
