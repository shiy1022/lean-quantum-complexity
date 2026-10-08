import ReversibleGuardedConfiguration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _
variable {tm : Turing.FinTM2} {capacity position : Nat}
    {p : GuardedTickCfg tm} {q : NaturalFormulaCfg tm (NaturalConfigurationBit tm)}

theorem GuardedTickCfg.Agrees.headCodes (h : p.Agrees capacity position q)
    (k : tm.K) (a : Option (MachineSymbol tm)) :
    (p.headCodes k a).evaluate capacity position = q.headCodes capacity k a := by
  by_cases hc : 0 < capacity
  · have hc' : 1 ≤ capacity := by omega
    simpa [GuardedTickCfg.headCodes, TickGuardFormula.evaluate_branch, TickIndexGuard.eval,
      TickIndexExpr.eval, NaturalFormulaCfg.headCodes, hc, hc'] using h.2.2 k (.literal 0) a
  · have hc' : ¬ 1 ≤ capacity := by omega
    simp [GuardedTickCfg.headCodes, TickGuardFormula.evaluate_branch, TickIndexGuard.eval,
      TickIndexExpr.eval, NaturalFormulaCfg.headCodes, hc, hc', DecisionTree.evaluate,
      DecisionTree.eval, Formula.rename]

theorem GuardedTickCfg.Agrees.load (h : p.Agrees capacity position q) (f : tm.σ → tm.σ) :
    (p.load f).Agrees capacity position (q.load f) := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro v
  change (guardedUnaryTable f p.memory v).evaluate capacity position = unaryTable f q.memory v
  simp only [TickGuardFormula.evaluate_unaryTable, h.2.1]

theorem GuardedTickCfg.Agrees.peek (h : p.Agrees capacity position q) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.peek k f).Agrees capacity position (q.peek capacity k f) := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro v
  change (guardedBinaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes k) v).evaluate
    capacity position = binaryTable (fun s a => f s (decodeCellSymbol k a)) q.memory (q.headCodes capacity k) v
  simp only [TickGuardFormula.evaluate_binaryTable, h.2.1, h.headCodes]

theorem GuardedTickCfg.Agrees.goto (h : p.Agrees capacity position q) (f : tm.σ → tm.Λ) :
    (p.goto f).Agrees capacity position (q.goto f) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro l
  change (guardedUnaryTable (fun v => some (f v)) p.memory l).evaluate capacity position =
    unaryTable (fun v => some (f v)) q.memory l
  simp only [TickGuardFormula.evaluate_unaryTable, h.2.1]

theorem GuardedTickCfg.Agrees.halt (h : p.Agrees capacity position q) :
    p.halt.Agrees capacity position q.halt := by
  exact ⟨fun _ => rfl, h.2.1, h.2.2⟩

theorem GuardedTickCfg.Agrees.mux {p' : GuardedTickCfg tm}
    {q' : NaturalFormulaCfg tm (NaturalConfigurationBit tm)}
    (h : p.Agrees capacity position q) (h' : p'.Agrees capacity position q') (s : TickGuardFormula tm) :
    (GuardedTickCfg.mux s p p').Agrees capacity position
      (NaturalFormulaCfg.mux (s.evaluate capacity position) q q') := by
  refine ⟨?_, ?_, ?_⟩
  · intro l; exact (tickGuardMux_evaluate _ _ _ _ _).trans (by rw [h.1, h'.1]; rfl)
  · intro v; exact (tickGuardMux_evaluate _ _ _ _ _).trans (by rw [h.2.1, h'.2.1]; rfl)
  · intro k i a; exact (tickGuardMux_evaluate _ _ _ _ _).trans (by rw [h.2.2, h'.2.2]; rfl)

theorem GuardedTickCfg.Agrees.push (h : p.Agrees capacity position q) (k : tm.K)
    (f : tm.σ → MachineSymbol tm) :
    (p.push k f).Agrees capacity position (q.push k f) := by
  classical
  refine ⟨h.1, h.2.1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [GuardedTickCfg.push, NaturalFormulaCfg.push, Function.update_self,
      TickGuardFormula.evaluate_branch]
    by_cases hi : i.eval capacity position = 0
    · simp [TickIndexGuard.eval, TickIndexExpr.eval, hi, TickGuardFormula.evaluate_unaryTable, h.2.1]
    · simpa [TickIndexGuard.eval, TickIndexExpr.eval, hi, Nat.le_zero] using h.2.2 k (.sub i 1) a
  · simpa [GuardedTickCfg.push, NaturalFormulaCfg.push, Function.update_of_ne hj] using h.2.2 j i a

theorem GuardedTickCfg.Agrees.pop (h : p.Agrees capacity position q) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.pop k f).Agrees capacity position (q.pop capacity k f) := by
  classical
  refine ⟨h.1, (h.peek k f).2.1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [GuardedTickCfg.pop, NaturalFormulaCfg.pop, Function.update_self,
      TickGuardFormula.evaluate_branch]
    by_cases hi : i.eval capacity position + 1 < capacity
    · have hi' : i.eval capacity position + 2 ≤ capacity := by omega
      simpa [TickIndexGuard.eval, TickIndexExpr.eval, hi, hi'] using h.2.2 k (.add i 1) a
    · have hi' : ¬ i.eval capacity position + 2 ≤ capacity := by omega
      simp [TickIndexGuard.eval, TickIndexExpr.eval, hi, hi', DecisionTree.evaluate,
        DecisionTree.eval, Formula.rename]
  · simpa [GuardedTickCfg.pop, GuardedTickCfg.peek, NaturalFormulaCfg.pop, NaturalFormulaCfg.peek,
      Function.update_of_ne hj] using h.2.2 j i a

end ShiReversibleGenerator
