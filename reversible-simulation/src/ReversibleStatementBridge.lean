import ReversibleStatementFormulas
import ReversibleStatementCapacity

set_option autoImplicit false
namespace ShiReversibleTM

local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

noncomputable def BoundedCfg.control {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (l : Option tm.Λ) (v : tm.σ) : BoundedCfg tm capacity where
  cfg := { c.cfg with l := l, var := v }
  length_bound := c.length_bound
  alphabet := c.alphabet

theorem BoundedCfg.encode_control {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (l : Option tm.Λ) (v : tm.σ) :
    (c.control l v).encode = { c.encode with label := l, memory := v } := by
  apply FiniteCfg.ext
  · rfl
  · rfl
  · funext k
    change ShiReversibleCoding.tapeEncode capacity ((c.control l v).stackSymbols k) =
      ShiReversibleCoding.tapeEncode capacity (c.stackSymbols k)
    rw [BoundedCfg.stackSymbols_congr (c.control l v) c k rfl]

noncomputable def BoundedCfg.pushCell {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ machineSymbols tm)
    (hr : (c.cfg.stk k).length + 1 ≤ capacity) : BoundedCfg tm capacity where
  cfg := { c.cfg with stk := Function.update c.cfg.stk k (a :: c.cfg.stk k) }
  length_bound i := by
    by_cases hi : i = k
    · subst i; simpa using hr
    · simpa [Function.update_of_ne hi] using c.length_bound i
  alphabet i b hb := by
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self, List.mem_cons] at hb
      rcases hb with hb | hb
      · subst b; exact ha
      · exact c.alphabet k b hb
    · exact c.alphabet i b (by simpa [Function.update_of_ne hi] using hb)

noncomputable def BoundedCfg.popCell {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    BoundedCfg tm capacity where
  cfg := { c.cfg with var := f c.cfg.var ((c.cfg.stk k).head?)
                      stk := Function.update c.cfg.stk k (c.cfg.stk k).tail }
  length_bound i := by
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self, List.length_tail]
      have h := c.length_bound k
      omega
    · simpa [Function.update_of_ne hi] using c.length_bound i
  alphabet i a ha := by
    by_cases hi : i = k
    · subst i
      exact c.alphabet k a (List.mem_of_mem_tail (by simpa using ha))
    · exact c.alphabet i a (by simpa [Function.update_of_ne hi] using ha)

/-- The finite interpreter is exact on actual TM2 configurations whenever the proved push margin holds. -/
theorem BoundedCfg.finiteStatement_encode {tm : Turing.FinTM2} {capacity : Nat}
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (c : BoundedCfg tm capacity) (hr : StackRoom capacity q c.cfg.stk) :
    finiteStatement q hq c.encode = (c.execute q hq hr).encode := by
  induction q generalizing c with
  | push k f q ih =>
    have ha := (pushedSymbol k f q hq c.cfg.var).property
    have hp : (c.cfg.stk k).length + 1 ≤ capacity := by
      have h := hr k
      simp only [pushBound] at h
      omega
    let d := c.pushCell k (f c.cfg.var) ha hp
    have hd : d.encode = c.encode.push k (pushedSymbol k f q hq c.cfg.var) :=
      c.encode_push d k (f c.cfg.var) ha rfl rfl rfl
    change finiteStatement q _ (c.encode.push k (pushedSymbol k f q hq c.cfg.var)) = _
    rw [← hd, ih _ d (hr.push c.cfg.var)]
    congr 1
  | peek k f q ih =>
    let d := c.control c.cfg.l (f c.cfg.var (c.cfg.stk k).head?)
    have hd : d.encode = c.encode.peek k f := by
      rw [BoundedCfg.encode_control]
      simp only [FiniteCfg.peek, BoundedCfg.head_encode]
      rfl
    change finiteStatement q hq (c.encode.peek k f) = _
    rw [← hd, ih hq d hr]
    congr 1
  | pop k f q ih =>
    let d := c.popCell k f
    have hd : d.encode = c.encode.pop k f := c.encode_pop d k f rfl rfl rfl
    change finiteStatement q hq (c.encode.pop k f) = _
    rw [← hd, ih hq d hr.pop]
    congr 1
  | load f q ih =>
    let d := c.control c.cfg.l (f c.cfg.var)
    have hd : d.encode = c.encode.load f := c.encode_control _ _
    change finiteStatement q hq (c.encode.load f) = _
    rw [← hd, ih hq d hr]
    congr 1
  | branch f q r ihq ihr =>
    change cond (f c.cfg.var) (finiteStatement q _ c.encode)
      (finiteStatement r _ c.encode) = _
    cases hf : f c.cfg.var
    · simp only [Bool.cond_false]
      rw [ihr _ c hr.branch_right]
      congr 1
      apply BoundedCfg.ext
      simp only [BoundedCfg.execute, Turing.TM2.stepAux, hf, Bool.cond_false]
      rfl
    · simp only [Bool.cond_true]
      rw [ihq _ c hr.branch_left]
      congr 1
      apply BoundedCfg.ext
      simp only [BoundedCfg.execute, Turing.TM2.stepAux, hf, Bool.cond_true]
      rfl
  | goto f =>
    exact (c.encode_control (some (f c.cfg.var)) c.cfg.var).symm
  | halt => exact (c.encode_control none c.cfg.var).symm

end ShiReversibleTM
