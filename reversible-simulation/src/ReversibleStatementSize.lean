import ReversibleStatementCircuit

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

def FormulaCfg.SizeBound {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (b : Nat) : Prop :=
  1 ≤ b ∧ (∀ l, (p.label l).size ≤ b) ∧ (∀ v, (p.memory v).size ≤ b) ∧
    (∀ k i a, (p.cells k i a).size ≤ b)

noncomputable def primitiveSizeBound (tm : Turing.FinTM2) (b : Nat) : Nat :=
  b + 1 + Fintype.card tm.σ * (b + 6) +
    Fintype.card (Option (MachineSymbol tm)) * Fintype.card tm.σ * (b + b + 7)

theorem primitiveSizeBound_ge (tm : Turing.FinTM2) (b : Nat) : b ≤ primitiveSizeBound tm b := by
  unfold primitiveSizeBound
  omega

theorem FormulaCfg.SizeBound.unary {tm : Turing.FinTM2} {capacity : Nat} {ι β : Type}
    [DecidableEq β] {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (f : tm.σ → β) (a : β) :
    (unaryTable f p.memory a).size ≤ primitiveSizeBound tm b := by
  have hs := size_unaryTable f p.memory a b h.2.2.1
  unfold primitiveSizeBound
  omega

theorem FormulaCfg.SizeBound.head {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (k : tm.K) (a : Option (MachineSymbol tm)) : (p.headCodes k a).size ≤ b := by
  by_cases hc : 0 < capacity
  · simpa [FormulaCfg.headCodes, hc] using h.2.2.2 k ⟨0, hc⟩ a
  · simpa [FormulaCfg.headCodes, hc, Formula.size] using h.1

theorem FormulaCfg.SizeBound.peekMemory {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) (v : tm.σ) :
    ((p.peek k f).memory v).size ≤ primitiveSizeBound tm b := by
  have hs := size_binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes k)
    v b b h.2.2.1 (h.head k)
  change (binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes k) v).size ≤ _
  unfold primitiveSizeBound
  rw [Nat.mul_comm (Fintype.card (Option (MachineSymbol tm))) (Fintype.card tm.σ)]
  omega

theorem FormulaCfg.SizeBound.load {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b) (f : tm.σ → tm.σ) :
    (p.load f).SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  exact ⟨h.1.trans hb, fun l => (h.2.1 l).trans hb, h.unary f,
    fun k i a => (h.2.2.2 k i a).trans hb⟩

theorem FormulaCfg.SizeBound.peek {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.peek k f).SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  exact ⟨h.1.trans hb, fun l => (h.2.1 l).trans hb, h.peekMemory k f,
    fun j i a => (h.2.2.2 j i a).trans hb⟩

theorem FormulaCfg.SizeBound.goto {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b) (f : tm.σ → tm.Λ) :
    (p.goto f).SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  exact ⟨h.1.trans hb, h.unary (fun v => some (f v)),
    fun v => (h.2.2.1 v).trans hb, fun k i a => (h.2.2.2 k i a).trans hb⟩

theorem FormulaCfg.SizeBound.halt {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b) :
    p.halt.SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  exact ⟨h.1.trans hb, fun _ => h.1.trans hb,
    fun v => (h.2.2.1 v).trans hb, fun k i a => (h.2.2.2 k i a).trans hb⟩

theorem FormulaCfg.SizeBound.push {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (k : tm.K) (f : tm.σ → MachineSymbol tm) :
    (p.push k f).SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  refine ⟨h.1.trans hb, fun l => (h.2.1 l).trans hb,
    fun v => (h.2.2.1 v).trans hb, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    by_cases hi : i.val = 0
    · simpa [FormulaCfg.push, hi] using h.unary (fun v => some (f v)) a
    · simpa [FormulaCfg.push, hi] using (h.2.2.2 k ⟨i.val - 1, by omega⟩ a).trans hb
  · simpa [FormulaCfg.push, Function.update_of_ne hj] using (h.2.2.2 j i a).trans hb

theorem FormulaCfg.SizeBound.pop {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p : FormulaCfg tm capacity ι} {b : Nat} (h : p.SizeBound b)
    (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.pop k f).SizeBound (primitiveSizeBound tm b) := by
  have hb := primitiveSizeBound_ge tm b
  refine ⟨h.1.trans hb, fun l => (h.2.1 l).trans hb, h.peekMemory k f, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    by_cases hi : i.val + 1 < capacity
    · simpa [FormulaCfg.pop, hi] using (h.2.2.2 k ⟨i.val + 1, hi⟩ a).trans hb
    · simpa [FormulaCfg.pop, hi, Formula.size] using h.1.trans hb
  · simpa [FormulaCfg.pop, Function.update_of_ne hj] using (h.2.2.2 j i a).trans hb

theorem FormulaCfg.SizeBound.mux {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    {p q : FormulaCfg tm capacity ι} {b c d : Nat} {s : Formula ι}
    (hp : p.SizeBound b) (hq : q.SizeBound c) (hs : s.size ≤ d) :
    (FormulaCfg.mux s p q).SizeBound (2 * d + b + c + 7) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro l; change (s.mux (p.label l) (q.label l)).size ≤ _
    rw [Formula.size_mux]; have h₁ := hp.2.1 l; have h₂ := hq.2.1 l; omega
  · intro v; change (s.mux (p.memory v) (q.memory v)).size ≤ _
    rw [Formula.size_mux]; have h₁ := hp.2.2.1 v; have h₂ := hq.2.2.1 v; omega
  · intro k i a; change (s.mux (p.cells k i a) (q.cells k i a)).size ≤ _
    rw [Formula.size_mux]; have h₁ := hp.2.2.2 k i a; have h₂ := hq.2.2.2 k i a; omega

/-- This bound depends on the fixed machine and statement, never on stack capacity. -/
noncomputable def statementSizeBound (tm : Turing.FinTM2) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat → Nat
  | .push _ _ q, b => statementSizeBound tm q (primitiveSizeBound tm b)
  | .peek _ _ q, b => statementSizeBound tm q (primitiveSizeBound tm b)
  | .pop _ _ q, b => statementSizeBound tm q (primitiveSizeBound tm b)
  | .load _ q, b => statementSizeBound tm q (primitiveSizeBound tm b)
  | .branch _ q r, b => 2 * primitiveSizeBound tm b + statementSizeBound tm q b +
      statementSizeBound tm r b + 7
  | .goto _, b => primitiveSizeBound tm b
  | .halt, b => primitiveSizeBound tm b

theorem statementFormulas_size {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (p : FormulaCfg tm capacity ι) (b : Nat) (h : p.SizeBound b) :
    (statementFormulas q hq p).SizeBound (statementSizeBound tm q b) := by
  induction q generalizing p b with
  | push k f q ih => exact ih _ _ _ (h.push k (pushedSymbol k f q hq))
  | peek k f q ih => exact ih _ _ _ (h.peek k f)
  | pop k f q ih => exact ih _ _ _ (h.pop k f)
  | load f q ih => exact ih _ _ _ (h.load f)
  | branch f q r ihq ihr =>
    exact FormulaCfg.SizeBound.mux (ihq _ _ _ h) (ihr _ _ _ h) (h.unary f true)
  | goto f => exact h.goto f
  | halt => exact h.halt

theorem FormulaCfg.inputs_size (tm : Turing.FinTM2) (capacity : Nat) :
    (FormulaCfg.inputs tm capacity).SizeBound 1 := by
  exact ⟨by omega, fun _ => by rfl, fun _ => by rfl, fun _ _ _ => by rfl⟩

theorem statementForest_size {tm : Turing.FinTM2} (capacity : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm) :
    ∀ p ∈ statementForest capacity q hq, p.size ≤ statementSizeBound tm q 1 := by
  have h := statementFormulas_size q hq (FormulaCfg.inputs tm capacity) 1
    (FormulaCfg.inputs_size tm capacity)
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  unfold FormulaCfg.bitFormula
  cases (configurationBitEquiv tm capacity).symm i with
  | inl z => cases z with
    | inl l => exact h.2.1 l
    | inr v => exact h.2.2.1 v
  | inr z => exact h.2.2.2 z.1.1 z.1.2 z.2

/-- A linear size bound in configuration width for each fixed actual machine statement. -/
theorem statementCircuit_size {tm : Turing.FinTM2} (capacity : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm) :
    (forestCircuit (statementForest capacity q hq)).reversible.length ≤
      4 * configurationWidth tm capacity * statementSizeBound tm q 1 + configurationWidth tm capacity := by
  simpa only [statementForest_length] using forestCircuit_size_bound
    (statementForest capacity q hq) (statementSizeBound tm q 1) (statementForest_size capacity q hq)

end ShiReversibleTM
