import ReversibleConfigurationBits
import ReversibleBooleanFormula

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding ShiReversibleFormula

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

structure FormulaCfg (tm : Turing.FinTM2) (capacity : Nat) (ι : Type) where
  label : Option tm.Λ → Formula ι
  memory : tm.σ → Formula ι
  cells : tm.K → Fin capacity → Option (MachineSymbol tm) → Formula ι

def FormulaCfg.Denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity) : Prop :=
  (∀ l, (p.label l).eval x = oneHot c.label l) ∧
  (∀ v, (p.memory v).eval x = oneHot c.memory v) ∧
  (∀ k i a, (p.cells k i a).eval x = oneHot (c.cells k i) a)

noncomputable def FormulaCfg.inputs (tm : Turing.FinTM2) (capacity : Nat) :
    FormulaCfg tm capacity (Fin (configurationWidth tm capacity)) where
  label l := .input (configurationBitEquiv tm capacity (.inl (.inl l)))
  memory v := .input (configurationBitEquiv tm capacity (.inl (.inr v)))
  cells k i a := .input (configurationBitEquiv tm capacity (.inr ((k, i), a)))

theorem FormulaCfg.inputs_denotes {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : (FormulaCfg.inputs tm capacity).Denotes c.bitEncode c := by
  refine ⟨?_, ?_, ?_⟩
  · intro l; simp [FormulaCfg.inputs, Formula.eval, FiniteCfg.indicators]
  · intro v; simp [FormulaCfg.inputs, Formula.eval, FiniteCfg.indicators]
  · intro k i a; simp [FormulaCfg.inputs, Formula.eval, FiniteCfg.indicators]

noncomputable def FormulaCfg.headCodes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (k : tm.K) : Option (MachineSymbol tm) → Formula ι :=
  fun a => if h : 0 < capacity then p.cells k ⟨0, h⟩ a else .constant (oneHot none a)

theorem FormulaCfg.headCodes_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (k : tm.K) (a : Option (MachineSymbol tm)) :
    (p.headCodes k a).eval x = oneHot (tapeHead (c.cells k)) a := by
  by_cases hc : 0 < capacity
  · simpa [FormulaCfg.headCodes, tapeHead, hc] using h.2.2 k ⟨0, hc⟩ a
  · simp [FormulaCfg.headCodes, tapeHead, hc, Formula.eval]

noncomputable def FormulaCfg.load {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (f : tm.σ → tm.σ) : FormulaCfg tm capacity ι :=
  { p with memory := unaryTable f p.memory }

noncomputable def FormulaCfg.peek {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : FormulaCfg tm capacity ι :=
  { p with memory := binaryTable (fun v a => f v (decodeCellSymbol k a)) p.memory (p.headCodes k) }

noncomputable def FormulaCfg.goto {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (f : tm.σ → tm.Λ) : FormulaCfg tm capacity ι :=
  { p with label := unaryTable (fun v => some (f v)) p.memory }

noncomputable def FormulaCfg.halt {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) : FormulaCfg tm capacity ι :=
  { p with label := fun l => .constant (oneHot none l) }

theorem FormulaCfg.load_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (f : tm.σ → tm.σ) : (p.load f).Denotes x (c.load f) := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro v
  exact eval_unaryTable f p.memory x c.memory v h.2.1

theorem FormulaCfg.peek_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.peek k f).Denotes x (c.peek k f) := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro v
  exact eval_binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes k)
    x c.memory (tapeHead (c.cells k)) v h.2.1 (p.headCodes_denotes x c h k)

theorem FormulaCfg.goto_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (f : tm.σ → tm.Λ) : (p.goto f).Denotes x (c.goto f) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro l
  exact eval_unaryTable (fun v => some (f v)) p.memory x c.memory l h.2.1

theorem FormulaCfg.halt_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) : p.halt.Denotes x c.halt := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro l
  rfl

noncomputable def FormulaCfg.push {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (k : tm.K) (f : tm.σ → MachineSymbol tm) :
    FormulaCfg tm capacity ι :=
  { p with cells := Function.update p.cells k (fun i a =>
      if h : i.val = 0 then unaryTable (fun v => some (f v)) p.memory a
      else p.cells k ⟨i.val - 1, by omega⟩ a) }

noncomputable def FormulaCfg.pop {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : FormulaCfg tm capacity ι :=
  { p.peek k f with cells := Function.update p.cells k (fun i a =>
      if h : i.val + 1 < capacity then p.cells k ⟨i.val + 1, h⟩ a
      else .constant (oneHot none a)) }

theorem FormulaCfg.push_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (k : tm.K) (f : tm.σ → MachineSymbol tm) :
    (p.push k f).Denotes x (c.push k (f c.memory)) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    by_cases hi : i.val = 0
    · simpa [FormulaCfg.push, FiniteCfg.push, tapePush, hi] using
        eval_unaryTable (fun v => some (f v)) p.memory x c.memory a h.2.1
    · simpa [FormulaCfg.push, FiniteCfg.push, tapePush, hi] using
        h.2.2 k ⟨i.val - 1, by omega⟩ a
  · simpa [FormulaCfg.push, FiniteCfg.push, Function.update_of_ne hj] using h.2.2 j i a

theorem FormulaCfg.pop_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.pop k f).Denotes x (c.pop k f) := by
  have hm := (p.peek_denotes x c h k f).2.1
  refine ⟨h.1, hm, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    by_cases hi : i.val + 1 < capacity
    · simpa [FormulaCfg.pop, FiniteCfg.pop, tapePop, hi] using h.2.2 k ⟨i.val + 1, hi⟩ a
    · simp [FormulaCfg.pop, FiniteCfg.pop, tapePop, hi, Formula.eval]
  · simpa [FormulaCfg.pop, FiniteCfg.pop, Function.update_of_ne hj] using h.2.2 j i a

/-- A branch selects each bit with a verified bounded-arity multiplexer. -/
def FormulaCfg.mux {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (selector : Formula ι) (yes no : FormulaCfg tm capacity ι) : FormulaCfg tm capacity ι where
  label l := selector.mux (yes.label l) (no.label l)
  memory v := selector.mux (yes.memory v) (no.memory v)
  cells k i a := selector.mux (yes.cells k i a) (no.cells k i a)

theorem FormulaCfg.mux_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (selector : Formula ι) (yes no : FormulaCfg tm capacity ι) (x : ι → Bool)
    (c d : FiniteCfg tm capacity) (hy : yes.Denotes x c) (hn : no.Denotes x d) :
    (FormulaCfg.mux selector yes no).Denotes x (cond (selector.eval x) c d) := by
  cases hs : selector.eval x
  · simpa [FormulaCfg.mux, FormulaCfg.Denotes, hs] using hn
  · simpa [FormulaCfg.mux, FormulaCfg.Denotes, hs] using hy

end ShiReversibleTM
