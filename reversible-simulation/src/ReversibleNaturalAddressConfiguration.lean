import ReversibleConfigurationRenaming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

/-- The address type and configuration fields do not depend on runtime capacity. -/
structure NaturalFormulaCfg (tm : Turing.FinTM2) (ι : Type) where
  label : Option tm.Λ → Formula ι
  memory : tm.σ → Formula ι
  cells : tm.K → Nat → Option (MachineSymbol tm) → Formula ι

variable {tm : Turing.FinTM2} {ι : Type}

def NaturalFormulaCfg.restrict (p : NaturalFormulaCfg tm ι) (capacity : Nat) :
    FormulaCfg tm capacity ι where
  label := p.label
  memory := p.memory
  cells k i := p.cells k i.val

noncomputable def NaturalFormulaCfg.headCodes (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) : Option (MachineSymbol tm) → Formula ι :=
  fun a => if 0 < capacity then p.cells k 0 a else .constant (oneHot none a)

noncomputable def NaturalFormulaCfg.load (p : NaturalFormulaCfg tm ι)
    (f : tm.σ → tm.σ) : NaturalFormulaCfg tm ι :=
  { p with memory := unaryTable f p.memory }

noncomputable def NaturalFormulaCfg.peek (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) : NaturalFormulaCfg tm ι :=
  { p with memory := binaryTable (fun v a => f v (decodeCellSymbol k a)) p.memory (p.headCodes capacity k) }

noncomputable def NaturalFormulaCfg.goto (p : NaturalFormulaCfg tm ι)
    (f : tm.σ → tm.Λ) : NaturalFormulaCfg tm ι :=
  { p with label := unaryTable (fun v => some (f v)) p.memory }

noncomputable def NaturalFormulaCfg.halt (p : NaturalFormulaCfg tm ι) : NaturalFormulaCfg tm ι :=
  { p with label := fun l => .constant (oneHot none l) }

noncomputable def NaturalFormulaCfg.push (p : NaturalFormulaCfg tm ι)
    (k : tm.K) (f : tm.σ → MachineSymbol tm) : NaturalFormulaCfg tm ι :=
  { p with cells := Function.update p.cells k (fun i a =>
      if i = 0 then unaryTable (fun v => some (f v)) p.memory a else p.cells k (i - 1) a) }

/-- The explicit capacity check discards the cell beyond the bounded stack. -/
noncomputable def NaturalFormulaCfg.pop (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) : NaturalFormulaCfg tm ι :=
  { p.peek capacity k f with cells := Function.update p.cells k (fun i a =>
      if i + 1 < capacity then p.cells k (i + 1) a else .constant (oneHot none a)) }

def NaturalFormulaCfg.mux (s : Formula ι) (p q : NaturalFormulaCfg tm ι) : NaturalFormulaCfg tm ι where
  label l := s.mux (p.label l) (q.label l)
  memory v := s.mux (p.memory v) (q.memory v)
  cells k i a := s.mux (p.cells k i a) (q.cells k i a)

theorem NaturalFormulaCfg.restrict_headCodes (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) : (p.restrict capacity).headCodes k = p.headCodes capacity k := by
  funext a
  unfold FormulaCfg.headCodes NaturalFormulaCfg.headCodes
  split <;> rfl

theorem NaturalFormulaCfg.restrict_load (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (f : tm.σ → tm.σ) :
    (p.load f).restrict capacity = (p.restrict capacity).load f := by rfl

theorem NaturalFormulaCfg.restrict_peek (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.peek capacity k f).restrict capacity = (p.restrict capacity).peek k f := by
  apply FormulaCfg.fields_ext
  · rfl
  · change (fun v => binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes capacity k) v) =
      (fun v => binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory ((p.restrict capacity).headCodes k) v)
    rw [p.restrict_headCodes]
  · rfl

theorem NaturalFormulaCfg.restrict_goto (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (f : tm.σ → tm.Λ) :
    (p.goto f).restrict capacity = (p.restrict capacity).goto f := by rfl

theorem NaturalFormulaCfg.restrict_halt (p : NaturalFormulaCfg tm ι) (capacity : Nat) :
    p.halt.restrict capacity = (p.restrict capacity).halt := by rfl

theorem NaturalFormulaCfg.restrict_mux (s : Formula ι) (p q : NaturalFormulaCfg tm ι)
    (capacity : Nat) : (NaturalFormulaCfg.mux s p q).restrict capacity =
      FormulaCfg.mux s (p.restrict capacity) (q.restrict capacity) := by rfl

theorem NaturalFormulaCfg.restrict_push (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) (f : tm.σ → MachineSymbol tm) :
    (p.push k f).restrict capacity = (p.restrict capacity).push k f := by
  classical
  apply FormulaCfg.fields_ext
  · rfl
  · rfl
  · funext j i a
    by_cases hj : j = k
    · subst j
      simp only [NaturalFormulaCfg.restrict, NaturalFormulaCfg.push, FormulaCfg.push,
        Function.update_self]
      split <;> rfl
    · simp [NaturalFormulaCfg.restrict, NaturalFormulaCfg.push, FormulaCfg.push,
        Function.update_of_ne hj]

theorem NaturalFormulaCfg.restrict_pop (p : NaturalFormulaCfg tm ι)
    (capacity : Nat) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.pop capacity k f).restrict capacity = (p.restrict capacity).pop k f := by
  classical
  apply FormulaCfg.fields_ext
  · rfl
  · simpa only [NaturalFormulaCfg.pop, NaturalFormulaCfg.restrict, FormulaCfg.pop] using
      congrArg FormulaCfg.memory (p.restrict_peek capacity k f)
  · funext j i a
    by_cases hj : j = k
    · subst j
      simp only [NaturalFormulaCfg.restrict, NaturalFormulaCfg.pop, FormulaCfg.pop,
        Function.update_self]
      split <;> rfl
    · simp [NaturalFormulaCfg.restrict, NaturalFormulaCfg.pop, NaturalFormulaCfg.peek,
        FormulaCfg.pop, FormulaCfg.peek, Function.update_of_ne hj]

end ShiReversibleTM
