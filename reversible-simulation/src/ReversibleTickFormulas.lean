import ReversibleStatementSize

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

/-- Dispatch always reads the original label and executes from the original configuration. -/
noncomputable def finiteDispatch {tm : Turing.FinTM2} {capacity : Nat} :
    List tm.Λ → FiniteCfg tm capacity → FiniteCfg tm capacity
  | [], c => c
  | l :: ls, c => cond (oneHot c.label (some l))
      (finiteStatement (tm.m l) (machineSymbols_contains_push tm l) c) (finiteDispatch ls c)

noncomputable def dispatchFormulas {tm : Turing.FinTM2} {capacity : Nat} {ι : Type} :
    List tm.Λ → FormulaCfg tm capacity ι → FormulaCfg tm capacity ι
  | [], p => p
  | l :: ls, p => FormulaCfg.mux (p.label (some l))
      (statementFormulas (tm.m l) (machineSymbols_contains_push tm l) p) (dispatchFormulas ls p)

theorem dispatchFormulas_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (ls : List tm.Λ) (p : FormulaCfg tm capacity ι) (x : ι → Bool)
    (c : FiniteCfg tm capacity) (h : p.Denotes x c) :
    (dispatchFormulas ls p).Denotes x (finiteDispatch ls c) := by
  induction ls with
  | nil => exact h
  | cons l ls ih =>
    simpa only [dispatchFormulas, finiteDispatch, h.1 (some l)] using
      FormulaCfg.mux_denotes (p.label (some l)) _ _ x _ _
        (statementFormulas_denotes _ _ p x c h) ih

theorem finiteDispatch_halted {tm : Turing.FinTM2} {capacity : Nat}
    (ls : List tm.Λ) (c : FiniteCfg tm capacity) (h : c.label = none) :
    finiteDispatch ls c = c := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simpa [finiteDispatch, oneHot, h] using ih

theorem finiteDispatch_active {tm : Turing.FinTM2} {capacity : Nat}
    (ls : List tm.Λ) (c : FiniteCfg tm capacity) (l : tm.Λ)
    (h : c.label = some l) (hm : l ∈ ls) :
    finiteDispatch ls c = finiteStatement (tm.m l) (machineSymbols_contains_push tm l) c := by
  induction ls with
  | nil => simp at hm
  | cons j ls ih =>
    by_cases hj : l = j
    · subst j
      simp [finiteDispatch, oneHot, h]
    · have ht : l ∈ ls := by simpa [hj] using hm
      simpa [finiteDispatch, oneHot, h, hj] using ih ht

noncomputable def finiteTick {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : FiniteCfg tm capacity := finiteDispatch Finset.univ.toList c

noncomputable def tickFormulas {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) : FormulaCfg tm capacity ι := dispatchFormulas Finset.univ.toList p

theorem tickFormulas_denotes {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) : (tickFormulas p).Denotes x (finiteTick c) :=
  dispatchFormulas_denotes _ p x c h

/-- All statement interiors fit at this tick, including either branch. -/
def TickRoom {tm : Turing.FinTM2} (capacity : Nat) (c : tm.Cfg) : Prop :=
  ∀ k, (c.stk k).length + machinePushBound tm ≤ capacity

theorem TickRoom.statement {tm : Turing.FinTM2} {capacity : Nat} {c : tm.Cfg}
    (h : TickRoom capacity c) (l : tm.Λ) : StackRoom capacity (tm.m l) c.stk := by
  classical
  intro k
  exact (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushBound (tm.m l))
    (Finset.mem_univ l)) _).trans (h k)

noncomputable def BoundedCfg.tick {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (h : TickRoom capacity c.cfg) : BoundedCfg tm capacity where
  cfg := ShiReversibleTM.tick tm c.cfg
  length_bound k := (tick_stack_length tm c.cfg k).trans (h k)
  alphabet := tick_alphabet tm c.cfg c.alphabet

/-- Finite-label dispatch simulates the actual machine tick; a halted configuration is preserved. -/
theorem BoundedCfg.finiteTick_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (h : TickRoom capacity c.cfg) :
    finiteTick c.encode = (c.tick h).encode := by
  cases hl : c.cfg.l with
  | none =>
    have he : c.encode.label = none := hl
    rw [finiteTick, finiteDispatch_halted _ c.encode he]
    congr 1
    apply BoundedCfg.ext
    simp [BoundedCfg.tick, ShiReversibleTM.tick, hl]
  | some l =>
    have he : c.encode.label = some l := hl
    rw [finiteTick, finiteDispatch_active _ c.encode l he (by simp)]
    rw [c.finiteStatement_encode _ _ (h.statement l)]
    congr 1
    apply BoundedCfg.ext
    simp only [BoundedCfg.execute, BoundedCfg.tick, ShiReversibleTM.tick, hl]
    rfl

noncomputable def dispatchSizeBound (tm : Turing.FinTM2) : List tm.Λ → Nat → Nat
  | [], b => b
  | l :: ls, b => 2 * b + statementSizeBound tm (tm.m l) b + dispatchSizeBound tm ls b + 7

theorem dispatchFormulas_size {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (ls : List tm.Λ) (p : FormulaCfg tm capacity ι) (b : Nat) (h : p.SizeBound b) :
    (dispatchFormulas ls p).SizeBound (dispatchSizeBound tm ls b) := by
  induction ls with
  | nil => exact h
  | cons l ls ih =>
    exact FormulaCfg.SizeBound.mux (statementFormulas_size _ _ p b h) ih (h.2.1 (some l))

noncomputable def tickSizeBound (tm : Turing.FinTM2) : Nat := dispatchSizeBound tm Finset.univ.toList 1

theorem tickFormulas_size (tm : Turing.FinTM2) (capacity : Nat) :
    (tickFormulas (FormulaCfg.inputs tm capacity)).SizeBound (tickSizeBound tm) :=
  dispatchFormulas_size _ _ 1 (FormulaCfg.inputs_size tm capacity)

end ShiReversibleTM
