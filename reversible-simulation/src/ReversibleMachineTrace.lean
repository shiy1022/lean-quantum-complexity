import ReversibleMachineBounds
import ReversibleMachineAlphabet
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiReversibleTM

local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
local instance (tm : Turing.FinTM2) : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin

noncomputable def machinePushBound (tm : Turing.FinTM2) : Nat :=
  Finset.univ.sup (fun l => pushBound (tm.m l))

/-- Padded execution leaves halted configurations unchanged. -/
def tick (tm : Turing.FinTM2) (c : tm.Cfg) : tm.Cfg :=
  match c.l with
  | none => c
  | some l => Turing.TM2.stepAux (tm.m l) c.var c.stk

def advance (tm : Turing.FinTM2) : Nat → tm.Cfg → tm.Cfg
  | 0, c => c
  | t + 1, c => tick tm (advance tm t c)

theorem tick_stack_length (tm : Turing.FinTM2) (c : tm.Cfg) (i : tm.K) :
    ((tick tm c).stk i).length ≤ (c.stk i).length + machinePushBound tm := by
  classical
  cases h : c.l with
  | none => simp [tick, h]
  | some l =>
    have hs := stepAux_stack_length (tm.m l) c.var c.stk i
    have hb : pushBound (tm.m l) ≤ machinePushBound tm :=
      Finset.le_sup (f := fun l => pushBound (tm.m l)) (Finset.mem_univ l)
    simpa [tick, h] using hs.trans (Nat.add_le_add_left hb _)

theorem advance_stack_length (tm : Turing.FinTM2) (t : Nat) (c : tm.Cfg) (i : tm.K) :
    ((advance tm t c).stk i).length ≤ (c.stk i).length + t * machinePushBound tm := by
  induction t with
  | zero => simp [advance]
  | succ t ih =>
    have hs := tick_stack_length tm (advance tm t c) i
    have h := hs.trans (Nat.add_le_add_right ih (machinePushBound tm))
    simpa [advance, Nat.succ_mul, Nat.add_assoc] using h

theorem tick_halted (tm : Turing.FinTM2) (c : tm.Cfg) (h : c.l = none) : tick tm c = c := by
  simp [tick, h]

theorem advance_halted (tm : Turing.FinTM2) (t : Nat) (c : tm.Cfg) (h : c.l = none) :
    advance tm t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => simp [advance, ih, tick_halted tm c h]

noncomputable def machineSymbols (tm : Turing.FinTM2) : Finset (Σ k, tm.Γ k) := by
  classical
  exact (Finset.univ.image (fun a : tm.Γ tm.k₀ => (⟨tm.k₀, a⟩ : Σ k, tm.Γ k))) ∪
    Finset.univ.biUnion (fun l => pushSymbols (tm.m l))

theorem machineSymbols_contains_push (tm : Turing.FinTM2) (l : tm.Λ) :
    pushSymbols (tm.m l) ⊆ machineSymbols tm := by
  classical
  intro z hz
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hz⟩)

theorem tick_alphabet (tm : Turing.FinTM2) (c : tm.Cfg)
    (h : StackAlphabet (machineSymbols tm) c.stk) :
    StackAlphabet (machineSymbols tm) (tick tm c).stk := by
  cases hl : c.l with
  | none => simpa [tick, hl] using h
  | some l =>
    simpa [tick, hl] using stepAux_alphabet (tm.m l) (machineSymbols tm)
      (machineSymbols_contains_push tm l) c.var c.stk h

theorem initial_alphabet (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₀)) :
    StackAlphabet (machineSymbols tm) (Turing.initList tm xs).stk := by
  classical
  intro k a ha
  by_cases hk : k = tm.k₀
  · subst k
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  · simp [Turing.initList, hk] at ha

theorem advance_alphabet (tm : Turing.FinTM2) (t : Nat) (xs : List (tm.Γ tm.k₀)) :
    StackAlphabet (machineSymbols tm) (advance tm t (Turing.initList tm xs)).stk := by
  induction t with
  | zero => exact initial_alphabet tm xs
  | succ t ih => exact tick_alphabet tm _ ih

theorem initial_stack_length (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₀)) (i : tm.K) :
    ((Turing.initList tm xs).stk i).length ≤ xs.length := by
  by_cases hi : i = tm.k₀
  · subst i; simp [Turing.initList]
  · simp [Turing.initList, hi]

theorem initial_trace_stack_length (tm : Turing.FinTM2) (t : Nat)
    (xs : List (tm.Γ tm.k₀)) (i : tm.K) :
    ((advance tm t (Turing.initList tm xs)).stk i).length ≤
      xs.length + t * machinePushBound tm := by
  exact (advance_stack_length tm t _ i).trans
    (Nat.add_le_add_right (initial_stack_length tm xs i) _)

end ShiReversibleTM
