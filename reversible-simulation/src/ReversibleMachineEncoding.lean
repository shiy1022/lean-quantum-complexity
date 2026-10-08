import ReversibleMachineTrace
import ReversibleBoundedTape
import ReversibleFiniteCodec
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _

abbrev MachineSymbol (tm : Turing.FinTM2) := ↥(machineSymbols tm)

/-- The bounded configurations needed by the Boolean transition compiler. -/
@[ext] structure BoundedCfg (tm : Turing.FinTM2) (capacity : Nat) where
  cfg : tm.Cfg
  length_bound : ∀ k, (cfg.stk k).length ≤ capacity
  alphabet : StackAlphabet (machineSymbols tm) cfg.stk

@[ext] structure FiniteCfg (tm : Turing.FinTM2) (capacity : Nat) where
  label : Option tm.Λ
  memory : tm.σ
  cells : tm.K → Fin capacity → Option (MachineSymbol tm)

noncomputable def BoundedCfg.stackSymbols {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) : List (MachineSymbol tm) :=
  (c.cfg.stk k).attach.map (fun a => ⟨⟨k, a.val⟩, c.alphabet k a.val a.property⟩)

@[simp] theorem BoundedCfg.stackSymbols_length {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) : (c.stackSymbols k).length = (c.cfg.stk k).length := by
  simp [BoundedCfg.stackSymbols]

def decodeStackSymbols {tm : Turing.FinTM2} (k : tm.K)
    (xs : List (MachineSymbol tm)) : List (tm.Γ k) :=
  xs.filterMap (fun a => if h : a.val.1 = k then some (h ▸ a.val.2) else none)

@[simp] theorem decodeStackSymbols_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) : decodeStackSymbols k (c.stackSymbols k) = c.cfg.stk k := by
  simp [decodeStackSymbols, BoundedCfg.stackSymbols, List.filterMap_map, Function.comp_def]

noncomputable def BoundedCfg.encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) : FiniteCfg tm capacity where
  label := c.cfg.l
  memory := c.cfg.var
  cells k := tapeEncode capacity (c.stackSymbols k)

def FiniteCfg.decode {tm : Turing.FinTM2} {capacity : Nat} (c : FiniteCfg tm capacity) : tm.Cfg where
  l := c.label
  var := c.memory
  stk k := decodeStackSymbols k (tapeDecode (c.cells k))

@[simp] theorem BoundedCfg.decode_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) : c.encode.decode = c.cfg := by
  have hs : (fun k => decodeStackSymbols k (tapeDecode (c.encode.cells k))) = c.cfg.stk := by
    funext k
    rw [BoundedCfg.encode, tapeDecode_encode]
    · exact decodeStackSymbols_encode c k
    · simpa using c.length_bound k
  change Turing.TM2.Cfg.mk c.cfg.l c.cfg.var _ = c.cfg
  rw [hs]
  cases c.cfg
  rfl

theorem BoundedCfg.encode_injective {tm : Turing.FinTM2} {capacity : Nat} :
    Function.Injective (BoundedCfg.encode (tm := tm) (capacity := capacity)) := by
  intro c d h
  have he := congrArg FiniteCfg.decode h
  simp only [BoundedCfg.decode_encode] at he
  cases c
  cases d
  cases he
  rfl

noncomputable def stackCellEquiv (tm : Turing.FinTM2) (capacity : Nat) :
    tm.K × Fin capacity ≃ Fin (Fintype.card tm.K * capacity) :=
  (Equiv.prodCongr (Fintype.equivFin tm.K) (Equiv.refl (Fin capacity))).trans finProdFinEquiv

noncomputable def FiniteCfg.cellList {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : List (Option (MachineSymbol tm)) :=
  List.ofFn (fun i => c.cells ((stackCellEquiv tm capacity).symm i).1
    ((stackCellEquiv tm capacity).symm i).2)

noncomputable def configurationWidth (tm : Turing.FinTM2) (capacity : Nat) : Nat := by
  classical
  exact Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
    Fintype.card tm.K * capacity * Fintype.card (Option (MachineSymbol tm))

noncomputable def FiniteCfg.serialize {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : List Bool := by
  classical
  exact oneHotList c.label ++ oneHotList c.memory ++ c.cellList.flatMap oneHotList

theorem flatMap_fixed_length {α β : Type} (f : α → List β) (width : Nat)
    (h : ∀ a, (f a).length = width) (xs : List α) :
    (xs.flatMap f).length = xs.length * width := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

theorem FiniteCfg.serialize_length {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : c.serialize.length = configurationWidth tm capacity := by
  classical
  unfold FiniteCfg.serialize
  rw [List.length_append, List.length_append,
    flatMap_fixed_length _ _ (fun a => oneHotList_length a)]
  simp [FiniteCfg.cellList, configurationWidth]

theorem configurationWidth_affine (tm : Turing.FinTM2) :
    ∃ a b : Nat, ∀ capacity, configurationWidth tm capacity = a * capacity + b := by
  classical
  refine ⟨Fintype.card tm.K * Fintype.card (Option (MachineSymbol tm)),
    Fintype.card (Option tm.Λ) + Fintype.card tm.σ, ?_⟩
  intro capacity
  simp only [configurationWidth]
  ring

noncomputable def boundedTrace (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t ≤ budget) :
    BoundedCfg tm (xs.length + budget * machinePushBound tm + 1) where
  cfg := advance tm t (Turing.initList tm xs)
  length_bound k := by
    have h := initial_trace_stack_length tm t xs k
    have hm := Nat.mul_le_mul_right (machinePushBound tm) ht
    omega
  alphabet := advance_alphabet tm t xs

/-- Before a budgeted step, there is room for every push in its statement tree. -/
theorem trace_statement_margin (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t < budget) (l : tm.Λ) (k : tm.K) :
    ((advance tm t (Turing.initList tm xs)).stk k).length + pushBound (tm.m l) <
      xs.length + budget * machinePushBound tm + 1 := by
  classical
  have hs := initial_trace_stack_length tm t xs k
  have hb : pushBound (tm.m l) ≤ machinePushBound tm :=
    Finset.le_sup (f := fun l => pushBound (tm.m l)) (Finset.mem_univ l)
  have hm := Nat.mul_le_mul_right (machinePushBound tm) (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at hm
  omega

end ShiReversibleTM
