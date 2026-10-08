import ReversibleMachineEncoding
import ReversibleTapeHead

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding

/-- Decode a finite tagged cell for the stack being read. Wrong tags and padding decode to empty. -/
def decodeCellSymbol {tm : Turing.FinTM2} (k : tm.K) :
    Option (MachineSymbol tm) → Option (tm.Γ k)
  | none => none
  | some a => if h : a.val.1 = k then some (h ▸ a.val.2) else none

@[simp] theorem decodeCellSymbol_tag {tm : Turing.FinTM2} (k : tm.K) (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ machineSymbols tm) :
    decodeCellSymbol k (some ⟨⟨k, a⟩, ha⟩) = some a := by
  simp [decodeCellSymbol]

def FiniteCfg.head {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (k : tm.K) : Option (tm.Γ k) :=
  decodeCellSymbol k (tapeHead (c.cells k))

def FiniteCfg.push {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (k : tm.K) (a : MachineSymbol tm) : FiniteCfg tm capacity :=
  { c with cells := Function.update c.cells k (tapePush a (c.cells k)) }

def FiniteCfg.pop {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : FiniteCfg tm capacity :=
  { c with memory := f c.memory (c.head k)
           cells := Function.update c.cells k (tapePop (c.cells k)) }

def FiniteCfg.peek {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : FiniteCfg tm capacity :=
  { c with memory := f c.memory (c.head k) }

def FiniteCfg.load {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (f : tm.σ → tm.σ) : FiniteCfg tm capacity :=
  { c with memory := f c.memory }

def FiniteCfg.goto {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (f : tm.σ → tm.Λ) : FiniteCfg tm capacity :=
  { c with label := some (f c.memory) }

def FiniteCfg.halt {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : FiniteCfg tm capacity := { c with label := none }

@[simp] theorem BoundedCfg.head_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) : c.encode.head k = (c.cfg.stk k).head? := by
  unfold FiniteCfg.head BoundedCfg.encode
  rw [tapeHead_encode capacity (c.stackSymbols k) (by simpa using c.length_bound k)]
  simp only [BoundedCfg.stackSymbols, List.head?_map]
  have hop (z : Option { a : tm.Γ k // a ∈ c.cfg.stk k }) :
      decodeCellSymbol k (z.map (fun a =>
        (⟨⟨k, a.val⟩, c.alphabet k a.val a.property⟩ : MachineSymbol tm))) =
      z.map Subtype.val := by
    cases z <;> simp [decodeCellSymbol]
  rw [hop]
  exact (List.head?_map).symm.trans
    (congrArg List.head? (List.attach_map_subtype_val (c.cfg.stk k)))

/-- Canonical cell codes depend on stack contents, not on alphabet proof witnesses. -/
theorem BoundedCfg.stackSymbols_congr {tm : Turing.FinTM2} {capacity : Nat}
    (c d : BoundedCfg tm capacity) (k : tm.K) (h : c.cfg.stk k = d.cfg.stk k) :
    c.stackSymbols k = d.stackSymbols k := by
  apply List.ext_getElem
  · simp [BoundedCfg.stackSymbols, h]
  · intro i hi hj
    apply Subtype.ext
    simp [BoundedCfg.stackSymbols, h]

theorem BoundedCfg.stackSymbols_cons {tm : Turing.FinTM2} {capacity : Nat}
    (c d : BoundedCfg tm capacity) (k : tm.K) (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ machineSymbols tm)
    (h : d.cfg.stk k = a :: c.cfg.stk k) :
    d.stackSymbols k = (⟨⟨k, a⟩, ha⟩ : MachineSymbol tm) :: c.stackSymbols k := by
  apply List.ext_getElem
  · simp [BoundedCfg.stackSymbols, h]
  · intro i hi hj
    apply Subtype.ext
    cases i with
    | zero => simp [BoundedCfg.stackSymbols, h]
    | succ i => simp [BoundedCfg.stackSymbols, h]

theorem BoundedCfg.stackSymbols_tail {tm : Turing.FinTM2} {capacity : Nat}
    (c d : BoundedCfg tm capacity) (k : tm.K) (h : d.cfg.stk k = (c.cfg.stk k).tail) :
    d.stackSymbols k = (c.stackSymbols k).tail := by
  apply List.ext_getElem
  · simp [BoundedCfg.stackSymbols, h]
  · intro i hi hj
    apply Subtype.ext
    simp [BoundedCfg.stackSymbols, h]

/-- Every finite-cell push agrees with the actual stack update when the new configuration fits. -/
theorem BoundedCfg.encode_push {tm : Turing.FinTM2} {capacity : Nat}
    (c d : BoundedCfg tm capacity) (k : tm.K) (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ machineSymbols tm)
    (hl : d.cfg.l = c.cfg.l) (hv : d.cfg.var = c.cfg.var)
    (hs : d.cfg.stk = Function.update c.cfg.stk k (a :: c.cfg.stk k)) :
    d.encode = c.encode.push k ⟨⟨k, a⟩, ha⟩ := by
  apply FiniteCfg.ext
  · exact hl
  · exact hv
  · funext j
    by_cases hj : j = k
    · subst j
      have hc : d.cfg.stk k = a :: c.cfg.stk k := by simp [hs]
      simp only [BoundedCfg.encode, FiniteCfg.push, Function.update_self]
      rw [BoundedCfg.stackSymbols_cons c d k a ha hc, tapePush_encode]
    · have hc : c.cfg.stk j = d.cfg.stk j := by simp [hs, Function.update_of_ne hj]
      simp only [BoundedCfg.encode, FiniteCfg.push, Function.update_of_ne hj]
      rw [BoundedCfg.stackSymbols_congr c d j hc]

/-- Empty-stack and nonempty-stack pop behavior are both represented by the same finite shift. -/
theorem BoundedCfg.encode_pop {tm : Turing.FinTM2} {capacity : Nat}
    (c d : BoundedCfg tm capacity) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ)
    (hl : d.cfg.l = c.cfg.l) (hv : d.cfg.var = f c.cfg.var (c.cfg.stk k).head?)
    (hs : d.cfg.stk = Function.update c.cfg.stk k (c.cfg.stk k).tail) :
    d.encode = c.encode.pop k f := by
  apply FiniteCfg.ext
  · exact hl
  · change d.cfg.var = f c.cfg.var (c.encode.head k)
    rw [BoundedCfg.head_encode]
    exact hv
  · funext j
    by_cases hj : j = k
    · subst j
      have hc : d.cfg.stk k = (c.cfg.stk k).tail := by simp [hs]
      simp only [BoundedCfg.encode, FiniteCfg.pop, Function.update_self]
      rw [BoundedCfg.stackSymbols_tail c d k hc,
        tapePop_encode capacity (c.stackSymbols k) (by simpa using c.length_bound k)]
    · have hc : c.cfg.stk j = d.cfg.stk j := by simp [hs, Function.update_of_ne hj]
      simp only [BoundedCfg.encode, FiniteCfg.pop, Function.update_of_ne hj]
      rw [BoundedCfg.stackSymbols_congr c d j hc]

end ShiReversibleTM
