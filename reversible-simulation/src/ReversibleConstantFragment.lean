import ReversibleCounterRelabel
import ReversibleCounterMacros

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev ConstantLabel (c : Nat) (L : Type) := Fin c ⊕ L

def constantFrom (c : Nat) (stop : L) (i : Nat) : ConstantLabel c L :=
  if h : i < c then .inl ⟨i, h⟩ else .inr stop

def incrementCode (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L) :
    ConstantLabel c L → CounterInstr R (ConstantLabel c L)
  | .inl i => .inc r (constantFrom c stop (i.val + 1))
  | .inr l => (code l).relabel Sum.inr

def decrementCode (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L) :
    ConstantLabel c L → CounterInstr R (ConstantLabel c L)
  | .inl i => .dec r (constantFrom c stop (i.val + 1))
  | .inr l => (code l).relabel Sum.inr

/-- Constant addition is a finite chain, preserving all other counters and output. -/
theorem increment_span (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L)
    (base : CounterCfg R (ConstantLabel c L)) (k i n : Nat) (hi : i + k = c) :
    CounterRun (incrementCode code c r stop) (withCounter base r n (constantFrom c stop i)) k
      (withCounter base r (n + k) (.inr stop)) := by
  induction k generalizing i n with
  | zero =>
    have he : i = c := by omega
    subst i
    simpa [constantFrom] using CounterRun.refl (withCounter base r n (.inr stop))
  | succ k ih =>
    have hil : i < c := by omega
    have hf : constantFrom c stop i = .inl ⟨i, hil⟩ := dif_pos hil
    rw [hf]
    apply CounterRun.next (code := incrementCode code c r stop) (l := .inl ⟨i, hil⟩) rfl
    simpa [incrementCode, withCounter_inc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (i + 1) (n + 1) (by omega)

/-- Constant truncated subtraction has the same finite exact clock. -/
theorem decrement_span (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L)
    (base : CounterCfg R (ConstantLabel c L)) (k i n : Nat) (hi : i + k = c) :
    CounterRun (decrementCode code c r stop) (withCounter base r n (constantFrom c stop i)) k
      (withCounter base r (n - k) (.inr stop)) := by
  induction k generalizing i n with
  | zero =>
    have he : i = c := by omega
    subst i
    simpa [constantFrom] using CounterRun.refl (withCounter base r n (.inr stop))
  | succ k ih =>
    have hil : i < c := by omega
    have hf : constantFrom c stop i = .inl ⟨i, hil⟩ := dif_pos hil
    rw [hf]
    apply CounterRun.next (code := decrementCode code c r stop) (l := .inl ⟨i, hil⟩) rfl
    simpa [decrementCode, withCounter_dec, Nat.sub_sub, Nat.add_comm]
      using ih (i + 1) (n - 1) (by omega)

theorem incrementCode_run (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L)
    (base : CounterCfg R (ConstantLabel c L)) (n : Nat) :
    CounterRun (incrementCode code c r stop) (withCounter base r n (constantFrom c stop 0)) c
      (withCounter base r (n + c) (.inr stop)) :=
  increment_span code c r stop base c 0 n (by omega)

theorem decrementCode_run (code : L → CounterInstr R L) (c : Nat) (r : R) (stop : L)
    (base : CounterCfg R (ConstantLabel c L)) (n : Nat) :
    CounterRun (decrementCode code c r stop) (withCounter base r (n + c) (constantFrom c stop 0)) c
      (withCounter base r n (.inr stop)) := by
  simpa using decrement_span code c r stop base c 0 (n + c) (by omega)

end ShiReversibleGenerator
