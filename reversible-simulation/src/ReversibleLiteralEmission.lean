import ReversibleNatEmission
import ReversibleEstablishedBQP

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Emit a fixed execution-order list, preserving every counter. -/
theorem emit_sequence_run (code : L → CounterInstr R L) (bits : List Bool)
    (ptr : Nat → L) (hc : ∀ i (h : i < bits.length),
      code (ptr i) = .emit bits[i] (ptr (i + 1)))
    (cs : R → Nat) (ys : List Bool) :
    CounterRun code ⟨some (ptr 0), cs, ys⟩ bits.length
      ⟨some (ptr bits.length), cs, bits.reverse ++ ys⟩ := by
  induction bits generalizing ptr ys with
  | nil => exact CounterRun.refl _
  | cons b bs ih =>
    have hc' : ∀ i (h : i < bs.length),
        code (ptr (i + 1)) = .emit bs[i] (ptr (i + 1 + 1)) := by
      intro i h
      exact hc (i + 1) (by simp; omega)
    have hr := ih (fun i => ptr (i + 1)) hc' (b :: ys)
    have hs := CounterRun.next (code := code) (s := ⟨some (ptr 0), cs, ys⟩) rfl
      (by simpa [hc 0 (by simp), CounterInstr.eval] using hr)
    simpa [List.reverse_cons, List.append_assoc] using hs

/-- Fixed literals are part of the finite program, never dependent on input length. -/
abbrev LiteralLabel (bits : List Bool) (L : Type) := Fin bits.length ⊕ L

def literalPointer (bits : List Bool) (stop : L) (i : Nat) : LiteralLabel bits L :=
  if h : i < bits.length then .inl ⟨i, h⟩ else .inr stop

def literalCode (bits : List Bool) (code : L → CounterInstr R L) (stop : L) :
    LiteralLabel bits L → CounterInstr R (LiteralLabel bits L)
  | .inl j => .emit ((bits.reverse)[j.val]'(by simpa using j.isLt))
      (literalPointer bits stop (j.val + 1))
  | .inr l => (code l).relabel Sum.inr

/-- Exact serialized literal, with no counter mutation and an explicit return label. -/
theorem literalCode_run (bits : List Bool) (code : L → CounterInstr R L) (stop : L)
    (cs : R → Nat) (ys : List Bool) :
    CounterRun (literalCode bits code stop)
      ⟨some (literalPointer bits stop 0), cs, ys⟩ bits.length
      ⟨some (.inr stop), cs, bits ++ ys⟩ := by
  have h := emit_sequence_run (literalCode bits code stop) bits.reverse
    (literalPointer bits stop) (by
      intro i hi
      simp only [List.length_reverse] at hi
      simp [literalPointer, hi, literalCode]) cs ys
  simpa [literalPointer] using h

@[simp] theorem printedNat_eq_encNat (n : Nat) : printedNat n = ShiBQP.encNat n := rfl

/-- Singleton layer framing is the established unary list-length header. -/
theorem encLayer_singleton {m : Nat} (g : ShiShallow.Instr m) :
    ShiBQP.encLayer [g] = ShiBQP.encNat 1 ++ ShiBQP.encInstr g := by
  simp [ShiBQP.encLayer, ShiBQP.encStr]

/-- Size of instruction serialization is linear in its wire addresses. -/
theorem encInstr_length {m : Nat} (g : ShiShallow.Instr m) :
    (ShiBQP.encInstr g).length ≤ 2 * m + 5 := by
  cases g <;> simp [ShiBQP.encInstr, ShiBQP.encNat] <;> omega

end ShiReversibleGenerator
