import ReversibleFinalCleanup
import ReversibleArithmeticSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev AddressBindingLabels (positive coefficient negative : Nat) (L : Type) :=
  ClearLabel (AffineLabel positive coefficient (ConstantLabel negative L))

/-- Replace one address register by coefficient*source+positive-negative. -/
def addressBindingCode (caller : L → CounterInstr R L) (source target tmp : R)
    (positive coefficient negative : Nat) (stop : L) :
    AddressBindingLabels positive coefficient negative L →
      CounterInstr R (AddressBindingLabels positive coefficient negative L) :=
  let dec := decrementCode caller negative target stop
  let arith := affineCode dec positive coefficient source target tmp (constantFrom negative stop 0)
  clearCode target arith (affineStart positive coefficient (constantFrom negative stop 0))

theorem addressBindingCode_run (caller : L → CounterInstr R L) (source target tmp : R)
    (positive coefficient negative : Nat) (stop : L)
    (hst : source ≠ target) (hsx : source ≠ tmp) (htx : target ≠ tmp)
    (cs : R → Nat) (hx : cs tmp = 0) (ys : List Bool) :
    CounterRun (addressBindingCode caller source target tmp positive coefficient negative stop)
      ⟨some (.inl 0), cs, ys⟩
      (((2 * cs target + 1) + (coefficient * (7 * cs source + 2) + positive)) + negative)
      ⟨some (.inr (.inr (.inr (.inr stop)))),
        Function.update cs target (coefficient * cs source + positive - negative), ys⟩ := by
  let dec := decrementCode caller negative target stop
  let decStart := constantFrom negative stop 0
  let arith := affineCode dec positive coefficient source target tmp decStart
  let arithStart := affineStart positive coefficient decStart
  let code := addressBindingCode caller source target tmp positive coefficient negative stop
  let cs₀ := Function.update cs target 0
  let value := coefficient * cs source + positive
  have hc := clearCode_run target arith arithStart cs ys
  have ha := AffineAtom.run (⟨source, target, positive, coefficient⟩ : AffineAtom R)
    dec tmp decStart ⟨hst, hsx, htx⟩ cs₀ (by simp [cs₀, Ne.symm htx, hx]) ys
  have ha' := CounterRun.relabel arith code Sum.inr (fun _ => rfl) ha
  have heval : (⟨source, target, positive, coefficient⟩ : AffineAtom R).apply cs₀ =
      Function.update cs target value := by
    simp [AffineAtom.apply, cs₀, value, hst]
  rw [heval] at ha'
  change CounterRun code ⟨some (.inr arithStart), cs₀, ys⟩
    (coefficient * (7 * cs₀ source + 2) + positive)
    ⟨some (.inr (.inr (.inr decStart))), Function.update cs target value, ys⟩ at ha'
  have hd := decrement_span caller negative target stop
    (⟨none, cs, ys⟩ : CounterCfg R (ConstantLabel negative L)) negative 0 value (by omega)
  have hd' := CounterRun.relabel dec arith (fun l => .inr (.inr l))
    (fun l => by
      change ((dec l).relabel Sum.inr).relabel Sum.inr = _
      cases dec l <;> rfl) hd
  have hd'' := CounterRun.relabel arith code Sum.inr (fun _ => rfl) hd'
  change CounterRun code ⟨some (.inr (.inr (.inr decStart))), Function.update cs target value, ys⟩ negative
    ⟨some (.inr (.inr (.inr (.inr stop)))), Function.update cs target (value - negative), ys⟩ at hd''
  have h := CounterRun.trans code (CounterRun.trans code hc ha') hd''
  simpa [cs₀, value, hst] using h

theorem addressBinding_clock (sourceSize targetSize : Polynomial Nat)
    (positive coefficient negative : Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (((2 * targetSize.eval n + 1) +
        (coefficient * (7 * sourceSize.eval n + 2) + positive)) + negative) = p.eval n := by
  refine ⟨((Polynomial.C 2 * targetSize + Polynomial.C 1) +
    (Polynomial.C coefficient * (Polynomial.C 7 * sourceSize + Polynomial.C 2) +
      Polynomial.C positive)) + Polynomial.C negative, ?_⟩
  intro n; simp

theorem addressBinding_value_bound (source positive coefficient negative : Nat) :
    coefficient * source + positive - negative ≤ coefficient * source + positive := Nat.sub_le _ _

end ShiReversibleGenerator
