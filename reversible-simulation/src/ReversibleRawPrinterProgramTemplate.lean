import ReversibleCounterOutputSuffix
import ReversibleNaturalPolynomialMonotone
import ReversibleTemplateRegisterInjectionRun
import ReversibleCounterRunExitBudget
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R] [DecidableEq L] [Fintype L]

/-- A fixed raw-length printer is packaged for finite continuation composition. Its proof remains an actual counted run. -/
noncomputable def rawPrinterProgramTemplate (code : L → CounterInstr R L) (entry exit : L) (input : R)
    (initial final : Nat → R → Nat) (count : Nat → Nat) (payload : Nat → List Bool) : CounterProgramTemplate R where
  Labels := fun M => L ⊕ M
  finite := fun M fm => by letI := fm; infer_instance
  code := fun caller stop => chainedCounterCode code caller exit stop input
  entry := fun _ => .inl entry
  exit := Sum.inr
  ready := fun cs => cs=initial (cs input)
  steps := fun cs => count (cs input)+1
  counters := fun cs => final (cs input)
  bytes := fun cs => payload (cs input)

theorem rawPrinterProgramTemplate_embeds (code : L → CounterInstr R L) (entry exit : L) (input : R)
    (initial final : Nat → R → Nat) (count : Nat → Nat) (payload : Nat → List Bool) :
    (rawPrinterProgramTemplate code entry exit input initial final count payload).Embeds := by
  intro M caller stop l
  rfl

theorem rawPrinterProgramTemplate_run (code : L → CounterInstr R L) (entry exit : L) (input : R)
    (initial final : Nat → R → Nat) (count : Nat → Nat) (payload : Nat → List Bool)
    (hhalt : code exit=.halt)
    (hr : ∀ n,CounterRun code ⟨some entry,initial n,[]⟩ (count n) ⟨some exit,final n,payload n⟩) :
    (rawPrinterProgramTemplate code entry exit input initial final count payload).Runs := by
  intro M caller stop cs ys hc
  let n := cs input
  have hfirst := CounterRun.appendOutput code (hr n) ys
  change CounterRun code ⟨some entry,initial n,ys⟩ (count n) ⟨some exit,final n,payload n++ys⟩ at hfirst
  have hsecond := CounterRun.refl (code := caller) (⟨some stop,final n,payload n++ys⟩ : CounterCfg R M)
  have h := chainedCounterCode_run code caller exit stop input hhalt _ (final n) (payload n++ys)
    _ (count n) 0 hfirst hsecond
  rw [←hc] at h
  simpa only [rawPrinterProgramTemplate,CounterCfg.relabel,Option.map_some,Nat.add_zero] using h

/-- A polynomial clock composed with an ambient input bound is still a polynomial. -/
theorem rawPrinterProgramTemplate_polynomial (code : L → CounterInstr R L) (entry exit : L) (input : R)
    (initial final : Nat → R → Nat) (count : Nat → Nat) (payload : Nat → List Bool)
    (clock bound : Polynomial Nat) (ht : ∀ n,count n ≤ clock.eval n) :
    (rawPrinterProgramTemplate code entry exit input initial final count payload).PolynomiallyTimed bound := by
  refine ⟨clock.comp bound+Polynomial.C 1,?_⟩
  intro n cs hb hc
  have h := (ht (cs input)).trans (naturalPolynomial_eval_mono clock _ _ (hb input))
  simpa only [rawPrinterProgramTemplate,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_comp]
    using Nat.add_le_add_right h 1

/-- Ready or not, the selected output counters obey a polynomial bound derived from the certified raw run. -/
theorem rawPrinterProgramTemplate_budget (code : L → CounterInstr R L) (entry exit : L) (input : R)
    (initial final : Nat → R → Nat) (count : Nat → Nat) (payload : Nat → List Bool)
    (clock bound : Polynomial Nat) (ht : ∀ n,count n ≤ clock.eval n)
    (hi : ∀ n q,initial n q ≤ n)
    (hr : ∀ n,CounterRun code ⟨some entry,initial n,[]⟩ (count n) ⟨some exit,final n,payload n⟩) :
    (rawPrinterProgramTemplate code entry exit input initial final count payload).CounterBound bound := by
  refine ⟨bound+clock.comp bound,?_⟩
  intro n cs hb q
  have hf := CounterRun.counter_le _ (hr (cs input)) q
  have hcount := (ht (cs input)).trans (naturalPolynomial_eval_mono clock _ _ (hb input))
  have hinit := (hi (cs input) q).trans (hb input)
  change final (cs input) q ≤ initial (cs input) q+count (cs input) at hf
  simpa only [rawPrinterProgramTemplate,Polynomial.eval_add,Polynomial.eval_comp] using
    hf.trans (Nat.add_le_add hinit hcount)

end ShiReversibleGenerator
