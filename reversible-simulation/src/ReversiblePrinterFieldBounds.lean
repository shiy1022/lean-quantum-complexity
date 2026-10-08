import ReversibleFormulaPrinterRun

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem FixedNodeTemplate.counters_fields (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (hs : t.StableSources r) (cs : R → Nat) :
    t.counters r cs r.p = t.x.eval cs ∧ t.counters r cs r.q = t.y.eval cs ∧ t.counters r cs r.r = t.z.eval cs := by
  rcases hs with ⟨⟨hxp, hxq, hxr, hxc⟩, ⟨hyp, hyq, hyr, hyc⟩, ⟨hzp, hzq, hzr, hzc⟩⟩
  simp only [FixedNodeTemplate.counters, FixedNodeTemplate.fields]
  rw [nodeFieldResult_eval t.x t.y t.z r.p r.q r.r hpq hpr hqr
    ⟨hxp, hxq, hxr⟩ ⟨hyp, hyq, hyr⟩ ⟨hzp, hzq, hzr⟩]
  simp [Ne.symm hcp, Ne.symm hcq, Ne.symm hcr, hpq, hpr, hqr]

theorem SymbolicWire.eval_template_counters (w : SymbolicWire R) (t : FixedNodeTemplate R)
    (r : NodePrinterRegisters R)
    (hp : w.source ≠ r.p) (hq : w.source ≠ r.q) (hr : w.source ≠ r.r)
    (hc : w.source ≠ r.count) (cs : R → Nat) :
    w.eval (t.counters r cs) = w.eval cs := by
  simp only [SymbolicWire.eval, t.counters_other r w.source hp hq hr hc]

/-- Field registers are reset by a nonempty fixed printer, independent of their old values. -/
theorem fixedNodeCounters_fields_bound (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (hs : ∀ t ∈ ts, t.StableSources r) (hne : ts ≠ []) (cs : R → Nat) (bound : Nat)
    (hb : ∀ t ∈ ts, t.x.eval cs ≤ bound ∧ t.y.eval cs ≤ bound ∧ t.z.eval cs ≤ bound) :
    fixedNodeCounters r ts cs r.p ≤ bound ∧ fixedNodeCounters r ts cs r.q ≤ bound ∧
      fixedNodeCounters r ts cs r.r ≤ bound := by
  induction ts generalizing cs with
  | nil => exact False.elim (hne rfl)
  | cons t ts ih =>
      by_cases ht : ts = []
      · subst ts
        have hf := t.counters_fields r hpq hpr hqr hcp hcq hcr (hs t (by simp)) cs
        simpa only [fixedNodeCounters, hf.1, hf.2.1, hf.2.2] using hb t (by simp)
      · apply ih (fun u hu => hs u (by simp [hu])) ht (t.counters r cs)
        intro u hu
        have hs' := hs u (by simp [hu])
        have hb' := hb u (by simp [hu])
        rcases hs' with ⟨⟨hxp, hxq, hxr, hxc⟩, ⟨hyp, hyq, hyr, hyc⟩, ⟨hzp, hzq, hzr, hzc⟩⟩
        simpa only [u.x.eval_template_counters t r hxp hxq hxr hxc,
          u.y.eval_template_counters t r hyp hyq hyr hyc,
          u.z.eval_template_counters t r hzp hzq hzr hzc] using hb'

end ShiReversibleGenerator
