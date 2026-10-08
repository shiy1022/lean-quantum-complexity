import ReversibleWireEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev CnotEmissionLabel (L : Type) :=
  NatEmissionLabel (WireEmissionLabel (ShiBQP.encNat 1 ++ ShiBQP.encNat 4) L)

def cnotEmissionCode (code : L → CounterInstr R L) (r q buf tmp : R) (stop : L) :
    CnotEmissionLabel L → CounterInstr R (CnotEmissionLabel L) :=
  natEmissionCode
    (wireEmissionCode (ShiBQP.encNat 1 ++ ShiBQP.encNat 4) code r buf tmp stop)
    q buf tmp (.inl 0)

/-- Print target, then source, then the fixed layer/opcode header. No counter changes. -/
theorem cnotEmissionCode_run (code : L → CounterInstr R L) (r q buf tmp : R) (stop : L)
    (hrb : r ≠ buf) (hrt : r ≠ tmp) (hqb : q ≠ buf) (hqt : q ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (cnotEmissionCode code r q buf tmp stop) ⟨some (.inl 0), cs, ys⟩
      (10 * cs q + 10 * cs r + 15)
      ⟨some (.inr (.inr (.inr (.inr (.inr stop))))), cs,
        (ShiBQP.encNat 1 ++ ShiBQP.encNat 4 ++ ShiBQP.encNat (cs r) ++
          ShiBQP.encNat (cs q)) ++ ys⟩ := by
  let inner := wireEmissionCode (ShiBQP.encNat 1 ++ ShiBQP.encNat 4) code r buf tmp stop
  let prg := cnotEmissionCode code r q buf tmp stop
  have hq := natEmissionCode_run_preserved inner q buf tmp (.inl 0) hqb hqt hbt cs hb ht ys
  have hr := wireEmissionCode_run_preserved (ShiBQP.encNat 1 ++ ShiBQP.encNat 4)
    code r buf tmp stop hrb hrt hbt cs hb ht (ShiBQP.encNat (cs q) ++ ys)
  have hx := CounterRun.relabel inner prg (fun l => .inr (.inr l)) (fun _ => rfl) hr
  have h := CounterRun.trans prg hq hx
  convert h using 1 <;> (try simp [prg, CounterCfg.relabel, ShiBQP.encNat, List.append_assoc]) <;> first | rfl | omega

/-- The emitted CNOT bytes agree exactly with the established circuit encoding. -/
theorem cnotLayer_run {m : Nat} (i j : Fin m) (hij : i ≠ j)
    (code : L → CounterInstr R L) (r q buf tmp : R) (stop : L)
    (hrb : r ≠ buf) (hrt : r ≠ tmp) (hqb : q ≠ buf) (hqt : q ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hi : cs r = i.val) (hj : cs q = j.val)
    (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (cnotEmissionCode code r q buf tmp stop) ⟨some (.inl 0), cs, ys⟩
      (10 * j.val + 10 * i.val + 15)
      ⟨some (.inr (.inr (.inr (.inr (.inr stop))))), cs,
        ShiBQP.encLayer [.cnot i j hij] ++ ys⟩ := by
  have h := cnotEmissionCode_run code r q buf tmp stop hrb hrt hqb hqt hbt cs hb ht ys
  simpa [hi, hj, encLayer_singleton, ShiBQP.encInstr, List.append_assoc] using h

theorem cnotEmissionCode_clock_polynomial (source target : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      10 * target.eval n + 10 * source.eval n + 15 = p.eval n := by
  refine ⟨Polynomial.C 10 * target + Polynomial.C 10 * source + Polynomial.C 15, ?_⟩
  intro n
  simp

end ShiReversibleGenerator
