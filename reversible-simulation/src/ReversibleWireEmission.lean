import ReversibleLiteralEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev WireEmissionLabel (header : List Bool) (L : Type) :=
  NatEmissionLabel (LiteralLabel header L)

def wireEmissionCode (header : List Bool) (code : L → CounterInstr R L)
    (r buf tmp : R) (stop : L) :
    WireEmissionLabel header L → CounterInstr R (WireEmissionLabel header L) :=
  natEmissionCode (literalCode header code stop) r buf tmp (literalPointer header stop 0)

/-- A fixed header followed by a variable address, printed by one finite program. -/
theorem wireEmissionCode_run (header : List Bool) (code : L → CounterInstr R L)
    (r buf tmp : R) (stop : L) (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (base : CounterCfg R (WireEmissionLabel header L)) (n : Nat) :
    CounterRun (wireEmissionCode header code r buf tmp stop)
      (natEmissionState base r buf tmp n 0 base.output (.inl 0))
      (10 * n + 4 + header.length)
      (natEmissionState base r buf tmp n 0
        ((header ++ ShiBQP.encNat n) ++ base.output) (.inr (.inr (.inr stop)))) := by
  let prg := wireEmissionCode header code r buf tmp stop
  have hn := natEmissionCode_run (literalCode header code stop) r buf tmp
    (literalPointer header stop 0) hrb hrt hbt base n
  let cs := (natEmissionState base r buf tmp n 0 base.output (.inl 0)).counters
  have hl := literalCode_run header code stop cs (printedNat n ++ base.output)
  have hx := CounterRun.relabel (literalCode header code stop) prg
    (fun l => .inr (.inr l)) (fun _ => rfl) hl
  have ht := CounterRun.trans prg hn hx
  simpa [prg, CounterCfg.relabel, cs, natEmissionState, copyState, List.append_assoc] using ht

/-- Canonical emission states agree with caller registers when scratch is zero. -/
theorem natEmissionState_preserved (base : CounterCfg R L) (r buf tmp : R)
    (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (hb : base.counters buf = 0) (ht : base.counters tmp = 0) (ys : List Bool) (pc : L) :
    natEmissionState base r buf tmp (base.counters r) 0 ys pc =
      ⟨some pc, base.counters, ys⟩ := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hjt : j = tmp
    · subst j; simp [natEmissionState, copyState, ht]
    · by_cases hjb : j = buf
      · subst j; simp [natEmissionState, copyState, hb, hbt]
      · by_cases hjr : j = r
        · subst j; simp [natEmissionState, copyState, hrb, hrt]
        · simp [natEmissionState, copyState, hjt, hjb, hjr]
  · rfl

theorem natEmissionCode_run_preserved (code : L → CounterInstr R L) (r buf tmp : R)
    (stop : L) (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (natEmissionCode code r buf tmp stop) ⟨some (.inl 0), cs, ys⟩
      (10 * cs r + 4) ⟨some (.inr (.inr stop)), cs, ShiBQP.encNat (cs r) ++ ys⟩ := by
  have h := natEmissionCode_run code r buf tmp stop hrb hrt hbt
    ⟨some (.inl 0), cs, ys⟩ (cs r)
  simpa only [natEmissionState_preserved (⟨some (.inl 0), cs, ys⟩ : CounterCfg R (NatEmissionLabel L)) r buf tmp hrb hrt hbt hb ht,
    printedNat_eq_encNat] using h

theorem wireEmissionCode_run_preserved (header : List Bool) (code : L → CounterInstr R L)
    (r buf tmp : R) (stop : L) (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (wireEmissionCode header code r buf tmp stop) ⟨some (.inl 0), cs, ys⟩
      (10 * cs r + 4 + header.length)
      ⟨some (.inr (.inr (.inr stop))), cs, (header ++ ShiBQP.encNat (cs r)) ++ ys⟩ := by
  have h := wireEmissionCode_run header code r buf tmp stop hrb hrt hbt
    ⟨some (.inl 0), cs, ys⟩ (cs r)
  simpa only [natEmissionState_preserved (⟨some (.inl 0), cs, ys⟩ : CounterCfg R (WireEmissionLabel header L)) r buf tmp hrb hrt hbt hb ht] using h

/-- The four one-wire instructions in the established gate set. -/
def oneWireInstr {m : Nat} (tag : Fin 4) (i : Fin m) : ShiShallow.Instr m :=
  match tag.val with
  | 0 => .h i
  | 1 => .s i
  | 2 => .t i
  | _ => .x i

@[simp] theorem encInstr_oneWire {m : Nat} (tag : Fin 4) (i : Fin m) :
    ShiBQP.encInstr (oneWireInstr tag i) = ShiBQP.encNat tag.val ++ ShiBQP.encNat i.val := by
  fin_cases tag <;> rfl

/-- Actual finite emission of a singleton H/S/T/X layer in the unchanged encoding. -/
theorem oneWireLayer_run {m : Nat} (tag : Fin 4) (i : Fin m)
    (code : L → CounterInstr R L) (r buf tmp : R) (stop : L)
    (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (base : CounterCfg R (WireEmissionLabel (ShiBQP.encNat 1 ++ ShiBQP.encNat tag.val) L)) :
    CounterRun (wireEmissionCode (ShiBQP.encNat 1 ++ ShiBQP.encNat tag.val) code r buf tmp stop)
      (natEmissionState base r buf tmp i.val 0 base.output (.inl 0))
      (10 * i.val + tag.val + 7)
      (natEmissionState base r buf tmp i.val 0
        (ShiBQP.encLayer [oneWireInstr tag i] ++ base.output) (.inr (.inr (.inr stop)))) := by
  have h := wireEmissionCode_run (ShiBQP.encNat 1 ++ ShiBQP.encNat tag.val) code
    r buf tmp stop hrb hrt hbt base i.val
  convert h using 1 <;> (try simp [encLayer_singleton, ShiBQP.encNat, List.append_assoc]) <;> first | rfl | omega

theorem wireEmissionCode_clock_polynomial (header : List Bool) (size : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n, 10 * size.eval n + 4 + header.length = p.eval n := by
  refine ⟨Polynomial.C 10 * size + Polynomial.C (4 + header.length), ?_⟩
  intro n
  simp [Nat.add_assoc]

end ShiReversibleGenerator
