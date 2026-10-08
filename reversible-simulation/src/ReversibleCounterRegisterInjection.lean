import ReversibleCounterRegisterExtension

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R S L : Type}

def CounterInstr.mapRegisters (f : R → S) : CounterInstr R L → CounterInstr S L
  | .inc r l => .inc (f r) l
  | .dec r l => .dec (f r) l
  | .branch r l m => .branch (f r) l m
  | .emit b l => .emit b l
  | .halt => .halt

def CounterCfg.pullRegisters (f : R → S) (s : CounterCfg S L) : CounterCfg R L :=
  ⟨s.pc,fun r => s.counters (f r),s.output⟩

/-- Injective register translation preserves each actual instruction on the original counters. -/
theorem CounterInstr.eval_pullRegisters [DecidableEq R] [DecidableEq S]
    (f : R → S) (hf : Function.Injective f) (instr : CounterInstr R L) (s : CounterCfg S L) :
    ((instr.mapRegisters f).eval s).pullRegisters f=instr.eval (s.pullRegisters f) := by
  cases instr with
  | inc r l | dec r l =>
    apply CounterCfg.ext
    · rfl
    · funext q
      simp [CounterInstr.eval,CounterInstr.mapRegisters,CounterCfg.pullRegisters,Function.update_apply,hf.eq_iff]
    · rfl
  | branch r l m => rfl
  | emit b l => rfl
  | halt => rfl

/-- Lift a counted program run into an ambient register file without changing its instruction clock. -/
theorem CounterRun.mapRegisters [DecidableEq R] [DecidableEq S]
    (f : R → S) (hf : Function.Injective f) (code : L → CounterInstr R L)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t)
    (ambient : CounterCfg S L) (hstart : ambient.pullRegisters f=s) :
    ∃ final,CounterRun (fun l => (code l).mapRegisters f) ambient k final ∧ final.pullRegisters f=t := by
  induction h generalizing ambient with
  | refl => exact ⟨ambient,CounterRun.refl _,hstart⟩
  | @next s d k l hl rest ih =>
    have hstep : (((code l).mapRegisters f).eval ambient).pullRegisters f=(code l).eval s := by
      rw [CounterInstr.eval_pullRegisters f hf,hstart]
    obtain ⟨final,hfinal,hpull⟩ := ih _ hstep
    refine ⟨final,CounterRun.next ?_ hfinal,hpull⟩
    have hp := congrArg CounterCfg.pc hstart
    exact hp.trans hl

/-- Every ambient counter outside the injection's image is framed by each instruction. -/
theorem CounterInstr.eval_mapRegisters_outside [DecidableEq S]
    (f : R → S) (instr : CounterInstr R L) (s : CounterCfg S L) (q : S)
    (hq : ∀ r,f r ≠ q) : ((instr.mapRegisters f).eval s).counters q=s.counters q := by
  cases instr <;> simp [CounterInstr.mapRegisters,CounterInstr.eval,Function.update_of_ne,fun r => Ne.symm (hq r)]

theorem CounterRun.mapRegisters_outside [DecidableEq S]
    (f : R → S) (code : L → CounterInstr R L)
    {s t : CounterCfg S L} {k : Nat} (h : CounterRun (fun l => (code l).mapRegisters f) s k t)
    (q : S) (hq : ∀ r,f r ≠ q) : t.counters q=s.counters q := by
  induction h with
  | refl => rfl
  | @next s d k l hl rest ih =>
    exact ih.trans (CounterInstr.eval_mapRegisters_outside f (code l) s q hq)

end ShiReversibleGenerator
