import ReversibleCleanupProgramTemplate
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- Append complete administrative-counter cleanup without changing the emitted circuit. -/
noncomputable def cleanHaltProgramTemplate (p : CounterProgramTemplate R) : CounterProgramTemplate R :=
  sequenceProgramTemplate p (cleanupProgramTemplate (Finset.univ : Finset R).toList)

theorem cleanHaltProgramTemplate_embeds (p : CounterProgramTemplate R) (he : p.Embeds) :
    (cleanHaltProgramTemplate p).Embeds :=
  sequenceProgramTemplate_embeds _ _ he (cleanupProgramTemplate_embeds _)

theorem cleanHaltProgramTemplate_run (p : CounterProgramTemplate R) (he : p.Embeds) (hr : p.Runs) :
    (cleanHaltProgramTemplate p).Runs :=
  sequenceProgramTemplate_run _ _ he hr (cleanupProgramTemplate_run _)

theorem cleanHaltProgramTemplate_ready (p : CounterProgramTemplate R) (cs : R → Nat) :
    (cleanHaltProgramTemplate p).ready cs ↔ p.ready cs := by
  simp [cleanHaltProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate]

theorem cleanHaltProgramTemplate_counters (p : CounterProgramTemplate R) (cs : R → Nat) :
    (cleanHaltProgramTemplate p).counters cs=fun _ => 0 := by
  classical
  funext q
  simp [cleanHaltProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]

theorem cleanHaltProgramTemplate_bytes (p : CounterProgramTemplate R) (cs : R → Nat) :
    (cleanHaltProgramTemplate p).bytes cs=p.bytes cs := by
  simp [cleanHaltProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate]

theorem cleanHaltProgramTemplate_resources (p : CounterProgramTemplate R) (bound : Polynomial Nat)
    (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (cleanHaltProgramTemplate p).CounterBound bound ∧
    (cleanHaltProgramTemplate p).PolynomiallyTimed bound := by
  obtain ⟨middle,hm⟩ := hb
  refine ⟨⟨0,?_⟩,sequenceProgramTemplate_polynomial _ _ bound middle ht
    (fun n cs hc _ => hm n cs hc) (cleanupProgramTemplate_polynomial _ middle)⟩
  intro n cs hc q
  rw [cleanHaltProgramTemplate_counters]
  simp

/-- Include the last halt instruction: every generator counter is zero in the canonical endpoint. -/
theorem cleanHaltProgramTemplate_halted_run (p : CounterProgramTemplate R) (he : p.Embeds) (hr : p.Runs)
    (cs : R → Nat) (ys : List Bool) (hready : p.ready cs) :
    let q := cleanHaltProgramTemplate p
    CounterRun (q.code (fun _ : Unit => .halt) ())
      ⟨some (q.entry ()),cs,ys⟩ (q.steps cs+1) ⟨none,fun _ => 0,p.bytes cs++ys⟩ := by
  let q := cleanHaltProgramTemplate p
  have h := cleanHaltProgramTemplate_run p he hr Unit (fun _ => .halt) () cs ys
    ((cleanHaltProgramTemplate_ready p cs).2 hready)
  rw [cleanHaltProgramTemplate_counters,cleanHaltProgramTemplate_bytes] at h
  have hend : CounterRun (q.code (fun _ : Unit => .halt) ())
      ⟨some (q.exit ()),fun _ => 0,p.bytes cs++ys⟩ 1
      ⟨none,fun _ => 0,p.bytes cs++ys⟩ := by
    have hstep := CounterRun.one (q.code (fun _ : Unit => .halt) ())
      (⟨some (q.exit ()),fun _ => 0,p.bytes cs++ys⟩ : CounterCfg R (q.Labels Unit)) (q.exit ()) rfl
    have hhalt : q.code (fun _ : Unit => .halt) () (q.exit ())=.halt := by
      change (cleanHaltProgramTemplate p).code (fun _ : Unit => .halt) ()
        ((cleanHaltProgramTemplate p).exit ())=.halt
      rw [cleanHaltProgramTemplate_embeds p he Unit (fun _ => .halt) () ()]
      rfl
    simpa only [hhalt,CounterInstr.eval] using hstep
  exact CounterRun.trans _ h hend

end ShiReversibleGenerator
