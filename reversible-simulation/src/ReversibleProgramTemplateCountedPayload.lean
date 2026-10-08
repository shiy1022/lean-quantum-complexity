import ReversibleProgramTemplateSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A silent setup and an independently counted payload run compose in the same finite instruction graph. -/
theorem sequenceProgramTemplate_counted_payload_run (p q : CounterProgramTemplate R)
    (he : p.Embeds) (hp : p.Runs) (cs : R → Nat) (hr : p.ready cs) (hb : p.bytes cs=[])
    (L : Type) (caller : L → CounterInstr R L) (stop : L) (ys payload : List Bool)
    (hq : CounterRun (q.code caller stop) ⟨some (q.entry stop),p.counters cs,ys⟩
      (q.steps (p.counters cs)) ⟨some (q.exit stop),q.counters (p.counters cs),payload++ys⟩) :
    CounterRun ((sequenceProgramTemplate p q).code caller stop)
      ⟨some ((sequenceProgramTemplate p q).entry stop),cs,ys⟩
      ((sequenceProgramTemplate p q).steps cs)
      ⟨some ((sequenceProgramTemplate p q).exit stop),
        (sequenceProgramTemplate p q).counters cs,payload++ys⟩ := by
  have h₁ := hp (q.Labels L) (q.code caller stop) (q.entry stop) cs ys hr
  rw [hb,List.nil_append] at h₁
  have h₂ := CounterRun.relabel (q.code caller stop) (p.code (q.code caller stop) (q.entry stop)) p.exit
    (fun l => he (q.Labels L) (q.code caller stop) (q.entry stop) l) hq
  simpa only [sequenceProgramTemplate,CounterCfg.relabel,Option.map_some] using CounterRun.trans _ h₁ h₂

end ShiReversibleGenerator
