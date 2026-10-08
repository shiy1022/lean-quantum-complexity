import ReversibleGuardedProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem guardedProgramTemplate_embeds (r : GuardProgramRegisters R) (g : TickIndexGuard)
    (y n : CounterProgramTemplate R) (hy : y.Embeds) (hn : n.Embeds) :
    (guardedProgramTemplate r g y n).Embeds := by
  intro L caller stop l
  change indexGuardCode g (y.code (n.code caller stop) (n.exit stop))
    r.capacity r.position r.left r.right r.tmp (y.entry (n.exit stop)) (y.exit (n.entry stop))
    (indexGuardExit g (y.exit (n.exit l))) = _
  rw [indexGuardCode_embed, hy, hn]
  cases caller l <;> rfl

/-- The clean guard and either actual branch compose to the same continuation. -/
theorem guardedProgramTemplate_run (r : GuardProgramRegisters R) (g : TickIndexGuard)
    (y n : CounterProgramTemplate R) (hr : r.Valid)
    (hyEmbed : y.Embeds) (hyRun : y.Runs) (hnRun : n.Runs) :
    (guardedProgramTemplate r g y n).Runs := by
  intro L caller stop cs ys hready
  rcases hready with ⟨hl, hn, hx, hyReady, hnReady⟩
  let rightCode := n.code caller stop
  let leftCode := y.code rightCode (n.exit stop)
  let code := (guardedProgramTemplate r g y n).code caller stop
  have hg := indexGuardCode_run g leftCode r.capacity r.position r.left r.right r.tmp
    (y.entry (n.exit stop)) (y.exit (n.entry stop)) hr.capacity_left hr.position_left
    hr.capacity_right hr.position_right hr.capacity_tmp hr.position_tmp hr.left_tmp hr.right_tmp
    hr.left_right cs hl hn hx ys
  cases he : g.eval (cs r.capacity) (cs r.position) with
  | false =>
    simp only [he, Bool.false_eq_true, if_false] at hg
    have hb := hnRun L caller stop cs ys hnReady
    have hb' := CounterRun.relabel rightCode leftCode y.exit
      (fun l => hyEmbed (n.Labels L) rightCode (n.exit stop) l) hb
    have hb'' := CounterRun.relabel leftCode code (indexGuardExit g)
      (fun l => indexGuardCode_embed g leftCode r.capacity r.position r.left r.right r.tmp
        (y.entry (n.exit stop)) (y.exit (n.entry stop)) l) hb'
    have h := CounterRun.trans code hg hb''
    simpa only [guardedProgramTemplate, he, Bool.false_eq_true, if_false, code, leftCode, rightCode,
      CounterCfg.relabel, Option.map_some] using h
  | true =>
    simp only [he, Bool.true_eq, if_true] at hg
    have hb := hyRun (n.Labels L) rightCode (n.exit stop) cs ys hyReady
    have hb' := CounterRun.relabel leftCode code (indexGuardExit g)
      (fun l => indexGuardCode_embed g leftCode r.capacity r.position r.left r.right r.tmp
        (y.entry (n.exit stop)) (y.exit (n.entry stop)) l) hb
    have h := CounterRun.trans code hg hb'
    simpa only [guardedProgramTemplate, he, Bool.true_eq, if_true, code, leftCode, rightCode,
      CounterCfg.relabel, Option.map_some] using h

end ShiReversibleGenerator
