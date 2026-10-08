import ReversibleTickOutputPreparationBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

noncomputable def sequenceProgramTemplate (p q : CounterProgramTemplate R) : CounterProgramTemplate R where
  Labels := fun L => p.Labels (q.Labels L)
  finite := fun L f => p.finite (q.Labels L) (q.finite L f)
  code := fun caller stop => p.code (q.code caller stop) (q.entry stop)
  entry := fun stop => p.entry (q.entry stop)
  exit := fun stop => p.exit (q.exit stop)
  ready := fun cs => p.ready cs ∧ q.ready (p.counters cs)
  steps := fun cs => p.steps cs + q.steps (p.counters cs)
  counters := fun cs => q.counters (p.counters cs)
  bytes := fun cs => q.bytes (p.counters cs) ++ p.bytes cs

theorem sequenceProgramTemplate_embeds (p q : CounterProgramTemplate R) (hp : p.Embeds) (hq : q.Embeds) :
    (sequenceProgramTemplate p q).Embeds := by
  intro L caller stop l
  change p.code (q.code caller stop) (q.entry stop) (p.exit (q.exit l)) = _
  rw [hp, hq]
  cases caller l <;> rfl

theorem sequenceProgramTemplate_run (p q : CounterProgramTemplate R) (he : p.Embeds)
    (hp : p.Runs) (hq : q.Runs) : (sequenceProgramTemplate p q).Runs := by
  intro L caller stop cs ys hready
  have h₁ := hp (q.Labels L) (q.code caller stop) (q.entry stop) cs ys hready.1
  have h₂ := hq L caller stop (p.counters cs) (p.bytes cs ++ ys) hready.2
  have h₂' := CounterRun.relabel (q.code caller stop) (p.code (q.code caller stop) (q.entry stop)) p.exit
    (fun l => he (q.Labels L) (q.code caller stop) (q.entry stop) l) h₂
  have h := CounterRun.trans (p.code (q.code caller stop) (q.entry stop)) h₁ h₂'
  simpa only [sequenceProgramTemplate, CounterCfg.relabel, Option.map_some, List.append_assoc] using h

theorem sequenceProgramTemplate_polynomial (p q : CounterProgramTemplate R)
    (bound afterBound : Polynomial Nat) (hp : p.PolynomiallyTimed bound)
    (hafter : ∀ n (cs : R → Nat), (∀ r, cs r ≤ bound.eval n) → p.ready cs →
      ∀ r, p.counters cs r ≤ afterBound.eval n)
    (hq : q.PolynomiallyTimed afterBound) : (sequenceProgramTemplate p q).PolynomiallyTimed bound := by
  obtain ⟨cp, hp⟩ := hp
  obtain ⟨cq, hq⟩ := hq
  refine ⟨cp + cq, ?_⟩
  intro n cs hb hr
  exact (by simpa only [sequenceProgramTemplate, Polynomial.eval_add] using
    Nat.add_le_add (hp n cs hb hr.1) (hq n (p.counters cs) (hafter n cs hb hr.1) hr.2))

end ShiReversibleGenerator
