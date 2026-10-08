import ReversibleGuardedProgramClock

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Every real counter instruction increases any given counter by at most one. -/
theorem CounterInstr.eval_counter_le (i : CounterInstr R L) (s : CounterCfg R L) (q : R) :
    (i.eval s).counters q ≤ s.counters q+1 := by
  cases i <;> simp [CounterInstr.eval,Function.update_apply]
  all_goals split_ifs <;> simp_all <;> omega

theorem CounterRun.counter_le (code : L → CounterInstr R L) {s d : CounterCfg R L} {t : Nat}
    (h : CounterRun code s t d) : ∀ q,d.counters q ≤ s.counters q+t := by
  induction h with
  | refl => intro q; simp
  | @next s d t l hl rest ih =>
    intro q
    have hr := ih q
    have hi := CounterInstr.eval_counter_le (code l) s q
    omega

/-- A checked finite run and polynomial real instruction clock provide a polynomial exit budget on ready inputs. -/
theorem CounterProgramTemplate.ready_exit_budget (p : CounterProgramTemplate R)
    (hr : p.Runs) (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    ∃ budget : Polynomial Nat,∀ n (cs : R → Nat),(∀ q,cs q ≤ bound.eval n) → p.ready cs →
      ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨clock,hclock⟩ := hp
  refine ⟨bound+clock,?_⟩
  intro n cs hb hready q
  have run := hr PUnit (fun _ => CounterInstr.halt) PUnit.unit cs [] hready
  have hc := CounterRun.counter_le _ run q
  have ht := hclock n cs hb hready
  have hq := hb q
  simp only [Polynomial.eval_add]
  change p.counters cs q ≤ cs q+p.steps cs at hc
  omega

end ShiReversibleGenerator
