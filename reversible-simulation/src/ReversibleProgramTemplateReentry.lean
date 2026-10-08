import ReversibleTickEmitterTraversalFrames
import ReversibleLoopControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem CounterProgramTemplate.exit_injective (p : CounterProgramTemplate R) (he : p.Embeds) (L : Type) :
    Function.Injective (p.exit (L := L)) := by
  classical
  intro a b hab
  let caller : L → CounterInstr R L := fun l => .emit (decide (l = a)) l
  have h := congrArg (p.code caller a) hab
  rw [he L caller a a, he L caller a b] at h
  have hb := congrArg (fun i : CounterInstr R (p.Labels L) => match i with | .emit v _ => v | _ => false) h
  have hba : b = a := by simpa [caller, CounterInstr.relabel] using hb.symm
  exact hba.symm

noncomputable def programReentryCode (p : CounterProgramTemplate R) (remaining : R) :
    p.Labels (Fin 3) → CounterInstr R (p.Labels (Fin 3)) := by
  classical
  exact reentryCode (p.code (fun (_ : Fin 3) => .halt) 0) remaining (p.exit 0) (p.exit 1) (p.entry 0) (p.exit 2)

theorem programReentryCode_test (p : CounterProgramTemplate R) (remaining : R) :
    programReentryCode p remaining (p.exit 0) = .branch remaining (p.exit 2) (p.exit 1) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem programReentryCode_pop (p : CounterProgramTemplate R) (remaining : R) (he : p.Embeds) :
    programReentryCode p remaining (p.exit 1) = .dec remaining (p.entry 0) := by
  classical
  apply reentryCode_pop
  intro h
  exact (by decide : (1 : Fin 3) ≠ 0) (p.exit_injective he (Fin 3) h)

theorem programReentryCode_body (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (hr : p.Runs) (cs : R → Nat) (ys : List Bool) (hready : p.ready cs) :
    CounterRun (programReentryCode p remaining) ⟨some (p.entry 0), cs, ys⟩ (p.steps cs)
      ⟨some (p.exit 0), p.counters cs, p.bytes cs ++ ys⟩ := by
  classical
  apply reentryCode_preserves_run
    (p.code (fun (_ : Fin 3) => .halt) 0) remaining (p.exit 0) (p.exit 1) (p.entry 0) (p.exit 2)
  · simpa only [CounterInstr.relabel] using he (Fin 3) (fun _ => .halt) 0 0
  · simpa only [CounterInstr.relabel] using he (Fin 3) (fun _ => .halt) 0 1
  · exact hr (Fin 3) (fun _ => .halt) 0 cs ys hready
  · simp

noncomputable def programDescendingBody (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R (p.Labels (Fin 3))) : CounterCfg R (p.Labels (Fin 3)) :=
  let cs := Function.update s.counters remaining k
  ⟨none, p.counters cs, p.bytes cs ++ s.output⟩

noncomputable def programDescendingCost (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R (p.Labels (Fin 3))) : Nat := p.steps (Function.update s.counters remaining k)

theorem programDescendingTraversal_run (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (hr : p.Runs)
    (invariant : Nat → CounterCfg R (p.Labels (Fin 3)) → Prop)
    (hready : ∀ k s, invariant (k + 1) s → p.ready (Function.update s.counters remaining k))
    (hframe : ∀ k s, invariant (k + 1) s → p.counters (Function.update s.counters remaining k) remaining = k)
    (hnext : ∀ k s, invariant (k + 1) s → invariant k (programDescendingBody p remaining k s))
    (k : Nat) (s : CounterCfg R (p.Labels (Fin 3))) (hs : invariant k s) :
    CounterRun (programReentryCode p remaining) (withCounter s remaining k (p.exit 0))
      (descendingSteps (programDescendingBody p remaining) (programDescendingCost p remaining) k s)
      (withCounter (descendingResult (programDescendingBody p remaining) k s) remaining 0 (p.exit 2)) := by
  apply descending_counter_run _ _ _ _ _ _ (programReentryCode_test p remaining)
    (programReentryCode_pop p remaining he) _ _ invariant _ hnext k s hs
  intro j t ht
  have h := programReentryCode_body p remaining he hr
    (Function.update t.counters remaining j) t.output (hready j t ht)
  have hf : Function.update (p.counters (Function.update t.counters remaining j)) remaining j =
      p.counters (Function.update t.counters remaining j) := by
    funext q
    by_cases hq : q = remaining
    · subst q; simpa only [Function.update_self] using (hframe j t ht).symm
    · simp [hq]
  simpa only [withCounter, programDescendingBody, programDescendingCost, hf] using h

end ShiReversibleGenerator
