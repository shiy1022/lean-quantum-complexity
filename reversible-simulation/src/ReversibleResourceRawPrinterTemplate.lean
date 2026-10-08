import ReversibleResourcePrelude
import ReversibleTickResourcePreludeExit
import ReversibleRawPrinterProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The actual finite scalar prelude is also a silent raw-length continuation template for header preparation. -/
theorem resourceRawPrinterTemplate_exists (tm : Turing.FinTM2) (c d : Nat) :
    ∃ p : CounterProgramTemplate WorkspaceRegister,
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=resourceBudgetState (cs 0) 0) ∧
      (∀ cs,p.bytes cs=[]) ∧
      (∀ cs q,p.counters cs q=operationResult (workspaceOperations tm)
        (workspaceInitial tm (cs 0) ((cs 0+c)^d)) q) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨clock,hclock⟩ := resourcePreludeCode_clock_polynomial tm c d
  let code := resourcePreludeCode tm c d (fun _ : Unit => .halt) ()
  let final := fun n => operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d))
  have hr : ∀ n,CounterRun code ⟨some (.inl ()),resourceBudgetState n 0,[]⟩ (clock.eval n)
      ⟨some (tickResourcePreludeExit tm c d),final n,[]⟩ := by
    intro n
    have h := resourcePreludeCode_run tm c d (fun _ : Unit => .halt) () n []
    rw [hclock n] at h
    exact h
  have hhalt : code (tickResourcePreludeExit tm c d)=.halt := by
    dsimp only [code,tickResourcePreludeExit,resourcePreludeCode]
    rw [initializedBudgetCode_embed,operationCode_embed,operationCode_embed]
    rfl
  let p := rawPrinterProgramTemplate code (.inl ()) (tickResourcePreludeExit tm c d) 0
    (fun n => resourceBudgetState n 0) final (fun n => clock.eval n) (fun _ => [])
  have hi : ∀ n q,resourceBudgetState n 0 q ≤ n := by
    intro n q
    simp only [resourceBudgetState]
    split_ifs <;> omega
  refine ⟨p,rawPrinterProgramTemplate_embeds _ _ _ _ _ _ _ _,
    rawPrinterProgramTemplate_run _ _ _ _ _ _ _ _ hhalt hr,?_,?_,?_,?_⟩
  · intro cs; rfl
  · intro cs; rfl
  · intro cs q; rfl
  · intro bound
    exact ⟨rawPrinterProgramTemplate_budget _ _ _ _ _ _ _ _ clock bound (fun _ => le_rfl) hi hr,
      rawPrinterProgramTemplate_polynomial _ _ _ _ _ _ _ _ clock bound (fun _ => le_rfl)⟩

end ShiReversibleGenerator
