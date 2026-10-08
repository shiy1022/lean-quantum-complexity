import ReversibleTickResourcePreparedInverseCertificate
import ReversibleTickResourcePreludeExit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickResourceInverseCode (tm : Turing.FinTM2) (c d : Nat) := by
  classical
  exact chainedCounterCode (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
    ((tickHandoffInverseTemplate tm).code (fun _ : Unit => .halt) ())
    (tickResourcePreludeExit tm c d) ((tickHandoffInverseTemplate tm).entry ()) (.inl 0)

/-- The entire resource setup, metadata handoff, and inverse history printer is one finite control graph. -/
theorem tickResourceInverseCode_finite (tm : Turing.FinTM2) (c d : Nat) :
    Nonempty (Fintype (ResourcePreludeLabels tm c d Unit ⊕ (tickHandoffInverseTemplate tm).Labels Unit)) := by
  classical
  letI := (tickHandoffInverseTemplate tm).finite Unit inferInstance
  exact ⟨inferInstance⟩

/-- Count the real resource prefix, the connecting branch, and the complete printer run. -/
theorem tickResourceInverseCode_joined_run (tm : Turing.FinTM2) (c d n : Nat) (ys payload : List Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (first : Nat)
    (hfirst : CounterRun (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ⟨some (.inl ()),tickResourceInitial tm n,ys⟩ first
      ⟨some (tickResourcePreludeExit tm c d),cs,ys⟩)
    (hsecond : CounterRun ((tickHandoffInverseTemplate tm).code (fun _ : Unit => .halt) ())
      ⟨some ((tickHandoffInverseTemplate tm).entry ()),cs,ys⟩
      ((tickHandoffInverseTemplate tm).steps cs)
      ⟨some ((tickHandoffInverseTemplate tm).exit ()),
        (tickHandoffInverseTemplate tm).counters cs,payload++ys⟩) :
    CounterRun (tickResourceInverseCode tm c d)
      ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩
      (first+1+(tickHandoffInverseTemplate tm).steps cs)
      ⟨some (.inr ((tickHandoffInverseTemplate tm).exit ())),
        (tickHandoffInverseTemplate tm).counters cs,payload++ys⟩ := by
  classical
  simpa only [tickResourceInverseCode,CounterCfg.relabel,Option.map_some] using
    chainedCounterCode_run (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ((tickHandoffInverseTemplate tm).code (fun _ : Unit => .halt) ())
      (tickResourcePreludeExit tm c d) ((tickHandoffInverseTemplate tm).entry ()) (.inl 0)
      (tickResourcePreludeExit_halt tm c d) _ cs ys _ first _ hfirst hsecond

/-- The complete inverse history generator starts from raw length alone and has an actual polynomial clock. -/
theorem tickResourceInverseCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool), 0 < (n+c)^d →
      ∃ (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (count : Nat),
        CounterRun (tickResourceInverseCode tm c d)
          ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩ count
          ⟨some (.inr ((tickHandoffInverseTemplate tm).exit ())),
            (tickHandoffInverseTemplate tm).counters cs,
            tickResourceInversePayload tm ((Polynomial.X+Polynomial.C c)^d) n++ys⟩ ∧
        count ≤ clock.eval n ∧
        (tickHandoffInverseTemplate tm).counters cs (tickTraversalSpare tm 3)=0 := by
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := tickResourcePreludeCode_polynomial tm c d
  obtain ⟨cq,hq⟩ := tickResourcePreparedInverse_certificate tm time
  refine ⟨cp+Polynomial.C 1+cq,?_⟩
  intro n ys ht
  obtain ⟨final,hfirst,hpull,houtside⟩ := hp Unit (fun _ => .halt) () n ys
  have he : final=⟨some (tickResourcePreludeExit tm c d),final.counters,ys⟩ :=
    tickResourcePrelude_endpoint tm c d final n ys hpull
  have hm : ∀ r,final.counters (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r := by
    intro r
    simpa only [CounterCfg.pullRegisters,time,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C] using congrArg (fun s => s.counters r) hpull
  have ht' : 0 < time.eval n := by simpa [time] using ht
  have hsecond := hq n final.counters hm houtside ht' Unit (fun _ => .halt) () ys
  rw [he] at hfirst
  refine ⟨final.counters,cp.eval n+1+(tickHandoffInverseTemplate tm).steps final.counters,?_,?_,hsecond.2.2⟩
  · exact tickResourceInverseCode_joined_run tm c d n ys _ final.counters (cp.eval n) hfirst hsecond.1
  · simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_left hsecond.2.1 (cp.eval n+1)

/-- Positive padding yields this run at every input length. -/
theorem tickResourceInverseCode_positive_padding (tm : Turing.FinTM2) (c d : Nat) (hc : 0 < c) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool),
      ∃ (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (count : Nat),
        CounterRun (tickResourceInverseCode tm c d)
          ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩ count
          ⟨some (.inr ((tickHandoffInverseTemplate tm).exit ())),
            (tickHandoffInverseTemplate tm).counters cs,
            tickResourceInversePayload tm ((Polynomial.X+Polynomial.C c)^d) n++ys⟩ ∧
        count ≤ clock.eval n ∧
        (tickHandoffInverseTemplate tm).counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickResourceInverseCode_polynomial_run tm c d
  refine ⟨clock,?_⟩
  intro n ys
  exact hclock n ys (Nat.pow_pos (by omega))

end ShiReversibleGenerator
