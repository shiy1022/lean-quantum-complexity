import ReversibleTickResourceForwardProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The complete forward history's bytes at the established machine wire count. -/
noncomputable def tickResourceForwardPayload (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) : List Bool :=
  let cap := (tickRuntimeCapacityPolynomial tm time).eval n
  let firstOutput := n+18*configurationWidth tm cap
  let wires := n+paddedMachineWorkspace tm n (time.eval n)+(2*cap+1)
  let hin : ∀ i : Fin (configurationWidth tm cap),n+17+18*i.val < firstOutput := by
    intro i
    have hi := i.isLt
    omega
  let hout : firstOutput+time.eval n*(configurationWidth tm cap*(tickSizeBound tm+1)) ≤ wires := by
    have h := tickPreparedEnd_le_workspace tm n (time.eval n)
    rw [←tickRuntimeCapacityPolynomial_eval tm time n] at h
    exact h.trans (Nat.le_add_right _ _)
  let gs := tickStridedHistoryQuantumLayers tm cap (n+17) 18 firstOutput (tickSizeBound tm)
    (time.eval n) wires (Nat.le_refl _) hin hout false
  (gs.map ShiBQP.encLayer).flatten

/-- Starting with raw length alone, the single finite program prints the exact quantum history in polynomial time. -/
theorem tickResourceForwardCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool), 0 < (n+c)^d →
      ∃ (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (count : Nat),
        CounterRun (tickResourceForwardCode tm c d)
          ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩ count
          ⟨some (.inr ((tickHandoffForwardTemplate tm).exit ())),
            (tickHandoffForwardTemplate tm).counters cs,
            tickResourceForwardPayload tm ((Polynomial.X+Polynomial.C c)^d) n++ys⟩ ∧
        count ≤ clock.eval n ∧
        (tickHandoffForwardTemplate tm).counters cs (tickTraversalSpare tm 3)=0 := by
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := tickResourcePreludeCode_polynomial tm c d
  obtain ⟨ch,hh⟩ := tickResourceHandoff_polynomial_run tm time
  obtain ⟨cf,hf⟩ := tickResourceForward_full_wire_certificate tm time
  refine ⟨cp+Polynomial.C 1+ch+cf,?_⟩
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
  have hand := hh n final.counters hm houtside Unit (fun _ => .halt) () ys
  have forward := hf n final.counters hm houtside ht' Unit (fun _ => .halt) () ys
  have hforward : CounterRun ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).code (fun _ : Unit => .halt) ())
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).entry ()),
        (tickMetadataHandoffTemplate tm).counters final.counters,ys⟩
      ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).steps
        ((tickMetadataHandoffTemplate tm).counters final.counters))
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).exit ()),
        (tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).counters
          ((tickMetadataHandoffTemplate tm).counters final.counters),
        tickResourceForwardPayload tm time n++ys⟩ := by
    simpa only [tickResourceForwardPayload] using forward.1
  have hs := (tickResourcePrelude_metadata tm n (time.eval n) final.counters hm).2.2.2.2.1
  have hsecond := tickHandoffForwardTemplate_counted_run tm final.counters Unit (fun _ => .halt) ()
    ys (tickResourceForwardPayload tm time n) hand.1 hforward hs
  rw [he] at hfirst
  refine ⟨final.counters,cp.eval n+1+(tickHandoffForwardTemplate tm).steps final.counters,?_,?_,?_⟩
  · exact tickResourceForwardCode_joined_run tm c d n ys _ final.counters (cp.eval n) hfirst hsecond
  · have hb : (tickHandoffForwardTemplate tm).steps final.counters ≤ ch.eval n+cf.eval n :=
      Nat.add_le_add hand.2 forward.2.1
    simpa only [Polynomial.eval_add,Polynomial.eval_C,Nat.add_assoc] using Nat.add_le_add_left hb (cp.eval n+1)
  · exact forward.2.2.2

/-- A positive padding constant makes the runtime budget positive at every input length. -/
theorem tickResourceForwardCode_positive_padding (tm : Turing.FinTM2) (c d : Nat) (hc : 0 < c) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool),
      ∃ (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (count : Nat),
        CounterRun (tickResourceForwardCode tm c d)
          ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩ count
          ⟨some (.inr ((tickHandoffForwardTemplate tm).exit ())),
            (tickHandoffForwardTemplate tm).counters cs,
            tickResourceForwardPayload tm ((Polynomial.X+Polynomial.C c)^d) n++ys⟩ ∧
        count ≤ clock.eval n ∧
        (tickHandoffForwardTemplate tm).counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickResourceForwardCode_polynomial_run tm c d
  refine ⟨clock,?_⟩
  intro n ys
  exact hclock n ys (Nat.pow_pos (by omega))

end ShiReversibleGenerator
