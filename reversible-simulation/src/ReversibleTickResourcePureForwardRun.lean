import ReversibleTickResourcePureState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The fixed raw-length history program retains its exact original layer count as well as its polynomial real clock. -/
theorem tickResourcePureForwardCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat,∀ n,0 < (n+c)^d →
      let cs := tickResourceState tm n ((n+c)^d)
      let p := tickHandoffForwardTemplate tm
      ∃ count,CounterRun (tickResourceForwardCode tm c d)
        ⟨some (.inl (.inl ())),tickResourceInitial tm n,[]⟩ count
        ⟨some (.inr (p.exit ())),p.counters cs,
          tickResourceForwardPayload tm ((Polynomial.X+Polynomial.C c)^d) n⟩ ∧
        count ≤ clock.eval n ∧ p.counters cs (.inl 9)=
          (n+c)^d*tickForestLayerCount tm (n+(n+c)^d*machinePushBound tm+1) := by
  classical
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := tickResourcePreludeCode_pure_run tm c d
  obtain ⟨ch,hh⟩ := tickResourceHandoff_polynomial_run tm time
  obtain ⟨cf,hf⟩ := tickResourceForward_full_wire_certificate tm time
  refine ⟨cp+Polynomial.C 1+ch+cf,?_⟩
  intro n ht
  dsimp only
  let cs := tickResourceState tm n ((n+c)^d)
  have hm : ∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r := by
    intro r
    simpa only [cs,time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
      using tickResourceState_pull tm n ((n+c)^d) r
  have ho := tickResourceState_outside tm n ((n+c)^d)
  have ht' : 0 < time.eval n := by simpa only [time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using ht
  have hand := hh n cs hm ho Unit (fun _ => .halt) () []
  have forward := hf n cs hm ho ht' Unit (fun _ => .halt) () []
  have hforward : CounterRun ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).code (fun _ : Unit => .halt) ())
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).entry ()),
        (tickMetadataHandoffTemplate tm).counters cs,[]⟩
      ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).steps ((tickMetadataHandoffTemplate tm).counters cs))
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).exit ()),
        (tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).counters ((tickMetadataHandoffTemplate tm).counters cs),
        tickResourceForwardPayload tm time n++[]⟩ := by
    simpa only [tickResourceForwardPayload] using forward.1
  have hs := (tickResourcePrelude_metadata tm n (time.eval n) cs hm).2.2.2.2.1
  have hsecond := tickHandoffForwardTemplate_counted_run tm cs Unit (fun _ => .halt) () []
    (tickResourceForwardPayload tm time n) hand.1 hforward hs
  have hrun := tickResourceForwardCode_joined_run tm c d n [] _ cs (cp.eval n) (hp n []) hsecond
  refine ⟨cp.eval n+1+(tickHandoffForwardTemplate tm).steps cs,?_,?_,?_⟩
  · simpa only [List.append_nil] using hrun
  · have hb : (tickHandoffForwardTemplate tm).steps cs ≤ ch.eval n+cf.eval n := Nat.add_le_add hand.2 forward.2.1
    simpa only [Polynomial.eval_add,Polynomial.eval_C,Nat.add_assoc] using Nat.add_le_add_left hb (cp.eval n+1)
  · have hc : 0 < (tickRuntimeCapacityPolynomial tm time).eval n := by
      rw [tickRuntimeCapacityPolynomial_eval]
      omega
    have hcount := forward.2.2.1
    rw [tickStridedHistoryQuantumLayers_length tm (hc := hc)] at hcount
    simpa only [tickHandoffForwardTemplate,sequenceProgramTemplate,tickRuntimeCapacityPolynomial_eval,
      time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using hcount

end ShiReversibleGenerator
