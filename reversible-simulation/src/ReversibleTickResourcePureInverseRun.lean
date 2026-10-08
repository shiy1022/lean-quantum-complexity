import ReversibleTickResourcePureState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual inverse history program starts from raw length and returns its exact original layer count. -/
theorem tickResourcePureInverseCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat,∀ n,0 < (n+c)^d →
      let cs := tickResourceState tm n ((n+c)^d)
      let p := tickHandoffInverseTemplate tm
      ∃ count,CounterRun (tickResourceInverseCode tm c d)
        ⟨some (.inl (.inl ())),tickResourceInitial tm n,[]⟩ count
        ⟨some (.inr (p.exit ())),p.counters cs,
          tickResourceInversePayload tm ((Polynomial.X+Polynomial.C c)^d) n⟩ ∧
        count ≤ clock.eval n ∧ p.counters cs (.inl 9)=
          (n+c)^d*tickForestLayerCount tm (n+(n+c)^d*machinePushBound tm+1) := by
  classical
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := tickResourcePreludeCode_pure_run tm c d
  obtain ⟨cq,hq⟩ := tickResourcePreparedInverse_certificate tm time
  obtain ⟨cw,hw⟩ := tickResourceInverse_full_wire_certificate tm time
  refine ⟨cp+Polynomial.C 1+cq,?_⟩
  intro n ht
  dsimp only
  let cs := tickResourceState tm n ((n+c)^d)
  have hm : ∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r := by
    intro r
    simpa only [cs,time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
      using tickResourceState_pull tm n ((n+c)^d) r
  have ho := tickResourceState_outside tm n ((n+c)^d)
  have ht' : 0 < time.eval n := by simpa only [time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using ht
  have inverse := hq n cs hm ho ht' Unit (fun _ => .halt) () []
  have wire := hw n cs hm ho ht' Unit (fun _ => .halt) () []
  have hrun := tickResourceInverseCode_joined_run tm c d n [] _ cs (cp.eval n) (hp n []) inverse.1
  refine ⟨cp.eval n+1+(tickHandoffInverseTemplate tm).steps cs,?_,?_,?_⟩
  · simpa only [List.append_nil] using hrun
  · simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_left inverse.2.1 (cp.eval n+1)
  · have hc : 0 < (tickRuntimeCapacityPolynomial tm time).eval n := by
      rw [tickRuntimeCapacityPolynomial_eval]
      omega
    have hcount := wire.2.2.1
    rw [tickStridedHistoryQuantumLayers_length tm (hc := hc)] at hcount
    simpa only [tickHandoffInverseTemplate,tickPreparedInverseHistoryTemplate,tickResourceInverseStart,
      sequenceProgramTemplate,tickRuntimeCapacityPolynomial_eval,time,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using hcount

end ShiReversibleGenerator
