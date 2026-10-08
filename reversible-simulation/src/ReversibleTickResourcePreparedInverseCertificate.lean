import ReversibleTickResourceInverseSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The complete inverse history's bytes at the established machine wire count. -/
noncomputable def tickResourceInversePayload (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) : List Bool :=
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
    (time.eval n) wires (Nat.le_refl _) hin hout true
  (gs.map ShiBQP.encLayer).flatten

/-- The finite handoff, initialized pointer setup, and complete inverse printer have exact quantum bytes and a counted polynomial clock. -/
theorem tickResourcePreparedInverse_certificate (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) → 0 < time.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (ys : List Bool),
      let p := tickHandoffInverseTemplate tm
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,tickResourceInversePayload tm time n++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨cp,hp⟩ := tickResourceInverseSetupTemplate_polynomial tm time
  obtain ⟨cq,hq⟩ := tickResourceInverse_full_wire_certificate tm time
  refine ⟨cp+cq,?_⟩
  intro n cs hpull houtside ht L caller stop ys
  dsimp only
  have hsetup := hp n cs hpull houtside
  have hinverse := hq n cs hpull houtside ht L caller stop ys
  have hrun : CounterRun ((tickInverseHistoryTemplate tm (tickSizeBound tm)).code caller stop)
      ⟨some ((tickInverseHistoryTemplate tm (tickSizeBound tm)).entry stop),
        (tickResourceInverseSetupTemplate tm).counters cs,ys⟩
      ((tickInverseHistoryTemplate tm (tickSizeBound tm)).steps ((tickResourceInverseSetupTemplate tm).counters cs))
      ⟨some ((tickInverseHistoryTemplate tm (tickSizeBound tm)).exit stop),
        (tickInverseHistoryTemplate tm (tickSizeBound tm)).counters ((tickResourceInverseSetupTemplate tm).counters cs),
        tickResourceInversePayload tm time n++ys⟩ := by
    simpa only [(tickResourceInverseSetupTemplate_result tm cs).2,tickResourceInversePayload] using hinverse.1
  have hwhole := sequenceProgramTemplate_counted_payload_run (tickResourceInverseSetupTemplate tm)
    (tickInverseHistoryTemplate tm (tickSizeBound tm)) (tickResourceInverseSetupTemplate_embeds tm)
    (tickResourceInverseSetupTemplate_run tm) cs hsetup.1 (tickResourceInverseSetupTemplate_result tm cs).1
    L caller stop ys (tickResourceInversePayload tm time n) hrun
  refine ⟨?_,?_,?_⟩
  · simpa only [tickHandoffInverseTemplate,tickPreparedInverseHistoryTemplate,tickResourceInverseSetupTemplate,
      sequenceProgramTemplate,Nat.add_assoc] using hwhole
  · simpa only [tickHandoffInverseTemplate,tickPreparedInverseHistoryTemplate,tickResourceInverseSetupTemplate,
      tickResourceInverseStart,sequenceProgramTemplate,Polynomial.eval_add,Nat.add_assoc] using
      Nat.add_le_add hsetup.2 hinverse.2.1
  · simpa only [tickHandoffInverseTemplate,tickPreparedInverseHistoryTemplate,tickResourceInverseStart,
      sequenceProgramTemplate] using hinverse.2.2.2

end ShiReversibleGenerator
