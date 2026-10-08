import ReversibleTickResourceForwardWireCertificate

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- One finite graph executes metadata handoff followed by the complete forward history printer. -/
noncomputable def tickHandoffForwardTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (tickMetadataHandoffTemplate tm)
    (tickPreparedForwardHistoryTemplate tm (tickSizeBound tm))

theorem tickHandoffForwardTemplate_embeds (tm : Turing.FinTM2) :
    (tickHandoffForwardTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickPreparedForwardHistoryTemplate_embeds tm (tickSizeBound tm))

theorem tickHandoffForwardTemplate_run (tm : Turing.FinTM2) :
    (tickHandoffForwardTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickMetadataHandoffTemplate_run tm)
    (tickPreparedForwardHistoryTemplate_run tm (tickSizeBound tm))

/-- The actual two counted runs combine without inserting any additional instructions. -/
theorem tickHandoffForwardTemplate_counted_run (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L)
    (stop : L) (ys payload : List Bool)
    (hhand : CounterRun ((tickMetadataHandoffTemplate tm).code caller stop)
      ⟨some ((tickMetadataHandoffTemplate tm).entry stop),cs,ys⟩
      ((tickMetadataHandoffTemplate tm).steps cs)
      ⟨some ((tickMetadataHandoffTemplate tm).exit stop),
        (tickMetadataHandoffTemplate tm).counters cs,ys⟩)
    (hforward : CounterRun ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).code caller stop)
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).entry stop),
        (tickMetadataHandoffTemplate tm).counters cs,ys⟩
      ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).steps
        ((tickMetadataHandoffTemplate tm).counters cs))
      ⟨some ((tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).exit stop),
        (tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)).counters
          ((tickMetadataHandoffTemplate tm).counters cs),payload++ys⟩)
    (hr : cs (.inl 5)=0) :
    CounterRun ((tickHandoffForwardTemplate tm).code caller stop)
      ⟨some ((tickHandoffForwardTemplate tm).entry stop),cs,ys⟩
      ((tickHandoffForwardTemplate tm).steps cs)
      ⟨some ((tickHandoffForwardTemplate tm).exit stop),
        (tickHandoffForwardTemplate tm).counters cs,payload++ys⟩ := by
  let q := tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)
  have h₁ := tickMetadataHandoffTemplate_run tm (q.Labels L) (q.code caller stop) (q.entry stop)
    cs ys ((tickMetadataHandoffTemplate_ready tm cs).2 hr)
  rw [tickMetadataHandoffTemplate_bytes,List.nil_append] at h₁
  have h₂ := CounterRun.relabel (q.code caller stop)
    ((tickMetadataHandoffTemplate tm).code (q.code caller stop) (q.entry stop))
    (tickMetadataHandoffTemplate tm).exit
    (fun l => tickMetadataHandoffTemplate_embeds tm (q.Labels L) (q.code caller stop) (q.entry stop) l)
    hforward
  simpa only [tickHandoffForwardTemplate,sequenceProgramTemplate,q,CounterCfg.relabel,Option.map_some]
    using CounterRun.trans _ h₁ h₂

end ShiReversibleGenerator
