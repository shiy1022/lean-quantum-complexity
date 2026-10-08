import ReversibleRawPayloadBridge

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversible ShiReversibleGateBridge

theorem substitute_append_payload {n : Nat} (gs hs : List (Gate n)) :
    ((substitute (gs ++ hs)).map ShiBQP.encLayer).flatten =
      ((substitute gs).map ShiBQP.encLayer).flatten ++
      ((substitute hs).map ShiBQP.encLayer).flatten := by
  simp [substitute, List.flatMap_append]

/-- Both natural-address payload orders equal the established compiler's circuit bytes. -/
theorem rawProgramPayload_substitute (n : Nat) (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological)
    (hd : ∀ a ∈ nodes, a.DistinctControls) (backward : Bool) :
    (((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten) =
      ((substitute (if backward then (compileAssignments (boundProgram n nodes ht hp)).reverse
        else compileAssignments (boundProgram n nodes ht hp))).map ShiBQP.encLayer).flatten := by
  induction nodes with
  | nil => cases backward <;> rfl
  | cons a nodes ih =>
      have ha : a ∈ a :: nodes := by simp
      have ht' : ∀ b ∈ nodes, b.target < n := fun b hb => ht b (by simp [hb])
      have hp' : ∀ b ∈ nodes, b.Topological := fun b hb => hp b (by simp [hb])
      have hd' : ∀ b ∈ nodes, b.DistinctControls := fun b hb => hd b (by simp [hb])
      have h := rawAssignmentPayload_substitute backward a (ht a ha) (hp a ha) (hd a ha)
      have htail := ih ht' hp' hd'
      cases backward <;>
        simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true, List.reverse_cons,
          List.map_cons, List.flatten_cons, List.map_append, List.flatten_append,
          List.map_singleton, List.flatten_singleton, boundProgram_cons,
          compileAssignments, List.flatMap_cons, List.reverse_append] at h htail ⊢
      all_goals rw [substitute_append_payload, ← h, ← htail]
      all_goals simp

theorem formulaPrinterPayload_substitute {R ι : Type} [DecidableEq R] (backward : Bool)
    (p : Formula ι) (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (cs : R → Nat)
    (n : Nat) (hin : ∀ i, (inputs i).eval cs < cs base + offset)
    (hsize : cs base + offset + p.size ≤ n) :
    let nodes := p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset)
    let ht : ∀ a ∈ nodes, a.target < n := fun a ha =>
      (p.rawCompile_target_interval _ _ a ha).2.trans_le hsize
    let hp : ∀ a ∈ nodes, a.Topological := p.rawCompile_topological _ _ hin
    formulaPrinterPayload backward p inputs base offset cs =
      ((substitute (if backward then (compileAssignments (boundProgram n nodes ht hp)).reverse
        else compileAssignments (boundProgram n nodes ht hp))).map ShiBQP.encLayer).flatten := by
  apply rawProgramPayload_substitute
  exact rawCompile_distinct_controls p _ _

end ShiReversibleGenerator
