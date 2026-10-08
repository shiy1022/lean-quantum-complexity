import ReversibleRawElementaryLayers

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversible ShiReversibleGateBridge

theorem substitute_length_sum {n : Nat} (gs : List (Gate n)) :
    (substitute gs).length = (gs.map (fun g => (gateCircuit g).length)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change (gateCircuit g ++ substitute gs).length = _
    rw [List.length_append, ih]
    rfl

theorem substitute_reverse_length {n : Nat} (gs : List (Gate n)) :
    (substitute gs.reverse).length = (substitute gs).length := by
  rw [substitute_length_sum, substitute_length_sum, List.map_reverse, List.sum_reverse]

/-- The raw-node count is exactly the length of the established gate-set substitution. -/
theorem rawAssignment_substitute_length {n : Nat} (a : RawAssignment)
    (ht : a.target < n) (hp : a.Topological) (hd : a.DistinctControls) :
    (substitute (a.toAssignment ht hp).compile).length = rawAssignmentLayerCount a := by
  cases a with
  | constant t b =>
    cases b <;> simp [RawAssignment.toAssignment, Assignment.compile, substitute, gateCircuit,
      rawAssignmentLayerCount]
  | copy s t | neg s t =>
    simp [RawAssignment.toAssignment, Assignment.compile, substitute, gateCircuit, rawAssignmentLayerCount]
  | conj a b t =>
    have hab : (⟨a, hp.1.trans ht⟩ : Fin n) ≠ ⟨b, hp.2.trans ht⟩ := by
      intro h
      exact hd (congrArg Fin.val h)
    have hat : (⟨a, hp.1.trans ht⟩ : Fin n) ≠ ⟨t, ht⟩ := by
      intro h
      exact hp.1.ne (congrArg Fin.val h)
    have hbt : (⟨b, hp.2.trans ht⟩ : Fin n) ≠ ⟨t, ht⟩ := by
      intro h
      exact hp.2.ne (congrArg Fin.val h)
    have h := toffoliCircuit_depth (⟨a, hp.1.trans ht⟩ : Fin n) ⟨b, hp.2.trans ht⟩ ⟨t, ht⟩ hab hat hbt
    simpa [RawAssignment.toAssignment, Assignment.compile, substitute, gateCircuit, hab,
      rawAssignmentLayerCount, ShiShallow.depth] using h

theorem rawProgram_substitute_length {n : Nat} (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological)
    (hd : ∀ a ∈ nodes, a.DistinctControls) :
    (substitute (compileAssignments (boundProgram n nodes ht hp))).length =
      (nodes.map rawAssignmentLayerCount).sum := by
  induction nodes with
  | nil => rfl
  | cons a nodes ih =>
    have ha : a ∈ a :: nodes := by simp
    have ht' : ∀ b ∈ nodes, b.target < n := fun b hb => ht b (by simp [hb])
    have hp' : ∀ b ∈ nodes, b.Topological := fun b hb => hp b (by simp [hb])
    have hd' : ∀ b ∈ nodes, b.DistinctControls := fun b hb => hd b (by simp [hb])
    rw [boundProgram_cons]
    change (substitute ((a.toAssignment (ht a ha) (hp a ha)).compile ++
      compileAssignments (boundProgram n nodes ht' hp'))).length = _
    rw [show substitute ((a.toAssignment (ht a ha) (hp a ha)).compile ++
        compileAssignments (boundProgram n nodes ht' hp')) =
        substitute (a.toAssignment (ht a ha) (hp a ha)).compile ++
          substitute (compileAssignments (boundProgram n nodes ht' hp')) by
      simp only [substitute, List.flatMap_append]]
    rw [List.length_append, rawAssignment_substitute_length a (ht a ha) (hp a ha) (hd a ha), ih ht' hp' hd']
    rfl

theorem rawProgram_substitute_length_both {n : Nat} (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological)
    (hd : ∀ a ∈ nodes, a.DistinctControls) (backward : Bool) :
    (substitute (if backward then (compileAssignments (boundProgram n nodes ht hp)).reverse
      else compileAssignments (boundProgram n nodes ht hp))).length =
        (nodes.map rawAssignmentLayerCount).sum := by
  cases backward <;> simp only [Bool.false_eq_true, if_false, if_true,
    substitute_reverse_length, rawProgram_substitute_length nodes ht hp hd]

end ShiReversibleGenerator
