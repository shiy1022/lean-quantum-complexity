import ReversibleFormulaLayerCount
import ReversibleRawBridge
import ReversibleGateSubstitution

set_option autoImplicit false
namespace ShiReversibleFormula
def RawAssignment.DistinctControls : RawAssignment → Prop
  | .conj a b _ => a ≠ b
  | _ => True
end ShiReversibleFormula

namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversible ShiReversibleGateBridge

theorem rawCompile_distinct_controls {ι : Type} (p : Formula ι) (inputs : ι → Nat) (base : Nat) :
    ∀ a ∈ p.rawCompile inputs base, a.DistinctControls := by
  induction p generalizing base with
  | constant b => simp [Formula.rawCompile, RawAssignment.DistinctControls]
  | input i => simp [Formula.rawCompile, RawAssignment.DistinctControls]
  | neg p ih =>
      intro a ha
      simp only [Formula.rawCompile, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact ih base a ha
      · trivial
  | conj p q ihp ihq =>
      intro a ha
      simp only [Formula.rawCompile, List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · exact ihp base a ha
      · exact ihq (base + p.size) a ha
      · have hp := p.size_pos
        have hq := q.size_pos
        simp only [RawAssignment.DistinctControls, Formula.result]
        omega

/-- Serialized natural addresses agree with the actual bounded gate compiler. -/
theorem rawAssignmentPayload_substitute {n : Nat} (backward : Bool) (a : RawAssignment)
    (ht : a.target < n) (hp : a.Topological) (hd : a.DistinctControls) :
    rawAssignmentPayload backward a =
      ((substitute (if backward then (a.toAssignment ht hp).compile.reverse
        else (a.toAssignment ht hp).compile)).map ShiBQP.encLayer).flatten := by
  cases a with
  | constant t b =>
      cases b <;> cases backward <;>
        simp [rawAssignmentPayload, RawAssignment.toAssignment, Assignment.compile,
          substitute, gateCircuit, assignmentPayload, assignmentAtoms, xAtoms,
          emissionBytes, EmissionAtom.bytes, payloadRegisters, ShiBQP.encLayer,
          ShiBQP.encStr, ShiBQP.encInstr]
  | copy s t | neg s t =>
      cases backward <;>
        simp [rawAssignmentPayload, RawAssignment.toAssignment, Assignment.compile,
          substitute, gateCircuit, assignmentPayload, assignmentAtoms, xAtoms, cxAtoms,
          emissionBytes, EmissionAtom.bytes, payloadRegisters, ShiBQP.encLayer,
          ShiBQP.encStr, ShiBQP.encInstr, List.append_assoc]
  | conj a b t =>
      have hab : (⟨a, hp.1.trans ht⟩ : Fin n) ≠ ⟨b, hp.2.trans ht⟩ := by
        intro h; exact hd (congrArg Fin.val h)
      have hat : (⟨a, hp.1.trans ht⟩ : Fin n) ≠ ⟨t, ht⟩ := by
        intro h; exact hp.1.ne (congrArg Fin.val h)
      have hbt : (⟨b, hp.2.trans ht⟩ : Fin n) ≠ ⟨t, ht⟩ := by
        intro h; exact hp.2.ne (congrArg Fin.val h)
      have h := assignmentPayload_encoding .conjunction
        (⟨a, hp.1.trans ht⟩ : Fin n) ⟨b, hp.2.trans ht⟩ ⟨t, ht⟩ hab hat hbt
      cases backward <;> simpa [rawAssignmentPayload, RawAssignment.toAssignment,
        Assignment.compile, substitute, gateCircuit, hab, assignmentLayers] using h

end ShiReversibleGenerator
