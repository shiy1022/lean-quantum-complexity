import ReversibleGeneratorActions
import ReversibleAssignmentEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem actionCounters_append (a b : List (GeneratorAction R)) (cs : R → Nat) :
    actionCounters (a ++ b) cs = actionCounters b (actionCounters a cs) := by
  induction a generalizing cs with
  | nil => rfl
  | cons x a ih => simp [actionCounters, ih]

theorem actionBytes_append (a b : List (GeneratorAction R)) (cs : R → Nat) :
    actionBytes (a ++ b) cs = actionBytes b (actionCounters a cs) ++ actionBytes a cs := by
  induction a generalizing cs with
  | nil => simp [actionBytes, actionCounters]
  | cons x a ih => simp [actionBytes, actionCounters, ih, List.append_assoc]

theorem emissionActions_counters (atoms : List (EmissionAtom R)) (cs : R → Nat) :
    actionCounters (atoms.map GeneratorAction.emit) cs = cs := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simpa [actionCounters, GeneratorAction.counters] using ih

theorem emissionActions_bytes (atoms : List (EmissionAtom R)) (cs : R → Nat) :
    actionBytes (atoms.map GeneratorAction.emit) cs = emissionBytes atoms cs := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [actionBytes, GeneratorAction.counters, GeneratorAction.bytes, emissionBytes, ih]

/-- Layer count changes by actual finite constant-increment instructions. -/
def countedEmissionActions (atoms : List (EmissionAtom R)) (source count : R) (layers : Nat) :
    List (GeneratorAction R) :=
  atoms.map GeneratorAction.emit ++ [.arithmetic (.affine ⟨source, count, layers, 0⟩)]

theorem countedEmission_counters (atoms : List (EmissionAtom R)) (source count : R)
    (layers : Nat) (cs : R → Nat) :
    actionCounters (countedEmissionActions atoms source count layers) cs =
      Function.update cs count (cs count + layers) := by
  simp [countedEmissionActions, actionCounters_append, emissionActions_counters,
    actionCounters, GeneratorAction.counters, GeneratorOperation.apply, AffineAtom.apply]

theorem countedEmission_bytes (atoms : List (EmissionAtom R)) (source count : R)
    (layers : Nat) (cs : R → Nat) :
    actionBytes (countedEmissionActions atoms source count layers) cs = emissionBytes atoms cs := by
  simp [countedEmissionActions, actionBytes_append, emissionActions_counters, emissionActions_bytes,
    actionBytes, GeneratorAction.bytes, GeneratorAction.counters]

theorem countedEmission_run (atoms : List (EmissionAtom R)) (source count buf tmp : R)
    (layers : Nat) (caller : L → CounterInstr R L) (stop : L)
    (hv : ∀ atom ∈ atoms, atom.Valid buf tmp)
    (hsc : source ≠ count) (hst : source ≠ tmp) (hct : count ≠ tmp) (hcb : count ≠ buf)
    (hbt : buf ≠ tmp) (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    let actions := countedEmissionActions atoms source count layers
    CounterRun (actionCode actions caller buf tmp stop)
      ⟨some (actionEntry actions stop), cs, ys⟩ (actionSteps actions cs)
      ⟨some (actionExit actions stop), Function.update cs count (cs count + layers),
        emissionBytes atoms cs ++ ys⟩ := by
  have ha : ∀ a ∈ countedEmissionActions atoms source count layers, a.Valid buf tmp := by
    intro a h
    simp only [countedEmissionActions, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨atom, hm, rfl⟩ | rfl
    · exact hv atom hm
    · exact ⟨⟨hsc, hst, hct⟩, hcb⟩
  simpa only [countedEmission_counters, countedEmission_bytes] using
    actionCode_run (countedEmissionActions atoms source count layers) caller buf tmp stop ha hbt cs hb ht ys

theorem countedAssignment_layers {m : Nat} (kind : AssignmentEmissionKind)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    kind.layers = (assignmentLayers kind i j k hij hik hjk).length :=
  (assignmentLayers_length kind i j k hij hik hjk).symm

end ShiReversibleGenerator
