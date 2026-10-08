import ReversibleToffoliEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

inductive AssignmentEmissionKind where
  | zero | one | copy | negateForward | negateBackward | conjunction
  deriving DecidableEq

instance : Fintype AssignmentEmissionKind :=
  ⟨{.zero, .one, .copy, .negateForward, .negateBackward, .conjunction}, by
    intro x; cases x <;> simp⟩

def xAtoms (r : R) : List (EmissionAtom R) :=
  [.natural r, .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 3)]

def cxAtoms (p r : R) : List (EmissionAtom R) :=
  [.natural r, .natural p, .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4)]

def assignmentAtoms (kind : AssignmentEmissionKind) (p q r : R) : List (EmissionAtom R) :=
  match kind with
  | .zero => []
  | .one => xAtoms r
  | .copy => cxAtoms p r
  | .negateForward => xAtoms r ++ cxAtoms p r
  | .negateBackward => cxAtoms p r ++ xAtoms r
  | .conjunction => toffoliEmissionAtoms p q r

noncomputable def assignmentLayers {m : Nat} (kind : AssignmentEmissionKind) (i j k : Fin m)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ShiShallow.Layered m :=
  match kind with
  | .zero => []
  | .one => [[.x k]]
  | .copy => [[.cnot i k hik]]
  | .negateForward => [[.cnot i k hik], [.x k]]
  | .negateBackward => [[.x k], [.cnot i k hik]]
  | .conjunction => ShiReversibleGateBridge.toffoliCircuit i j k hij hik hjk

def AssignmentEmissionKind.layers : AssignmentEmissionKind → Nat
  | .zero => 0
  | .one | .copy => 1
  | .negateForward | .negateBackward => 2
  | .conjunction => 37

theorem emissionBytes_append (a b : List (EmissionAtom R)) (cs : R → Nat) :
    emissionBytes (a ++ b) cs = emissionBytes b cs ++ emissionBytes a cs := by
  induction a with
  | nil => simp [emissionBytes]
  | cons x a ih => simp [emissionBytes, ih, List.append_assoc]

/-- Both computation directions use exact established elementary-layer payloads. -/
theorem assignmentAtoms_bytes {m : Nat} (kind : AssignmentEmissionKind) (p q r : R)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (cs : R → Nat) (hi : cs p = i.val) (hj : cs q = j.val) (hk : cs r = k.val) :
    emissionBytes (assignmentAtoms kind p q r) cs =
      ((assignmentLayers kind i j k hij hik hjk).map ShiBQP.encLayer).flatten := by
  cases kind with
  | conjunction => exact toffoliEmissionAtoms_bytes p q r i j k hij hik hjk cs hi hj hk
  | zero | one | copy | negateForward | negateBackward =>
      simp [assignmentAtoms, assignmentLayers, xAtoms, cxAtoms, emissionBytes_append,
        emissionBytes, EmissionAtom.bytes, ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encInstr,
        hi, hk, List.append_assoc]

theorem assignmentLayers_length {m : Nat} (kind : AssignmentEmissionKind)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (assignmentLayers kind i j k hij hik hjk).length = kind.layers := by
  cases kind <;> simp [assignmentLayers, AssignmentEmissionKind.layers,
    ← toffoliEmissionLayers_eq, toffoliEmissionLayers]

theorem assignmentAtoms_valid (kind : AssignmentEmissionKind) (p q r buf tmp : R)
    (hp : p ≠ buf ∧ p ≠ tmp) (hq : q ≠ buf ∧ q ≠ tmp) (hr : r ≠ buf ∧ r ≠ tmp) :
    ∀ a ∈ assignmentAtoms kind p q r, a.Valid buf tmp := by
  cases kind <;> simp [assignmentAtoms, xAtoms, cxAtoms, toffoliEmissionAtoms,
    EmissionAtom.Valid, hp, hq, hr]

theorem assignmentEmission_run {m : Nat} (kind : AssignmentEmissionKind) (p q r : R)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (caller : L → CounterInstr R L) (buf tmp : R) (stop : L)
    (hp : p ≠ buf ∧ p ≠ tmp) (hq : q ≠ buf ∧ q ≠ tmp) (hr : r ≠ buf ∧ r ≠ tmp)
    (hbt : buf ≠ tmp) (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0)
    (hi : cs p = i.val) (hj : cs q = j.val) (hk : cs r = k.val) (ys : List Bool) :
    CounterRun (emissionCode (assignmentAtoms kind p q r) caller buf tmp stop)
      ⟨some (emissionEntry (assignmentAtoms kind p q r) stop), cs, ys⟩
      (emissionSteps (assignmentAtoms kind p q r) cs)
      ⟨some (emissionExit (assignmentAtoms kind p q r) stop), cs,
        ((assignmentLayers kind i j k hij hik hjk).map ShiBQP.encLayer).flatten ++ ys⟩ := by
  simpa only [assignmentAtoms_bytes kind p q r i j k hij hik hjk cs hi hj hk] using
    emissionCode_run (assignmentAtoms kind p q r) caller buf tmp stop
      (assignmentAtoms_valid kind p q r buf tmp hp hq hr) hbt cs hb ht ys

theorem assignmentEmission_clock (kind : AssignmentEmissionKind) (p q r : R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    emissionSteps (assignmentAtoms kind p q r) (fun v => (sizes v).eval n) =
      (emissionClock (assignmentAtoms kind p q r) sizes).eval n :=
  (emissionClock_eval _ _ n).symm

end ShiReversibleGenerator
