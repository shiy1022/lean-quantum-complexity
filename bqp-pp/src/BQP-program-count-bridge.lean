import «BQP-program-evaluation»
import «BQP-program-count»
import «BQP-canonical-amplitude»

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BQPProgram
open ShiShallow BQPPaths BQPGates

 theorem phaseDifference_val_sub (a b : ZMod 8) :
    phaseDifference a.val b.val = (a - b).val := by
  fin_cases a <;> fin_cases b <;> decide

 theorem phaseDifference_eq_iff (a b d : ZMod 8) :
    phaseDifference a.val b.val = d.val ↔ a - b = d := by
  rw [phaseDifference_val_sub]
  exact (ZMod.val_injective 8).eq_iff

/-- The same implemented single-run checker counts the canonical common-endpoint
pairs. All reversal, phase, and program-evaluation premises are proved. -/
theorem compiled_pair_counts (C : Checker) {n m : ℕ} (gs : List (Instr (n + m)))
    (x : Bits n) (out : Fin (n + m)) (d : ZMod 8) :
    let z := Fin.append x (fun _ : Fin m => false)
    endpointCount
      (fun w : Fin (hadamardCount gs) → Bool => forwardRun gs z (List.ofFn w))
      (fun w : Fin (hadamardCount gs) → Bool => (phaseRun gs z (List.ofFn w)).val)
      (fun y => y out) d.val =
      ShiClassPP.countAccept (C.relation d) (C.encode (compile gs x out))
        (hadamardCount gs + hadamardCount gs) := by
  classical
  let z := Fin.append x (fun _ : Fin m => false)
  have h := BQPChecked.reference9.1 (Bits (n+m)) (ZMod 8) (hadamardCount gs)
    (forwardRun gs z) (backwardWitness gs z) (phaseRun gs z) (fun y => y out)
    (fun y v => decide (forwardRun gs.reverse y v = z))
    (fun y v => adjointPhaseRun gs.reverse y v)
    (fun y v => (backwardWitness gs.reverse y v).reverse)
    ZMod.val (C.eval (compile gs x out)) d
    (ZMod.val_injective 8)
    (fun w => backwardWitness_length gs z w)
    (by
      intro w hw
      exact decide_eq_true ((canonical_reversal.2.2.2 (n+m) gs z w hw).1))
    (fun w hw => canonical_adjoint_phase gs z w hw)
    (by
      intro u v hu hv hF hB
      apply List.reverse_injective
      calc
        u.reverse = backwardWitness gs.reverse (forwardRun gs z u)
            (backwardWitness gs z u).reverse := (canonical_reversal.2.2.2 (n+m) gs z u hu).2.symm
        _ = backwardWitness gs.reverse (forwardRun gs z v)
            (backwardWitness gs z v).reverse := by rw [hF, hB]
        _ = v.reverse := (canonical_reversal.2.2.2 (n+m) gs z v hv).2)
    (by intro y v; simp [backwardWitness_length, hadamardCount])
    (by
      intro y v hv had
      have he : forwardRun gs.reverse y v = z := of_decide_eq_true had
      have hr := canonical_reversal.2.2.2 (n+m) gs.reverse y v
        (by simpa [hadamardCount] using hv)
      simpa only [List.reverse_reverse, he] using hr)
    (by
      intro u v hu hv
      simpa only [decide_eq_true_eq] using eval_compile_split C gs x out u v hu hv)
  simpa only [endpointCount, phaseDifference_eq_iff, ShiClassPP.countAccept,
    C.relation_eval, decide_eq_true_eq] using h

/-- Canonical circuit counts are exactly the implemented checker's residue
counts at the encoded concrete program. -/
theorem circuitCount_checker (C : Checker) {n m : ℕ} (c : Layered (n+m))
    (x : Bits n) (out : Fin (n+m)) (d : ZMod 8) :
    circuitCount c x out d.val =
      ShiClassPP.countAccept (C.relation d) (C.encode (compile c.flatten x out))
        (hadamardCount c.flatten + hadamardCount c.flatten) :=
  compiled_pair_counts C c.flatten x out d

end BQPProgram
