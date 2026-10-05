import «BQP-program-sweeps»
import «BQP-canonical-recursions»

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BQPProgram
open ShiShallow BQPPaths BQPGates

/-- Exact evaluation of the concrete doubled program, on one witness per pass.
The output and endpoint tests, and both phases, are those of the canonical paths. -/
theorem eval_compile_split (C : Checker) {n m : ℕ} (gs : List (Instr (n + m)))
    (x : Bits n) (out : Fin (n + m)) (u v : List Bool)
    (hu : u.length = hadamardCount gs) (hv : v.length = hadamardCount gs) :
    let z := Fin.append x (fun _ : Fin m => false)
    let y := forwardRun gs z u
    let y' := forwardRun gs.reverse y v
    C.eval (compile gs x out) (u ++ v) =
      if y out = true ∧ y' = z then
        some (phaseRun gs z u + adjointPhaseRun gs.reverse y v).val else none := by
  classical
  let z := Fin.append x (fun _ : Fin m => false)
  let y := forwardRun gs z u
  let y' := forwardRun gs.reverse y v
  change C.eval (compile gs x out) (u ++ v) =
    if y out = true ∧ y' = z then
      some (phaseRun gs z u + adjointPhaseRun gs.reverse y v).val else none
  have hload := (input_sweeps C).1 (List.ofFn z) 0 false false false (u ++ v)
  simp only [List.length_ofFn, List.foldl_append] at hload
  have hpre := canonical_witness_prefix gs z u v (by omega)
  have hdrop : (u ++ v).drop (hadamardCount gs) = v := by simp [← hu]
  obtain ⟨ct₁, hf⟩ := forward_sweep C gs z 0 false false false (u ++ v) (by simp; omega)
  rw [hpre.1, hpre.2, hdrop] at hf
  simp only [zero_add] at hf
  have ht := (block_transfer C).2.2.2.2 (n+m) out y (phaseRun gs z u) ct₁ false false v
  simp only [Bool.false_or] at ht
  change (wrap out [8]).foldl C.step (phaseRun gs z u, [], List.ofFn y, ct₁, false, false, v) =
    (phaseRun gs z u, [], List.ofFn y, ct₁, !(y out), false, v) at ht
  obtain ⟨ct₂, ha⟩ := adjoint_sweep C gs.reverse y (phaseRun gs z u) ct₁ (!(y out)) false v
    (by simpa [hadamardCount] using hv.ge)
  have hvdrop : v.drop (hadamardCount gs.reverse) = [] := by
    rw [hadamardCount_reverse, ← hv]
    exact List.drop_length
  rw [hvdrop] at ha
  have he := (input_sweeps C).2 (List.ofFn z) (List.ofFn y') (by simp)
    (phaseRun gs z u + adjointPhaseRun gs.reverse y v) ct₂ (!(y out)) false []
  simp only [List.length_ofFn, List.foldl_append] at he
  rw [C.eval_fold]
  simp only [compile, paddedInput, adjointBody, List.foldl_append]
  rw [hload, hf, ht, ha, he]
  have hlist : List.ofFn y' = List.ofFn z ↔ y' = z := by
    constructor
    · intro h
      funext i
      have hi := congrArg (fun l : List Bool => l[i.val]?) h
      simpa using hi
    · exact congrArg List.ofFn
  by_cases hy : y out = true <;> by_cases hz : y' = z <;>
    simp [hy, hz, hlist]

end BQPProgram
