import «AMPUNI-readout-machine»
import «AMPUNI-fanout-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadout
open ShiTMLayoutMachine ShiTMRetainedTop

/-- Copy a unary register to the output while saving its marks for restoration. -/
theorem copy_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hsrc : S (wire k) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.copy pc k), v, S⟩) =
        some ⟨some (.restore pc k), none, U⟩
      ∧ U (wire k) = []
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = List.replicate n Cell.mark ++ S scratch
      ∧ ∀ j, j ≠ wire k → j ≠ output → j ≠ scratch → U j = S j := by
  have hks := wire_ne_scratch k
  have hko := wire_ne_output k
  have hso : scratch ≠ output := by decide
  induction n generalizing v S with
  | zero =>
      have he : S (wire k) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, by simp, by simp, by intro j _ _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S (wire k) = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update (Function.update S (wire k) (List.replicate n Cell.mark))
          output (Cell.mark :: S output))
        scratch (Cell.mark :: S scratch)
      have hfirst : run (some ⟨some (.copy pc k), v, S⟩) =
          some ⟨some (.copy pc k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T,
          hks, hks.symm, hko, hko.symm, hso, hso.symm]
      obtain ⟨U, hr, hs, ho, ht, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks, hko])
      refine ⟨U, ?_, hs, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [ho]
        simp [T, hso.symm, List.replicate_add, List.append_assoc]
      · rw [ht]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjo hjs
        rw [hf j hjk hjo hjs]
        simp [T, hjk, hjo, hjs]

/-- Restore the register and clear the saved unary marks. -/
theorem restore_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hs : S scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.restore pc k), v, S⟩) =
        some ⟨some (.delimiter pc), none, U⟩
      ∧ U scratch = []
      ∧ U (wire k) = List.replicate n Cell.mark ++ S (wire k)
      ∧ ∀ j, j ≠ wire k → j ≠ scratch → U j = S j := by
  have hks := wire_ne_scratch k
  induction n generalizing v S with
  | zero =>
      have he : S scratch = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S scratch = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S scratch (List.replicate n Cell.mark))
        (wire k) (Cell.mark :: S (wire k))
      have hfirst : run (some ⟨some (.restore pc k), v, S⟩) =
          some ⟨some (.restore pc k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T, hks]
      obtain ⟨U, hr, ht, hk, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks.symm])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [hk]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjs
        rw [hf j hjk hjs]
        simp [T, hjk, hjs]

/-- Emit a unary value without consuming its register. The delimiter is a
separate control step, allowing reuse for the layer header and both operands. -/
theorem field_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hsrc : S (wire k) = List.replicate n Cell.mark) (hs : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+2] (some ⟨some (.copy pc k), v, S⟩) =
        some ⟨some (.delimiter pc), none, U⟩
      ∧ U (wire k) = List.replicate n Cell.mark
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = []
      ∧ ∀ j, j ≠ wire k → j ≠ output → j ≠ scratch → U j = S j := by
  obtain ⟨T, ht, htk, hto, hts, htf⟩ := copy_run pc k n v S hsrc
  obtain ⟨U, hu, hus, huk, huf⟩ :=
    restore_run pc k n none T (by simpa [hs] using hts)
  refine ⟨U, ?_, ?_, ?_, hus, ?_⟩
  · have h := ShiTMFanout.iterTwo run (n+1) (n+1) _ _ _ ht hu
    have hc : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [hc] using h
  · rw [huk, htk, List.append_nil]
  · rw [huf output (wire_ne_output k).symm (by decide), hto]
  · intro j hjk hjo hjs
    rw [huf j hjk hjs, htf j hjk hjo hjs]

end ShiTMReadout
