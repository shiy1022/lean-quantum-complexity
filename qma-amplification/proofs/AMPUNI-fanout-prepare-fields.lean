import «AMPUNI-fanout-prepare-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2
namespace ShiTMFanoutPrepare
open ShiTMLayoutMachine ShiTMRetainedTop

/-- Copy one retained header into the count/base accumulators with fixed
multiplicities, saving its marks for restoration. -/
theorem copy_run (second : Bool) (h : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hs : S (source h) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[n+1] (some ⟨some (.copy h), v, S⟩) =
        some ⟨some (.restore h), none, U⟩
      ∧ U (source h) = []
      ∧ U (port 0) = List.replicate (n * countCoeff h) Cell.mark ++ S (port 0)
      ∧ U (port 2) = List.replicate (n * baseCoeff second h) Cell.mark ++ S (port 2)
      ∧ U scratch = List.replicate n Cell.mark ++ S scratch
      ∧ ∀ j, j ≠ source h → j ≠ port 0 → j ≠ port 2 → j ≠ scratch → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (source h) = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by simp, by simp, by intro j _ _ _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S (source h) = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update
        (Function.update
          (Function.update (Function.update S (source h) (List.replicate n Cell.mark))
            scratch (Cell.mark :: S scratch))
          (port 0) (List.replicate (countCoeff h) Cell.mark ++ S (port 0)))
        (port 2) (List.replicate (baseCoeff second h) Cell.mark ++ S (port 2))
      have hfirst : run second (some ⟨some (.copy h), v, S⟩) =
          some ⟨some (.copy h), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, pushMarks_step, T]
      obtain ⟨U, hr, hu, h0, h2, ht, hf⟩ :=
        ih (some Cell.mark) T (by simp [T])
      refine ⟨U, ?_, hu, ?_, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]; exact hr
      · rw [h0]
        simp [T, Nat.add_mul, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
      · rw [h2]
        simp [T, Nat.add_mul, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
      · rw [ht]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjs hj0 hj2 hjt
        rw [hf j hjs hj0 hj2 hjt]
        simp [T, hjs, hj0, hj2, hjt]

theorem restore_run (second : Bool) (h : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hs : S scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[n+1] (some ⟨some (.restore h), v, S⟩) =
        some ⟨some (afterField h), none, U⟩
      ∧ U scratch = []
      ∧ U (source h) = List.replicate n Cell.mark ++ S (source h)
      ∧ ∀ j, j ≠ source h → j ≠ scratch → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S scratch = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S scratch = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S scratch (List.replicate n Cell.mark))
        (source h) (Cell.mark :: S (source h))
      have hfirst : run second (some ⟨some (.restore h), v, S⟩) =
          some ⟨some (.restore h), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T]
      obtain ⟨U, hr, ht, hu, hf⟩ := ih (some Cell.mark) T (by simp [T])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]; exact hr
      · rw [hu]; simp [T, List.replicate_add, List.append_assoc]
      · intro j hjs hjt
        rw [hf j hjs hjt]
        simp [T, hjs, hjt]

/-- The source and every stack other than the two accumulators are restored.
This stronger frame includes the retained output-index/archive stack. -/
theorem field_run (second : Bool) (h : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hs : S (source h) = List.replicate n Cell.mark) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[2*n+2] (some ⟨some (.copy h), v, S⟩) =
        some ⟨some (afterField h), none, U⟩
      ∧ U (port 0) = List.replicate (n * countCoeff h) Cell.mark ++ S (port 0)
      ∧ U (port 2) = List.replicate (n * baseCoeff second h) Cell.mark ++ S (port 2)
      ∧ U scratch = []
      ∧ ∀ j, j ≠ port 0 → j ≠ port 2 → U j = S j := by
  obtain ⟨T, hr, hsT, h0T, h2T, htT, hfT⟩ := copy_run second h n v S hs
  obtain ⟨U, hu, htU, hsU, hfU⟩ :=
    restore_run second h n none T (by simpa [ht] using htT)
  refine ⟨U, ?_, ?_, ?_, htU, ?_⟩
  · have hc : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [hc] using ShiTMFanout.iterTwo (run second) (n+1) (n+1) _ _ _ hr hu
  · rw [hfU (port 0) (by simp) (by decide), h0T]
  · rw [hfU (port 2) (by simp) (by decide), h2T]
  · intro j hj0 hj2
    by_cases hjs : j = source h
    · subst j; rw [hsU, hsT, List.append_nil, hs]
    by_cases hjt : j = scratch
    · subst j; rw [htU, ht]
    rw [hfU j hjs hjt, hfT j hjs hj0 hj2 hjt]

end ShiTMFanoutPrepare
