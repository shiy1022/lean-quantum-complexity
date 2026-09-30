import «AMPUNI-replay-header-skip»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayHeaderSkip

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Skipping one valid unary field takes its length plus its delimiter step
and changes only the source stack. -/
theorem skip_nat_run (p : Phase) (hp : p ≠ 4) (n : Nat)
    (rest : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S source = (ShiBQP.encNat n).map bit ++ rest) :
    ∃ U : ∀ k, List (TopGam k),
      run^[n + 1] (some ⟨some p, v, S⟩) =
        some ⟨some (next p), some Cell.delim, U⟩
      ∧ U source = rest
      ∧ ∀ j : TopK, j ≠ source → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have hd : S source = Cell.delim :: rest := by
        simpa [ShiBQP.encNat, bit] using hsrc
      let U := Function.update S source rest
      refine ⟨U, ?_, ?_, ?_⟩
      · simpa [U] using delim_step p hp v S rest hd
      · simp [U]
      · intro j hj
        exact Function.update_of_ne hj _ _
  | succ n ih =>
      have henc : ((ShiBQP.encNat (n + 1)).map bit ++ rest) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        simp [ShiBQP.encNat, bit, List.replicate_succ,
          List.append_assoc]
      have hm : S source =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        rw [hsrc, henc]
      let T := Function.update S source
        ((ShiBQP.encNat n).map bit ++ rest)
      have hfirst : run^[1] (some ⟨some p, v, S⟩) =
          some ⟨some p, some Cell.mark, T⟩ := by
        simpa [T] using mark_step p hp v S _ hm
      have hTsrc : T source = (ShiBQP.encNat n).map bit ++ rest := by
        simp [T]
      obtain ⟨U, hrun, hUsrc, hUframe⟩ :=
        ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, hUsrc, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (n + 1) _ _ _ hfirst hrun)
      · intro j hj
        rw [hUframe j hj]
        exact Function.update_of_ne hj _ _

end ShiTMReplayHeaderSkip
