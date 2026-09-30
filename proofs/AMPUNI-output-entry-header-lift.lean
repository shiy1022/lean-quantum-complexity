import «AMPUNI-output-entry-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The existing unary-header run lifts to the redirected finite front-end. -/
theorem header_run_lift (h : Header) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ rest) :
    run^[n + 1]
        (some { l := some (headerLabel h), var := v, stk := S }) =
      (topRun^[n + 1]
        (some { l := some (.inr h), var := v, stk := S })).map
          (liftCfg mapTop) := by
  induction n generalizing v S with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one] using header_step h v S
  | succ n ih =>
      have henc : ((ShiBQP.encNat (n + 1)).map bit ++ rest) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        simp [ShiBQP.encNat, bit, List.replicate_succ, List.append_assoc]
      have hm : S (.inl (.inl (11 : Fin 14))) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        rw [hsrc, henc]
      let T := Function.update
        (Function.update S (.inl (.inl (11 : Fin 14)))
          ((ShiBQP.encNat n).map bit ++ rest))
        (.inr (headerStack h))
        (Cell.mark :: S (.inr (headerStack h)))
      have ht : topRun
          (some { l := some (.inr h), var := v, stk := S }) =
            some { l := some (.inr h), var := some Cell.mark, stk := T } := by
        exact header_mark_step h v S _ hm
      have he : run
          (some { l := some (headerLabel h), var := v, stk := S }) =
            some { l := some (headerLabel h), var := some Cell.mark, stk := T } := by
        rw [header_step, ht]
        rfl
      have hTsrc : T (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encNat n).map bit ++ rest := by
        simp [T]
      have hrec := ih (some Cell.mark) T hTsrc
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        Function.iterate_succ_apply, he, ht] using hrec

theorem entry_header_run (h : Header) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[n + 1]
        (some { l := some (headerLabel h), var := v, stk := S }) =
          some { l := some (mapTop (nextHeader h)), var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) = rest
      ∧ U (.inr (headerStack h)) =
          List.replicate n Cell.mark ++ S (.inr (headerStack h))
      ∧ ∀ j, j ≠ .inl (.inl (11 : Fin 14)) →
          j ≠ .inr (headerStack h) → U j = S j := by
  obtain ⟨U, hr, h11, hc, hf⟩ := header_run h n rest v S hsrc
  refine ⟨U, ?_, h11, hc, hf⟩
  rw [header_run_lift h n rest v S hsrc, hr]
  rfl

end ShiTMOutputEntry
