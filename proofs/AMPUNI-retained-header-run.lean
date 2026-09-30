import «AMPUNI-retained-top-machine»
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMRetainedTop

open ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A valid retained unary header is consumed in exactly `n+1` steps, leaving its count on
the assigned top-level stack and every other stack unchanged. -/
theorem header_run (h : Header) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) = (ShiBQP.encNat n).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      topRun^[n + 1]
        (some { l := some (.inr h), var := v, stk := S }) =
          some { l := some (nextHeader h), var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) = rest
      ∧ U (.inr (headerStack h)) =
          List.replicate n Cell.mark ++ S (.inr (headerStack h))
      ∧ ∀ j, j ≠ .inl (.inl (11 : Fin 14)) →
          j ≠ .inr (headerStack h) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have hd : S (.inl (.inl (11 : Fin 14))) = Cell.delim :: rest := by
        simpa [ShiBQP.encNat, bit] using hsrc
      let U := Function.update S (.inl (.inl (11 : Fin 14))) rest
      refine ⟨U, ?_, ?_, ?_, ?_⟩
      · exact header_delim_step h v S rest hd
      · simp [U]
      · simp [U]
      · intro j hj11 hjc
        simp [U, Function.update_of_ne hj11]
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
      have hfirst : topRun^[1]
          (some { l := some (.inr h), var := v, stk := S }) =
            some { l := some (.inr h), var := some Cell.mark, stk := T } := by
        exact header_mark_step h v S _ hm
      have hTsrc : T (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encNat n).map bit ++ rest := by
        simp [T]
      obtain ⟨U, hrun, h11, hc, hframe⟩ := ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h11, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo topRun 1 (n + 1) _ _ _ hfirst hrun)
      · have hTc : T (.inr (headerStack h)) =
            Cell.mark :: S (.inr (headerStack h)) := by simp [T]
        rw [hc, hTc]
        simp [List.replicate_add, List.append_assoc]
      · intro j hj11 hjc
        rw [hframe j hj11 hjc]
        simp [T, Function.update_of_ne hjc, Function.update_of_ne hj11]

end ShiTMRetainedTop
