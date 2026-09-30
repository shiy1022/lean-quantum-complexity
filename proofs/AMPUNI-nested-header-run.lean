import «AMPUNI-nested-header-step»
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The concrete header scanner consumes a complete unary count in exactly `n+1` steps,
loads the chosen counter, and preserves its reverse encoding on the output stack. -/
theorem nested_header_run (k : Fin 2) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (OuterGam j))
    (hsrc : S (.inl (11 : Fin 14)) = (ShiBQP.encNat n).map bit ++ rest) :
    ∃ (U : ∀ j, List (OuterGam j)),
      nestedRun^[n + 1]
        (some { l := some (.inr (headerAt k)), var := v, stk := S }) =
          some { l := some (.inr (headerNext k)), var := some Cell.delim, stk := U }
      ∧ U (.inl (11 : Fin 14)) = rest
      ∧ U (.inr k) = List.replicate n Cell.mark ++ S (.inr k)
      ∧ U (.inl (13 : Fin 14)) = ((ShiBQP.encNat n).map bit).reverse ++
          S (.inl (13 : Fin 14))
      ∧ ∀ j, j ≠ .inl (11 : Fin 14) → j ≠ .inr k →
          j ≠ .inl (13 : Fin 14) → U j = S j := by
  induction n generalizing v S with
  | zero =>
    have hd : S (.inl (11 : Fin 14)) = Cell.delim :: rest := by
      simpa [ShiBQP.encNat, bit] using hsrc
    let U := Function.update
      (Function.update S (.inl (11 : Fin 14)) rest)
      (.inl (13 : Fin 14)) (Cell.delim :: S (.inl (13 : Fin 14)))
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · exact nested_header_delim k v S rest hd
    · simp [U]
    · simp [U]
    · simp [U, ShiBQP.encNat, bit]
    · intro j hj11 hjc hj13
      simp [U, Function.update_of_ne hj13, Function.update_of_ne hj11]
  | succ n ih =>
    have henc : ((ShiBQP.encNat (n + 1)).map bit ++ rest) =
        Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
      simp [ShiBQP.encNat, bit, List.replicate_succ, List.append_assoc]
    have hm : S (.inl (11 : Fin 14)) =
        Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
      rw [hsrc, henc]
    let T := Function.update
      (Function.update
        (Function.update S (.inl (11 : Fin 14))
          ((ShiBQP.encNat n).map bit ++ rest))
        (.inr k) (Cell.mark :: S (.inr k)))
      (.inl (13 : Fin 14)) (Cell.mark :: S (.inl (13 : Fin 14)))
    have hfirst : nestedRun^[1]
        (some { l := some (.inr (headerAt k)), var := v, stk := S }) =
          some { l := some (.inr (headerAt k)), var := some Cell.mark, stk := T } := by
      exact nested_header_mark k v S _ hm
    have hTsrc : T (.inl (11 : Fin 14)) = (ShiBQP.encNat n).map bit ++ rest := by
      simp [T]
    obtain ⟨U, hrun, h11, hc, h13, hframe⟩ :=
      ih (some Cell.mark) T hTsrc
    refine ⟨U, ?_, h11, ?_, ?_, ?_⟩
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (iterTwo nestedRun 1 (n + 1) _ _ _ hfirst hrun)
    · have hTc : T (.inr k) = Cell.mark :: S (.inr k) := by simp [T]
      rw [hc, hTc]
      simp [List.replicate_add, List.append_assoc]
    · have hT13 : T (.inl (13 : Fin 14)) =
          Cell.mark :: S (.inl (13 : Fin 14)) := by simp [T]
      rw [h13, hT13]
      simp [ShiBQP.encNat, bit, List.replicate_succ, List.reverse_append,
        List.append_assoc]
    · intro j hj11 hjc hj13
      rw [hframe j hj11 hjc hj13]
      simp [T, Function.update_of_ne hj13, Function.update_of_ne hjc,
        Function.update_of_ne hj11]

end ShiTMOuterLift
