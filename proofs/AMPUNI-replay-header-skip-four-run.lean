import «AMPUNI-replay-header-skip-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayHeaderSkip

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def skipCost (n wit anc out : Nat) : Nat :=
  (((n + 1) + (wit + 1)) + (anc + 1)) + (out + 1)

/-- Four unary fields are consumed without modifying their retained copies.
The source then begins with the original verifier-circuit encoding. -/
theorem skip_four_run (n wit anc out : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S source =
      (ShiBQP.encNat n).map bit ++
      (ShiBQP.encNat wit).map bit ++
      (ShiBQP.encNat anc).map bit ++
      (ShiBQP.encNat out).map bit ++ rest) :
    ∃ U : ∀ k, List (TopGam k),
      run^[skipCost n wit anc out]
        (some ⟨some (0 : Phase), v, S⟩) =
          some ⟨some (4 : Phase), some Cell.delim, U⟩
      ∧ U source = rest
      ∧ ∀ j : TopK, j ≠ source → U j = S j := by
  obtain ⟨A, hA, hAsrc, hAframe⟩ :=
    skip_nat_run 0 (by decide) n
      ((ShiBQP.encNat wit).map bit ++
        (ShiBQP.encNat anc).map bit ++
        (ShiBQP.encNat out).map bit ++ rest)
      v S (by simpa [List.append_assoc] using hsrc)
  obtain ⟨B, hB, hBsrc, hBframe⟩ :=
    skip_nat_run 1 (by decide) wit
      ((ShiBQP.encNat anc).map bit ++
        (ShiBQP.encNat out).map bit ++ rest)
      (some Cell.delim) A (by simpa [List.append_assoc] using hAsrc)
  obtain ⟨C, hC, hCsrc, hCframe⟩ :=
    skip_nat_run 2 (by decide) anc
      ((ShiBQP.encNat out).map bit ++ rest)
      (some Cell.delim) B (by simpa [List.append_assoc] using hBsrc)
  obtain ⟨U, hU, hUsrc, hUframe⟩ :=
    skip_nat_run 3 (by decide) out rest
      (some Cell.delim) C (by simpa using hCsrc)
  refine ⟨U, ?_, hUsrc, ?_⟩
  · have hAB := iterTwo run (n + 1) (wit + 1)
      _ _ _ (by simpa [next] using hA) (by simpa [next] using hB)
    have hABC := iterTwo run ((n + 1) + (wit + 1)) (anc + 1)
      _ _ _ hAB (by simpa [next] using hC)
    exact iterTwo run (((n + 1) + (wit + 1)) + (anc + 1))
      (out + 1) _ _ _ hABC (by simpa [next] using hU)
  · intro j hj
    rw [hUframe j hj, hCframe j hj, hBframe j hj, hAframe j hj]

end ShiTMReplayHeaderSkip
