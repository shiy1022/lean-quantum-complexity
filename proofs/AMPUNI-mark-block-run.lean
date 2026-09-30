import «AMPUNI-piece-entry-param-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Starting directly at `copy` prepends a unary block without a delimiter. Repeating
this operation lets the table initializer form offsets such as `n + 3 * wit + anc`. -/
theorem mark_block_run_at (source : Fin 4) (dest : Fin 14)
    (hdest : dest ≠ 3) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr source) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runAt source dest)^[2 * n + 2]
        (some { l := some (.inr .copy), var := v, stk := S }) =
          some { l := some (.inr .done), var := none, stk := U }
      ∧ U (.inr source) = List.replicate n Cell.mark
      ∧ U (.inl (.inl dest)) =
          List.replicate n Cell.mark ++ S (.inl (.inl dest))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr source → j ≠ .inl (.inl dest) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨C, hcopy, hCsource, hCdest, hCscratch, hCframe⟩ :=
    copy_marks_run_at source dest hdest n v S hsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    simpa [hscratch] using hCscratch
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    restore_marks_run_at source dest n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hall := iterTwo (runAt source dest) (n + 1) (n + 1)
      _ _ _ hcopy hrestore
    have hcost : (n + 1) + (n + 1) = 2 * n + 2 := by omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · have hd : (.inl (.inl dest) : TopK) ≠ .inl (.inl (3 : Fin 14)) := by
      simp [hdest]
    rw [hUframe (.inl (.inl dest)) (by simp) hd, hCdest]
  · intro j hj0 hjd hj3
    rw [hUframe j hj0 hj3, hCframe j hj0 hjd hj3]

end ShiTMPieceEntry
