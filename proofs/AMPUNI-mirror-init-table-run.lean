import «AMPUNI-mirror-init-restore-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem table_run (table : Table) (xs : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inl (.inl (sourceIndex table))) = xs)
    (hmirror : S (.inl (.inl (mirrorIndex table))) = [])
    (hscratch : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * xs.length + 3]
        (some { l := some (startPhase table), var := v, stk := S }) =
          some { l := some (nextPhase table), var := none, stk := U }
      ∧ U (.inl (.inl (sourceIndex table))) = xs
      ∧ U (.inl (.inl (mirrorIndex table))) =
          xs.reverse ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inl (.inl (sourceIndex table)) →
          j ≠ .inl (.inl (mirrorIndex table)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  let T := Function.update S (.inl (.inl (mirrorIndex table)))
    (Cell.mirrorEnd :: S (.inl (.inl (mirrorIndex table))))
  have hstart : run^[1]
      (some { l := some (startPhase table), var := v, stk := S }) =
        some { l := some (copyPhase table), var := v, stk := T } :=
    start_step table v S
  have hTsource : T (.inl (.inl (sourceIndex table))) = xs := by
    cases table <;> simpa [T, sourceIndex, mirrorIndex] using hsource
  obtain ⟨C, hcopy, hCsource, hCmirror, hCscratch, hCframe⟩ :=
    copy_run table xs v T hTsource
  have hTmirror : T (.inl (.inl (mirrorIndex table))) =
      [Cell.mirrorEnd] := by
    simpa [T, hmirror]
  have hTscratch : T (.inl (.inl (10 : Fin 14))) = [] := by
    cases table <;> simpa [T, mirrorIndex] using hscratch
  have hCscratch' : C (.inl (.inl (10 : Fin 14))) = xs.reverse := by
    simpa [hTscratch] using hCscratch
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    restore_run table xs.reverse none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo run 1 (xs.length + 1) _ _ _ hstart hcopy
    have hall := iterTwo run (1 + (xs.length + 1))
      (xs.reverse.length + 1) _ _ _ hfirst hrestore
    have hcost : (1 + (xs.length + 1)) +
        (xs.reverse.length + 1) = 2 * xs.length + 3 := by simp; omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · have hm0 : (.inl (.inl (mirrorIndex table)) : TopK) ≠
        .inl (.inl (sourceIndex table)) := by
      cases table <;> decide
    have hm10 : (.inl (.inl (mirrorIndex table)) : TopK) ≠
        .inl (.inl (10 : Fin 14)) := by
      cases table <;> decide
    rw [hUframe _ hm0 hm10, hCmirror, hTmirror]
  · intro j hj0 hjm hj10
    rw [hUframe j hj0 hj10, hCframe j hj0 hjm hj10]
    simp [T, Function.update_of_ne hjm]

end ShiTMMirrorInit
