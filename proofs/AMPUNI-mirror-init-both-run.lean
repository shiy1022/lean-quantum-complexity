import «AMPUNI-mirror-init-table-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem both_run (widths bases : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hwidth : S (.inl (.inl (1 : Fin 14))) = widths)
    (hbase : S (.inl (.inl (2 : Fin 14))) = bases)
    (hm8 : S (.inl (.inl (8 : Fin 14))) = [])
    (hm9 : S (.inl (.inl (9 : Fin 14))) = [])
    (hscratch : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[(2 * widths.length + 3) + (2 * bases.length + 3)]
        (some { l := some .startWidth, var := v, stk := S }) =
          some { l := some .done, var := none, stk := U }
      ∧ U (.inl (.inl (1 : Fin 14))) = widths
      ∧ U (.inl (.inl (2 : Fin 14))) = bases
      ∧ U (.inl (.inl (8 : Fin 14))) = widths.reverse ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) = bases.reverse ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inl (.inl (1 : Fin 14)) →
          j ≠ .inl (.inl (2 : Fin 14)) →
          j ≠ .inl (.inl (8 : Fin 14)) →
          j ≠ .inl (.inl (9 : Fin 14)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  obtain ⟨T, hwidthRun, hTwidth, hTm8, hT10, hTframe⟩ :=
    table_run .width widths v S hwidth hm8 hscratch
  have hTbase : T (.inl (.inl (2 : Fin 14))) = bases := by
    rw [hTframe _ (by decide) (by decide) (by decide), hbase]
  have hTm9 : T (.inl (.inl (9 : Fin 14))) = [] := by
    rw [hTframe _ (by decide) (by decide) (by decide), hm9]
  obtain ⟨U, hbaseRun, hUbase, hUm9, hU10, hUframe⟩ :=
    table_run .base bases none T hTbase hTm9 hT10
  refine ⟨U, ?_, ?_, hUbase, ?_, hUm9, hU10, ?_⟩
  · exact iterTwo run (2 * widths.length + 3) (2 * bases.length + 3)
      _ _ _ hwidthRun hbaseRun
  · rw [hUframe _ (by decide) (by decide) (by decide)]
    simpa [sourceIndex] using hTwidth
  · rw [hUframe _ (by decide) (by decide) (by decide)]
    simpa [mirrorIndex] using hTm8
  · intro j hj1 hj2 hj8 hj9 hj10
    rw [hUframe j hj2 hj9 hj10, hTframe j hj1 hj8 hj10]

end ShiTMMirrorInit
