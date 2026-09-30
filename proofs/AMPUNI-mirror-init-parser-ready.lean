import «AMPUNI-mirror-init-both-run»
import «AMPUNI-piece-sentinel»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

/-- The finite mirror controller establishes exactly the sentinel and reverse
premises required by the nested circuit parser for a completed piece layout. -/
theorem parser_ready (ps : List (Nat × Nat)) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hw : S (.inl (.inl (1 : Fin 14))) = pieceCells Prod.fst ps)
    (hb : S (.inl (.inl (2 : Fin 14))) = pieceCells Prod.snd ps)
    (hm8 : S (.inl (.inl (8 : Fin 14))) = [])
    (hm9 : S (.inl (.inl (9 : Fin 14))) = [])
    (hscratch : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (pa pb : List Cell),
      run^[(2 * (pieceCells Prod.fst ps).length + 3) +
          (2 * (pieceCells Prod.snd ps).length + 3)]
        (some { l := some .startWidth, var := v, stk := S }) =
          some { l := some .done, var := none, stk := U }
      ∧ U (.inl (.inl (1 : Fin 14))) = pieceCells Prod.fst ps
      ∧ U (.inl (.inl (2 : Fin 14))) = pieceCells Prod.snd ps
      ∧ U (.inl (.inl (8 : Fin 14))) = pa ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) = pb ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ pa.reverse = pieceCells Prod.fst ps
      ∧ pb.reverse = pieceCells Prod.snd ps
      ∧ (∀ y ∈ pa, y ≠ Cell.mirrorEnd)
      ∧ (∀ y ∈ pb, y ≠ Cell.mirrorEnd)
      ∧ ∀ j, j ≠ .inl (.inl (1 : Fin 14)) →
          j ≠ .inl (.inl (2 : Fin 14)) →
          j ≠ .inl (.inl (8 : Fin 14)) →
          j ≠ .inl (.inl (9 : Fin 14)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hUw, hUb, hU8, hU9, hU10, hframe⟩ :=
    both_run (pieceCells Prod.fst ps) (pieceCells Prod.snd ps)
      v S hw hb hm8 hm9 hscratch
  refine ⟨U, (pieceCells Prod.fst ps).reverse,
    (pieceCells Prod.snd ps).reverse, hrun, hUw, hUb,
    hU8, hU9, hU10, ?_, ?_, ?_, ?_, hframe⟩
  · simp
  · simp
  · intro y hy
    exact pieceCells_ne_mirrorEnd Prod.fst ps y
      (by simpa using hy)
  · intro y hy
    exact pieceCells_ne_mirrorEnd Prod.snd ps y
      (by simpa using hy)

end ShiTMMirrorInit
