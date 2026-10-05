import «AMPUNI-output-entry-full-run»
import «AMPUNI-copy-local-blocks»
import «AMPUNI-piece-sentinel»

set_option autoImplicit false

namespace ShiTMOutputEntry

open ShiTMLayoutMachine

/-- The completed amplification table covers a full original verifier block. -/
theorem ampPieces_fit (n wit anc : Nat) :
    n + (wit + (anc + 1)) ≤
      ((ShiTMRawLayout.ampPieces n wit anc).map Prod.fst).sum := by
  rw [ampPieces_split]
  simp [List.map_append, List.sum_append, copyPieces0_width,
    copyPieces1_width, copyPieces2_width, copyTail]

theorem ampPieces_width_mirror_good (n wit anc : Nat) :
    ∀ y ∈ (pieceCells Prod.fst
      (ShiTMRawLayout.ampPieces n wit anc)).reverse,
      y ≠ Cell.mirrorEnd := by
  intro y hy
  exact pieceCells_ne_mirrorEnd Prod.fst
    (ShiTMRawLayout.ampPieces n wit anc) y (by simpa using hy)

theorem ampPieces_base_mirror_good (n wit anc : Nat) :
    ∀ y ∈ (pieceCells Prod.snd
      (ShiTMRawLayout.ampPieces n wit anc)).reverse,
      y ≠ Cell.mirrorEnd := by
  intro y hy
  exact pieceCells_ne_mirrorEnd Prod.snd
    (ShiTMRawLayout.ampPieces n wit anc) y (by simpa using hy)

end ShiTMOutputEntry
