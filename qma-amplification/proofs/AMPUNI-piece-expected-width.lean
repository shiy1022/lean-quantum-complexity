import «AMPUNI-piece-controller-program-tables»
import «AMPUNI-copy-local-blocks»

set_option autoImplicit false

namespace ShiTMPieceController

open ShiTMLayoutMachine

/-- Each copy-specific local layout covers the complete verifier width. -/
theorem expectedPieces_width (copy : Fin 3) (n wit anc : Nat) :
    ((expectedPieces copy n wit anc).map Prod.fst).sum =
      n + (wit + (anc + 1)) := by
  fin_cases copy
  · simpa [expectedPieces] using copyPieces0_width n wit anc
  · simpa [expectedPieces] using copyPieces1_width n wit anc
  · simpa [expectedPieces] using copyPieces2_width n wit anc

end ShiTMPieceController
