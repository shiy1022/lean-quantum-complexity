import «AMPUNI-layout-data»
import Theorems.Thm_ShiTM_piecewise_layout_block_residual_stack_lengths_are_exact

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- The canonical number of cells left on the piece-length stack by the destructive
layout walk.  Unlike the older public composite's existential `r1`, this is a function
of the encoded piece list and wire alone. -/
noncomputable def residualPiece : List (Nat × Nat) → Nat → Nat :=
  Classical.choose ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact

/-- The canonical number of cells left on the piece-base stack by the destructive
layout walk. -/
noncomputable def residualBase : List (Nat × Nat) → Nat → Nat :=
  Classical.choose
    (Classical.choose_spec ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact)

/-- WIRE-2 specialized to the concrete amplification-layout machine, with the two
residual stack lengths identified with fixed functions of `(ps,w)`. -/
noncomputable def exactWireRunner := by
  rcases program_equations 0 with
    ⟨hwire, hafterPiece, hafterBase, hfinishPiece, hfinishBase,
      hdispatch, hemitDelim, hemitIndex, hmark, hjoin,
      hreloadPiece, hreloadPieceMirror, hreloadPieceSentinel, hreloadPieceRestore,
      hreloadBase, hreloadBaseMirror, hreloadBaseSentinel, hreloadBaseRestore⟩
  have hs := Classical.choose_spec
    (Classical.choose_spec ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact)
  exact hs.2.2.2.2.1
    machine
    (mv := .mark) (ml := .mark) (dl := .delim)
    (mb := .mark) (db := .delim) (mdc := .mark) (m := .mark)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hwire hafterPiece hafterBase hfinishPiece hfinishBase
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl)
    rfl rfl
    depth cost (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (pieceCells Prod.fst) (pieceCells Prod.snd)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl

end ShiTMLayoutMachine
