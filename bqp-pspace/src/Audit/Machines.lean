import Machine.Increment
import Machine.MajorityTest
import Machine.CheckerCall

/-! # Fresh-import audit for wrapper machine routines (S07–S11) -/

#print axioms ShiPPPSPACE.update_join_inr
#print axioms ShiPPPSPACE.update_join_inl
#print axioms ShiPPPSPACE.size_update
#print axioms ShiPPPSPACE.size_join
#print axioms ShiPPPSPACE.loopOut_cons
#print axioms ShiPPPSPACE.loopOut_apply_ne
#print axioms ShiPPPSPACE.loopOut_src
#print axioms ShiPPPSPACE.step_loop_cons
#print axioms ShiPPPSPACE.step_loop_nil
#print axioms ShiPPPSPACE.loop_run
#print axioms ShiPPPSPACE.size_loopOut
#print axioms ShiPPPSPACE.loop_seg
#print axioms ShiPPPSPACE.loopOut_single_apply
#print axioms ShiPPPSPACE.size_incOut
#print axioms ShiPPPSPACE.inc_seg
#print axioms ShiPPPSPACE.answer_scanAll
#print axioms ShiPPPSPACE.scan_seg

-- Strict majority, ties rejected, including width zero.
example (m : ℕ) (l : List Bool) (hl : l.length = m + 1) :
    ShiPPPSPACE.answer (ShiPPPSPACE.scanAll (false, false, false) l) =
      decide (2 * ShiPPPSPACE.val l > 2 ^ m) := ShiPPPSPACE.answer_scanAll m l hl
example : ShiPPPSPACE.answer (ShiPPPSPACE.scanAll (false, false, false) [false, true]) = true := rfl
example : ShiPPPSPACE.answer (ShiPPPSPACE.scanAll (false, false, false) [true, false, true]) = true := rfl
example : ShiPPPSPACE.answer (ShiPPPSPACE.scanAll (false, false, false) [false, true, false]) = false := rfl
#print axioms ShiPPPSPACE.stepAux_tr
#print axioms ShiPPPSPACE.step_emb
#print axioms ShiPPPSPACE.iterate_emb
#print axioms ShiPPPSPACE.iterate_emb_halt
#print axioms ShiPPPSPACE.seg_emb
