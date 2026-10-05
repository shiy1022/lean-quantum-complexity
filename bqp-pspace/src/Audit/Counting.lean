import Count.Enumeration

/-! # Fresh-import audit for fixed-width words and prefix counts (S05, S06) -/

-- The machine-side count at the last word equals the original PP count.
example (R : PvsNP.Str × PvsNP.Str → Bool) (x : PvsNP.Str) (m : ℕ) :
    ShiPPPSPACE.prefixCount R x m (2 ^ m) = ShiClassPP.countAccept R x m :=
  ShiPPPSPACE.prefixCount_full R x m

-- Increment walks the words in order and overflows exactly after the last one.
example (m j : ℕ) (hj : j < 2 ^ m) :
    ShiPPPSPACE.inc (ShiPPPSPACE.word m j) =
      (ShiPPPSPACE.word m (j + 1), decide (j + 1 = 2 ^ m)) := ShiPPPSPACE.inc_word m j hj

-- Width zero: the single empty word, and increment overflows at once.
example : ShiPPPSPACE.inc (ShiPPPSPACE.word 0 0) = ([], true) := rfl

#print axioms ShiPPPSPACE.val_lt
#print axioms ShiPPPSPACE.val_word
#print axioms ShiPPPSPACE.word_val
#print axioms ShiPPPSPACE.val_inc
#print axioms ShiPPPSPACE.inc_overflow_iff
#print axioms ShiPPPSPACE.inc_word
#print axioms ShiPPPSPACE.word_zero
#print axioms ShiPPPSPACE.prefixCount_succ
#print axioms ShiPPPSPACE.prefixCount_le
#print axioms ShiPPPSPACE.prefixCount_full
#print axioms ShiPPPSPACE.prefixCount_lt
#print axioms ShiPPPSPACE.pp_condition_iff
