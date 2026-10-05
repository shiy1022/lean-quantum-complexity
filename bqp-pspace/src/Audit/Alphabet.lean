import Space.ReachableAlphabet

/-! # Fresh-import audit for reachable alphabets and transient peaks (S03) -/

open Turing

-- No `Fintype (tm.Γ j)` assumption: finiteness of each reachable stack alphabet is proved.
example (tm : FinTM2) (j : tm.K) : (ShiSpace.stackSyms tm j).Finite :=
  ShiSpace.stackSyms_finite tm j

example (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (t : ℕ) (c : tm.Cfg)
    (h : (ShiTMSubroutine.run tm.m)^[t] (some (initList tm xs)) = some c)
    (j : tm.K) (a : tm.Γ j) (ha : a ∈ c.stk j) : a ∈ ShiSpace.stackSyms tm j :=
  ShiSpace.mem_stackSyms_of_reachable tm xs t c h j a ha

#print axioms ShiSpace.pushed_finite
#print axioms ShiSpace.stepAux_symsIn
#print axioms ShiSpace.iterate_symsIn
#print axioms ShiSpace.reachSyms_finite
#print axioms ShiSpace.stackSyms_finite
#print axioms ShiSpace.mem_stackSyms_of_reachable
#print axioms ShiSpace.size_le_peakAux
#print axioms ShiSpace.stepAux_size_le_peakAux
#print axioms ShiSpace.peakAux_le
#print axioms ShiSpace.exists_transient_bound
