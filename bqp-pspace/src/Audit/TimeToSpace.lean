import Space.TimeToSpace

/-! # Fresh-import audit for certificate-to-space (S04) -/

open Turing

-- The checker bound needs only the polynomial-time certificate; no space hypothesis.
example (R : PvsNP.Str × PvsNP.Str → Bool)
    (c : TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R) :
    ∃ p : Polynomial ℕ, ∀ x : PvsNP.Str × PvsNP.Str,
      ShiSpace.SpaceBoundedOn c.tm ((PvsNP.encodePair x).map c.inputAlphabet.invFun)
        (p.eval (x.1.length + x.2.length)) := ShiSpace.checker_polySpace c

example : PvsNP.P ⊆ ShiSpace.PSPACE := ShiSpace.P_subset_PSPACE

#print axioms ShiSpace.exists_growth
#print axioms ShiSpace.spaceBoundedOn_of_outputsInTime
#print axioms ShiSpace.polySpace_of_polyTime
#print axioms ShiSpace.checker_polySpace
#print axioms ShiSpace.P_subset_PSPACE
