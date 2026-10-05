import Space.Model

/-!
# Fresh-import audit for the corrected space model (S01)

Exact-type checks: the class has type `Set (Language Bool)`, and fully unfolding it exposes
only a total `TM2Computable` certificate plus a polynomial bound on the stack length of every
reachable configuration of that same machine. No time bound occurs.
-/

open Turing

example : Set (Language Bool) := ShiSpace.PSPACE

example : ShiSpace.PSPACE =
    {L : Language Bool | ∃ χ : List Bool → Bool, ShiSpace.PolySpaceDecider χ ∧
      ∀ x, x ∈ L ↔ χ x = true} := rfl

example (χ : List Bool → Bool) : ShiSpace.PolySpaceDecider χ ↔
    ∃ c : TM2Computable (id : List Bool → List Bool) Computability.encodeBool χ,
      ∃ p : Polynomial ℕ, ∀ (x : List Bool) (t : ℕ) (d : c.tm.Cfg),
        (fun o : Option c.tm.Cfg => o.bind c.tm.step)^[t]
            (some (initList c.tm (x.map c.inputAlphabet.invFun))) = some d →
          ∑ k, (d.stk k).length ≤ p.eval x.length := Iff.rfl

example (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    ShiSpace.cfgSpace tm (initList tm xs) = xs.length := ShiSpace.cfgSpace_initList tm xs

#print axioms ShiSpace.cfgSpace_initList
#print axioms ShiSpace.cfgSpace_haltList
#print axioms ShiSpace.cfgSpace_haltList_encodeBool
#print axioms ShiSpace.SpaceBoundedOn.mono
#print axioms ShiSpace.SpaceBoundedOn.input_le
#print axioms ShiSpace.SpaceBoundedOn.output_le
#print axioms ShiSpace.PolySpaceDecider.mono
#print axioms ShiSpace.PolySpaceDecider.length_le
#print axioms ShiSpace.mem_PSPACE
