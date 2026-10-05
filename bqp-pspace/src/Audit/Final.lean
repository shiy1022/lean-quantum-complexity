import BQPToPSPACE

/-!
# Fresh-import audit of the final endpoints (S15, S16)

Exact types against the original, unchanged class definitions; the corrected space class
unfolded to its primitive content; axiom reports for the endpoints and the main construction.
-/

open Turing

-- The endpoints, with their exact public types.
example : ShiClassPP.PP ⊆ ShiSpace.PSPACE := ShiSpace.pp_subset_pspace
example : ShiBQP.BQP ⊆ ShiSpace.PSPACE := ShiBQP.bqp_subset_pspace

-- PP is the original counting class (no altered witness length or threshold).
example : ShiClassPP.PP =
    {L | ∃ (R : PvsNP.Str × PvsNP.Str → Bool) (k : ℕ), PvsNP.PolyTimeChecker R ∧
      ∀ x : PvsNP.Str, x ∈ L ↔
        2 * ShiClassPP.countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k)} := rfl

-- The composition uses the published BQP ⊆ PP endpoint unchanged.
example : ShiBQP.BQP ⊆ ShiClassPP.PP := ShiBQP.bqp_subset_pp

-- The corrected PSPACE, unfolded: a total TM2Computable decider plus a polynomial bound on the
-- total stack length of every configuration reachable by iterating that machine's step.
example : ShiSpace.PSPACE =
    {L : Language Bool | ∃ χ : List Bool → Bool,
      (∃ c : TM2Computable (id : List Bool → List Bool) Computability.encodeBool χ,
        ∃ p : Polynomial ℕ, ∀ (x : List Bool) (t : ℕ) (d : c.tm.Cfg),
          (fun o : Option c.tm.Cfg => o.bind c.tm.step)^[t]
              (some (initList c.tm (x.map c.inputAlphabet.invFun))) = some d →
            ∑ k, (d.stk k).length ≤ p.eval x.length) ∧
      ∀ x, x ∈ L ↔ χ x = true} := rfl

-- The decider for a PP witness is the concrete enumerator built from the checker's machine.
example {R : PvsNP.Str × PvsNP.Str → Bool}
    (c : TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R) (k : ℕ) :
    (ShiPPPSPACE.decider c k).tm = ShiPPPSPACE.machine c.tm c.inputAlphabet c.outputAlphabet k :=
  rfl

#print axioms ShiSpace.pp_subset_pspace
#print axioms ShiBQP.bqp_subset_pspace
#print axioms ShiPPPSPACE.polySpaceDecider_ppχ
#print axioms ShiPPPSPACE.decider
#print axioms ShiPPPSPACE.full_run
#print axioms ShiPPPSPACE.head_step
#print axioms ShiPPPSPACE.head_upto
#print axioms ShiPPPSPACE.eval_boundPoly
#print axioms ShiPPPSPACE.init_seg
#print axioms ShiPPPSPACE.init_round
#print axioms ShiPPPSPACE.init_rounds
#print axioms ShiPPPSPACE.iter_prep
#print axioms ShiPPPSPACE.iter_check
#print axioms ShiPPPSPACE.iter_ans
#print axioms ShiPPPSPACE.iter_incC
#print axioms ShiPPPSPACE.iter_incW
#print axioms ShiPPPSPACE.iter_seg
#print axioms ShiPPPSPACE.final_seg
#print axioms ShiPPPSPACE.initList_machine
#print axioms ShiPPPSPACE.haltList_machine
#print axioms ShiPPPSPACE.initList_stk_eq
#print axioms ShiPPPSPACE.haltList_pop
#print axioms ShiPPPSPACE.loopOut_one
#print axioms ShiPPPSPACE.loopOut_two
#print axioms ShiPPPSPACE.loopOut_clear
#print axioms ShiPPPSPACE.segE_loop
