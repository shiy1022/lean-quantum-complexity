import «BQP-family-counting»
import «BQP-short-machine-outputs»

set_option autoImplicit false
namespace BQPProgram
open ShiClassPP

 theorem familyH_polyBound (F : ShiClass.Family) (hwf : ShiBQP.WellFormed F)
    (hpoly : ShiBQP.PolyBounded F) :
    ∃ r : Polynomial ℕ, ∀ x : List Bool, familyH F x ≤ r.eval x.length := by
  obtain ⟨q, hd, ha⟩ := hpoly
  refine ⟨q * (Polynomial.X + q + 1), fun x => ?_⟩
  have h := BQPChecked.reference11.2.2.1 F hwf q hd ha
    (fun _ g => match g with | ShiShallow.Instr.h _ => true | _ => false) x.length
  convert h using 1
  unfold familyH BQPPaths.hadamardCount
  congr 1
  funext g
  cases g <;> rfl

/-- The explicit long-input checker. Its semantics are proved below; polynomial
runtime of its compiler, paired prefix, and bucket router remains to be proved. -/
noncomputable def longRelation (F : ShiClass.Family) : List Bool × List Bool → Bool :=
  BQPCounting.combinedChecker (fun x => familyH F x + 1)
    (fun d => BQPCounting.pairedPrefix (familyResidue checker F d))

noncomputable def patchedRelation (L : Language Bool) (F : ShiClass.Family) :
    List Bool × List Bool → Bool := by
  classical
  exact BQPCounting.shortChecker (decide ([] ∈ L)) (decide ([false] ∈ L))
    (decide ([true] ∈ L)) (longRelation F)

/-- The original BQP assumptions suffice for strict-majority correctness of one
explicit checker at the PP witness length, including all three short inputs.
This is a counting reduction; it does not assert the remaining runtime claim. -/
theorem bqp_counting_reduction (L : Language Bool) (hL : L ∈ ShiBQP.BQP) :
    ∃ (F : ShiClass.Family) (k : ℕ), ShiBQP.Uniform F ∧ ShiBQP.WellFormed F ∧
      ShiBQP.PolyBounded F ∧ ∀ x : List Bool,
        (x ∈ L ↔ 2 * countAccept (patchedRelation L F) x (x.length ^ k) >
          2 ^ (x.length ^ k)) := by
  classical
  obtain ⟨F, huni, hwf, hpoly, hdec⟩ := hL
  obtain ⟨r, hr⟩ := familyH_polyBound F hwf hpoly
  obtain ⟨k, hk⟩ := BQPCounting.normalized_long_majority L (familyH F)
    (familyResidue checker F) (fun x => F.accept x.length (ShiBQP.toBits x)) r hr
    (fun x _ => family_acceptance checker F x)
    (fun x => (hdec x).1) (fun x => (hdec x).2)
  refine ⟨F, k, huni, hwf, hpoly, ?_⟩
  exact BQPCounting.patched_majority L (longRelation F) k
    (decide ([] ∈ L)) (decide ([false] ∈ L)) (decide ([true] ∈ L))
    (by simp) (by simp) (by simp) hk

/-- The checked short dispatcher reduces the remaining runtime obligation to
that of the explicit long-input relation, without Boolean closure assumptions. -/
theorem patchedRelation_polyTime (L : Language Bool) (F : ShiClass.Family)
    (h : PvsNP.PolyTimeChecker (longRelation F)) :
    PvsNP.PolyTimeChecker (patchedRelation L F) := by
  classical
  exact BQPShortMachine.shortChecker_polyTime _ _ _ _ h

end BQPProgram
