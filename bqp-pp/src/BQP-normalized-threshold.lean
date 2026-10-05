import «BQP-counting-normalization»
import «BQP-counting-threshold»

set_option autoImplicit false
namespace BQPCounting
open ShiClassPP

/-- Positive witness length is obtained by the concrete prefix wrapper, rather
than assumed of the original circuit or residue relation. -/
theorem normalized_long_majority (L : Language Bool) (hh : List Bool → ℕ)
    (Rc : ℕ → List Bool × List Bool → Bool) (p : List Bool → ℝ)
    (r : Polynomial ℕ) (hr : ∀ x, hh x ≤ r.eval x.length)
    (hp : ∀ x, 2 ≤ x.length → p x = (1 / 2 : ℝ) ^ hh x *
      ((coefficient hh Rc 0 4 x : ℝ) + (coefficient hh Rc 1 3 x : ℝ) * Real.sqrt 2))
    (hyes : ∀ x, x ∈ L → (2 : ℝ) / 3 ≤ p x)
    (hno : ∀ x, x ∉ L → p x ≤ (1 : ℝ) / 3) :
    ∃ k : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      (x ∈ L ↔ 2 * countAccept
        (combinedChecker (fun x => hh x + 1) (fun d => pairedPrefix (Rc d)))
        x (x.length ^ k) > 2 ^ (x.length ^ k)) := by
  apply long_majority L (fun x => hh x + 1) (fun d => pairedPrefix (Rc d)) p r
    (fun x => Nat.add_le_add_right (hr x) 1) (fun _ _ => by omega) _ hyes hno
  intro x hx
  rw [hp x hx]
  simpa only [coefficient, Int.cast_sub, Int.cast_natCast, mul_comm] using
    (pairedPrefix_representation Rc x (hh x)).symm

/-- The shifted witness budget is supplied by the actual well-formed,
polynomially bounded family in the definition of BQP. -/
theorem family_shifted_budget (F : ShiClass.Family) (hwf : ShiBQP.WellFormed F)
    (hpoly : ShiBQP.PolyBounded F) :
    ∃ k : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      3 * ((F.circ x.length).flatten.countP
        (fun g => match g with | ShiShallow.Instr.h _ => true | _ => false) + 1) + 7 ≤
          x.length ^ k := by
  obtain ⟨k, hk⟩ := BQPChecked.reference11.2.2.2.2.2.2 F hwf hpoly
  refine ⟨k, fun x hx => ?_⟩
  have h := hk x.length hx
  let c := (F.circ x.length).flatten.countP
    (fun g => match g with | ShiShallow.Instr.h _ => true | _ => false)
  change 3 * (c + 1) + 7 ≤ x.length ^ k
  calc
    3 * (c + 1) + 7 = 3 * c + 10 := by omega
    _ ≤ x.length ^ k := by
      convert h using 1
      congr 2
      dsimp only [c]
      congr 1
      funext g
      cases g <;> rfl

end BQPCounting
