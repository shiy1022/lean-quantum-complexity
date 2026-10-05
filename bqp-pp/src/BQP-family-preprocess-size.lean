import «BQP-program-size»
import «BQP-prefix-integration»

set_option autoImplicit false
namespace BQPProgram
open Polynomial

/-- The all-gates instance of the proved predicate-count bound. -/
theorem family_gate_count_bound (F : ShiClass.Family) (hwf : ShiBQP.WellFormed F)
    (q : Polynomial ℕ)
    (hd : ∀ n, ShiShallow.depth (F.circ n) ≤ q.eval n)
    (ha : ∀ n, F.anc n ≤ q.eval n) (n : ℕ) :
    (F.circ n).flatten.length ≤ (q * (X + q + 1)).eval n := by
  have h := BQPChecked.reference11.2.2.1 F hwf q hd ha (fun _ _ => true) n
  simpa using h

/-- Includes the circuit's extra output wire and the compiler's additional unit. -/
noncomputable def familyProgramBudget (q : Polynomial ℕ) : Polynomial ℕ :=
  C 64 * (X + q + C 2) * (q * (X + q + 1) + 1)

theorem family_encoded_length_bound (checkerData : Checker) (F : ShiClass.Family)
    (hwf : ShiBQP.WellFormed F) (q : Polynomial ℕ)
    (hd : ∀ n, ShiShallow.depth (F.circ n) ≤ q.eval n)
    (ha : ∀ n, F.anc n ≤ q.eval n) (x : List Bool) :
    (checkerData.encode (familyProgram F x)).length ≤ (familyProgramBudget q).eval x.length := by
  have hg := family_gate_count_bound F hwf q hd ha x.length
  have han := ha x.length
  have hb := encoded_compile_length checkerData (F.circ x.length).flatten
    (ShiBQP.toBits x) (F.out x.length)
  change (checkerData.encode (familyProgram F x)).length ≤
    64 * (x.length + (F.anc x.length + 1) + 1) * ((F.circ x.length).flatten.length + 1) at hb
  apply hb.trans
  simp only [familyProgramBudget, eval_mul, eval_add, eval_C, eval_X, eval_one] at hg ⊢
  apply Nat.mul_le_mul
  · omega
  · omega

theorem family_encoded_polyBound (checkerData : Checker) (F : ShiClass.Family)
    (hwf : ShiBQP.WellFormed F) (hpoly : ShiBQP.PolyBounded F) :
    ∃ P : Polynomial ℕ, ∀ x : List Bool,
      (checkerData.encode (familyProgram F x)).length ≤ P.eval x.length := by
  obtain ⟨q, hd, ha⟩ := hpoly
  exact ⟨familyProgramBudget q, family_encoded_length_bound checkerData F hwf q hd ha⟩

theorem familyPreprocess_length (checkerData : Checker) (F : ShiClass.Family)
    (x w : List Bool) :
    (PvsNP.encodePair (familyPreprocess checkerData F (x,w))).length =
      (checkerData.encode (familyProgram F x)).length + w.length := by
  simp [familyPreprocess, PvsNP.encodePair]

/-- A bound in the full tagged input length, suitable for machine composition.
This proves output size, not a machine execution bound. -/
theorem familyPreprocess_polyBound (checkerData : Checker) (F : ShiClass.Family)
    (hwf : ShiBQP.WellFormed F) (hpoly : ShiBQP.PolyBounded F) :
    ∃ Q : Polynomial ℕ, ∀ p : List Bool × List Bool,
      (PvsNP.encodePair (familyPreprocess checkerData F p)).length ≤
        Q.eval (PvsNP.encodePair p).length := by
  obtain ⟨P, hP⟩ := family_encoded_polyBound checkerData F hwf hpoly
  refine ⟨P + X, ?_⟩
  rintro ⟨x,w⟩
  rw [familyPreprocess_length]
  have hm := BQPPrefixMachine.eval_mono P (Nat.le_add_right x.length w.length)
  have hp := hP x
  simp only [PvsNP.encodePair, List.length_append, List.length_map,
    eval_add, eval_X]
  omega

end BQPProgram
