import «BQP-counting-core»

set_option autoImplicit false
namespace BQPCounting

def suffixValue (s : List Bool) : ℕ := s.foldr (fun b r => (bif b then 1 else 0) + 2*r) 0

theorem suffixValue_append (s t : List Bool) :
    suffixValue (s++t) = suffixValue s + 2^s.length * suffixValue t := by
  induction s with
  | nil => simp [suffixValue]
  | cons b s ih =>
      simp only [List.cons_append, suffixValue, List.foldr_cons, List.length_cons] at *
      rw [ih, pow_succ]
      ring

theorem suffixValue_split (s : List Bool) (k : ℕ) :
    suffixValue s = suffixValue (s.take k) + 2^(s.take k).length * suffixValue (s.drop k) := by
  rw [← suffixValue_append, List.take_append_drop]

theorem suffixValue_overflow (s : List Bool) (k : ℕ) (hk : k ≤ s.length)
    (ht : 0 < suffixValue (s.drop k)) : 2^k ≤ suffixValue s := by
  rw [suffixValue_split s k, List.length_take, Nat.min_eq_left hk]
  have hm := Nat.mul_le_mul_left (2^k) (show 1 ≤ suffixValue (s.drop k) from ht)
  simp only [Nat.mul_one] at hm
  omega

/-- High suffix bits must be inspected: overflow selects the balanced tail,
not rejection and not comparison modulo the chosen threshold width. -/
theorem combinedChecker_overflow (hh : List Bool → ℕ)
    (Rc : ℕ → List Bool × List Bool → Bool) (x w : List Bool)
    (hover : 2^(hh x+7) ≤ suffixValue (w.drop (2*hh x))) :
    combinedChecker hh Rc (x,w) = (w.take (2*hh x)).headI := by
  have hfit := (BQPChecked.reference10 gap_suffix gap_complement gap_first_bit).1 (hh x)
  have h0 : ¬ suffixValue (w.drop (2*hh x)) < 2^(hh x+4) := by omega
  have h1 : ¬ suffixValue (w.drop (2*hh x)) < 2*2^(hh x+4) := by omega
  have h2 : ¬ suffixValue (w.drop (2*hh x)) <
      2*2^(hh x+4)+2*Nat.sqrt (2*4^(hh x+3)) := by omega
  have h3 : ¬ suffixValue (w.drop (2*hh x)) <
      2*2^(hh x+4)+4*Nat.sqrt (2*4^(hh x+3)) := by omega
  have h4 : ¬ suffixValue (w.drop (2*hh x)) <
      2*2^(hh x+4)+4*Nat.sqrt (2*4^(hh x+3))+16 := by omega
  simp only [suffixValue] at h0 h1 h2 h3 h4
  simp only [combinedChecker, h0,h1,h2,h3,h4, ↓reduceIte]

/-- Zero high bits may be dropped without changing a comparison's value. -/
theorem suffixValue_trim (s : List Bool) (k : ℕ) (hz : suffixValue (s.drop k) = 0) :
    suffixValue s = suffixValue (s.take k) := by
  rw [suffixValue_split s k, hz, Nat.mul_zero, Nat.add_zero]

end BQPCounting
