import «BQP-binary-add»
import «BQP-router-square-root»
import «BQP-router-overflow»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open BQPBinaryAdd

theorem bits_length (k n : ℕ) : (bits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bits, ih]

theorem bits_value (k n : ℕ) (hn : n < 2^k) : value (bits k n) = n := by
  induction k generalizing n with
  | zero =>
      simp only [pow_zero] at hn
      have hz : n = 0 := by omega
      subst n
      rfl
  | succ k ih =>
      have hq : n/2 < 2^k := by
        rw [pow_succ] at hn
        omega
      simp only [bits, value, ih _ hq, beq_iff_eq]
      have hm : n%2 < 2 := Nat.mod_lt _ (by decide)
      split_ifs <;> omega

def shift (k : ℕ) (s : List Bool) : List Bool := List.replicate k false ++ s

theorem shift_value (k : ℕ) (s : List Bool) : value (shift k s) = 2^k * value s := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
      simp only [shift, List.replicate_succ, List.cons_append, value, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add] at *
      rw [ih, pow_succ]
      ring

@[simp] theorem shift_length (k : ℕ) (s : List Bool) : (shift k s).length = k+s.length := by
  simp [shift]

def power (k : ℕ) : List Bool := shift k [true]

theorem power_value (k : ℕ) : value (power k) = 2^k := by
  simp [power, shift_value, value]

/-- Actual binary strings for all five router boundaries. Leading high zeroes
are harmless because the comparator processes arbitrary widths exactly. -/
def thresholds (h : ℕ) : Fin 5 → List Bool
  | 0 => power (h+4)
  | 1 => power (h+5)
  | 2 => add (power (h+5)) (shift 1 (bits (h+7) (Nat.sqrt (2*4^(h+3))))) false
  | 3 => add (power (h+5)) (shift 2 (bits (h+7) (Nat.sqrt (2*4^(h+3))))) false
  | _ => add (add (power (h+5)) (shift 2 (bits (h+7) (Nat.sqrt (2*4^(h+3))))) false)
      (power 4) false

theorem sqrt_fits (h : ℕ) : Nat.sqrt (2*4^(h+3)) < 2^(h+7) := by
  have hf := (BQPChecked.reference10 BQPCounting.gap_suffix BQPCounting.gap_complement
    BQPCounting.gap_first_bit).1 h
  omega

theorem thresholds_value (h : ℕ) (i : Fin 5) :
    value (thresholds h i) =
      (![2^(h+4), 2*2^(h+4),
        2*2^(h+4)+2*Nat.sqrt (2*4^(h+3)),
        2*2^(h+4)+4*Nat.sqrt (2*4^(h+3)),
        2*2^(h+4)+4*Nat.sqrt (2*4^(h+3))+16] : Fin 5 → ℕ) i := by
  have hb := bits_value (h+7) _ (sqrt_fits h)
  have hp : 2^(h+5) = 2*2^(h+4) := by
    rw [show h+5 = (h+4)+1 by omega, pow_succ, Nat.mul_comm]
  fin_cases i <;> simp [thresholds, add_correct, power_value, shift_value, hb, hp]

theorem thresholds_length (h : ℕ) (i : Fin 5) : (thresholds h i).length ≤ h+11 := by
  fin_cases i <;> simp [thresholds, add_length, power, shift_length, bits_length] <;> omega

theorem value_eq_suffixValue (s : List Bool) : value s = BQPCounting.suffixValue s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp_all [value, BQPCounting.suffixValue]

end BQPRouterArithmetic
