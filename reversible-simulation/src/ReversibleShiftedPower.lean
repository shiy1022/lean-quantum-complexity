import ReversibleUnaryPower
import ReversibleCounterRelabel

set_option autoImplicit false
namespace ShiReversibleGenerator

abbrev ShiftLabel (c d : Nat) := Fin c ⊕ PowerLabel d

def shiftFrom (c d i : Nat) : ShiftLabel c d :=
  if h : i < c then .inl ⟨i, h⟩ else .inr (.inl ())

def shiftCode (c d : Nat) : ShiftLabel c d → CounterInstr (Fin 4) (ShiftLabel c d)
  | .inl i => .inc 1 (shiftFrom c d (i.val + 1))
  | .inr l => (powerCode d l).relabel Sum.inr

def shiftState {c d : Nat} (pc : ShiftLabel c d) (n : Nat) : CounterCfg (Fin 4) (ShiftLabel c d) :=
  ⟨some pc, Function.update (fun _ => 0) 1 n, []⟩

/-- The constant shift is implemented by a finite chain of actual increments. -/
theorem shift_prefix_run (c d k i n : Nat) (hi : i + k = c) :
    CounterRun (shiftCode c d) (shiftState (shiftFrom c d i) n) k
      (shiftState (.inr (.inl ())) (n + k)) := by
  induction k generalizing i n with
  | zero =>
    have he : i = c := by omega
    subst i
    simpa [shiftFrom] using CounterRun.refl (shiftState (.inr (.inl ()) : ShiftLabel c d) n)
  | succ k ih =>
    have hil : i < c := by omega
    have hf : shiftFrom c d i = .inl ⟨i, hil⟩ := dif_pos hil
    rw [hf]
    apply CounterRun.next (code := shiftCode c d) (l := .inl ⟨i, hil⟩) rfl
    simpa [shiftCode, CounterInstr.eval, shiftState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (i + 1) (n + 1) (by omega)

/-- Constant shifting and the power machine are one finite program, with exact total execution. -/
theorem shifted_power_run (c d n : Nat) :
    CounterRun (shiftCode c d) (shiftState (shiftFrom c d 0) n)
      (c + (powerWork (n + c) d + 2 * d + 2 * (n + c) + 3 * (n + c) ^ d + 4))
      ⟨none, fun _ => 0, List.replicate ((n + c) ^ d) true⟩ := by
  have hs := shift_prefix_run c d c 0 n (by omega)
  have hp := CounterRun.relabel (powerCode d) (shiftCode c d) Sum.inr
    (fun _ => rfl) (power_run d (n + c))
  have he : (powerState (.inl ()) 0 (n + c) 0 0 []).relabel (Sum.inr : PowerLabel d → ShiftLabel c d) =
      shiftState (.inr (.inl ())) (n + c) := by
    apply CounterCfg.ext
    · rfl
    · funext i; fin_cases i <;> simp [CounterCfg.relabel, powerState, shiftState]
    · rfl
  rw [he] at hp
  exact CounterRun.trans (shiftCode c d) hs hp

noncomputable def powerTotalPolynomial (d : Nat) : Polynomial Nat :=
  powerWorkPolynomial d + Polynomial.C (2 * d) + Polynomial.C 2 * Polynomial.X +
    Polynomial.C 3 * Polynomial.X ^ d + Polynomial.C 4

@[simp] theorem powerTotalPolynomial_eval (d n : Nat) :
    (powerTotalPolynomial d).eval n = powerWork n d + 2 * d + 2 * n + 3 * n ^ d + 4 := by
  simp [powerTotalPolynomial]

/-- A genuine polynomial-time printing machine for the shifted-power runtime budgets. -/
theorem shiftedUnaryPower_polytime (c d : Nat) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => List.replicate ((xs.length + c) ^ d) true)) := by
  apply counterProgram_polytime (shiftCode c d) (1 : Fin 4) (shiftFrom c d 0) _
    (Polynomial.C c + (powerTotalPolynomial d).comp (Polynomial.X + Polynomial.C c))
  intro xs
  refine ⟨c + (powerWork (xs.length + c) d + 2 * d + 2 * (xs.length + c) + 3 * (xs.length + c) ^ d + 4),
    ⟨none, fun _ => 0, List.replicate ((xs.length + c) ^ d) true⟩,
    shifted_power_run c d xs.length, rfl, fun _ => rfl, rfl, ?_⟩
  simp [Polynomial.eval_comp]

end ShiReversibleGenerator
