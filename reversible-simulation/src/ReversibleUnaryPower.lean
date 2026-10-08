import ReversibleCounterMultiply
import ReversibleCounterTM2

set_option autoImplicit false
namespace ShiReversibleGenerator

abbrev PowerLabel (d : Nat) := Unit ⊕ ((Fin d × Fin 12) ⊕ Fin 6)
def powerStage {d : Nat} (i : Fin d) (j : Fin 12) : PowerLabel d := .inr (.inl (i, j))
def powerTail {d : Nat} (j : Fin 6) : PowerLabel d := .inr (.inr j)
def powerFrom (d i : Nat) : PowerLabel d :=
  if h : i < d then powerStage ⟨i, h⟩ 0 else powerTail 0

def powerCode (d : Nat) : PowerLabel d → CounterInstr (Fin 4) (PowerLabel d)
  | .inl _ => .inc 0 (powerFrom d 0)
  | .inr (.inl (i, j)) =>
    match j.val with
    | 0 => .branch 0 (powerStage i 9) (powerStage i 1)
    | 1 => .dec 0 (powerStage i 2)
    | 2 => .branch 1 (powerStage i 6) (powerStage i 3)
    | 3 => .dec 1 (powerStage i 4)
    | 4 => .inc 2 (powerStage i 5)
    | 5 => .inc 3 (powerStage i 2)
    | 6 => .branch 3 (powerStage i 0) (powerStage i 7)
    | 7 => .dec 3 (powerStage i 8)
    | 8 => .inc 1 (powerStage i 6)
    | 9 => .branch 2 (powerFrom d (i.val + 1)) (powerStage i 10)
    | 10 => .dec 2 (powerStage i 11)
    | _ => .inc 0 (powerStage i 9)
  | .inr (.inr j) =>
    match j.val with
    | 0 => .branch 1 (powerTail 2) (powerTail 1)
    | 1 => .dec 1 (powerTail 0)
    | 2 => .branch 0 (powerTail 5) (powerTail 3)
    | 3 => .dec 0 (powerTail 4)
    | 4 => .emit true (powerTail 2)
    | _ => .halt

def powerState {d : Nat} (pc : PowerLabel d) (r q a t : Nat) (ys : List Bool) :
    CounterCfg (Fin 4) (PowerLabel d) :=
  ⟨some pc, fun i => match i.val with | 0 => r | 1 => q | 2 => a | _ => t, ys⟩

@[simp] theorem powerState_inc {d : Nat} (p pc : PowerLabel d)
    (r q a t : Nat) (ys : List Bool) :
    (CounterInstr.inc (0 : Fin 4) pc).eval (powerState p r q a t ys) =
      powerState pc (r + 1) q a t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [CounterInstr.eval, powerState]
  · rfl

@[simp] theorem powerState_multiply {d : Nat} (p pc : PowerLabel d)
    (r q a t k n m : Nat) (ys : List Bool) :
    multiplyState (powerState p r q a t ys) 0 1 2 3 k n m pc = powerState pc k n m 0 ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [multiplyState, copyState, withCounter, powerState]
  · rfl

@[simp] theorem powerState_transfer {d : Nat} (p pc : PowerLabel d)
    (r q a t k m : Nat) (ys : List Bool) :
    transferState (powerState p r q a t ys) 2 0 k m pc = powerState pc m q k t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [transferState, powerState]
  · rfl

@[simp] theorem powerState_clear {d : Nat} (p pc : PowerLabel d)
    (r q a t n : Nat) (ys : List Bool) :
    withCounter (powerState p r q a t ys) 1 n pc = powerState pc r n a t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [withCounter, powerState]
  · rfl

@[simp] theorem powerState_print {d : Nat} (p pc : PowerLabel d)
    (r q a t n : Nat) (xs ys : List Bool) :
    printState (powerState p r q a t xs) 0 n ys pc = powerState pc n q a t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [printState, powerState]
  · rfl

/-- One finite exponentiation block multiplies and transfers the result back. -/
theorem power_stage_run (d : Nat) (i : Fin d) (a n : Nat) (ys : List Bool) :
    CounterRun (powerCode d) (powerState (powerStage i 0) a n 0 0 ys)
      (a * (10 * n + 4) + 2) (powerState (powerFrom d (i.val + 1)) (a * n) n 0 0 ys) := by
  let base := powerState (powerStage i 0) 0 0 0 0 ys
  have hm := multiply_counter_run (powerCode d) (0 : Fin 4) 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (powerStage i 0) (powerStage i 1) (powerStage i 2) (powerStage i 3)
    (powerStage i 4) (powerStage i 5) (powerStage i 6) (powerStage i 7)
    (powerStage i 8) (powerStage i 9) rfl rfl rfl rfl rfl rfl rfl rfl rfl base a n 0
  simp only [base, powerState_multiply, Nat.zero_add] at hm
  have ht := transfer_counter_run (powerCode d) (2 : Fin 4) 0 (by decide)
    (powerStage i 9) (powerStage i 10) (powerStage i 11) (powerFrom d (i.val + 1))
    rfl rfl rfl (powerState (powerStage i 9) 0 n 0 0 ys) (a * n) 0
  simp only [powerState_transfer, Nat.zero_add] at ht
  have h := CounterRun.trans (powerCode d) hm ht
  convert h using 1 <;> ring

def powerWork (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 10 * n + 4 + n * powerWork n k

noncomputable def powerWorkPolynomial : Nat → Polynomial Nat
  | 0 => 0
  | k + 1 => Polynomial.C 10 * Polynomial.X + Polynomial.C 4 +
      Polynomial.X * powerWorkPolynomial k

@[simp] theorem powerWorkPolynomial_eval (k n : Nat) :
    (powerWorkPolynomial k).eval n = powerWork n k := by
  induction k with
  | zero => simp [powerWorkPolynomial, powerWork]
  | succ k ih => simp [powerWorkPolynomial, powerWork, ih]

/-- A suffix of the finite block chain computes the corresponding power. -/
theorem power_span_run (d k i a n : Nat) (hi : i + k ≤ d) (ys : List Bool) :
    CounterRun (powerCode d) (powerState (powerFrom d i) a n 0 0 ys)
      (a * powerWork n k + 2 * k) (powerState (powerFrom d (i + k)) (a * n ^ k) n 0 0 ys) := by
  induction k generalizing i a with
  | zero => simpa [powerWork] using CounterRun.refl (powerState (powerFrom d i) a n 0 0 ys)
  | succ k ih =>
    have hil : i < d := by omega
    have hf : powerFrom d i = powerStage ⟨i, hil⟩ 0 := dif_pos hil
    have hs := power_stage_run d ⟨i, hil⟩ a n ys
    have hr := ih (i + 1) (a * n) (by omega)
    have h := CounterRun.trans (powerCode d) hs hr
    rw [hf]
    have hid : i + (k + 1) = i + 1 + k := by omega
    rw [hid]
    convert h using 1 <;> simp [powerWork, pow_succ] <;> ring

/-- The finite program computes unary n^d and clears every counter. -/
theorem power_run (d n : Nat) :
    CounterRun (powerCode d) (powerState (.inl ()) 0 n 0 0 [])
      (powerWork n d + 2 * d + 2 * n + 3 * n ^ d + 4)
      ⟨none, fun _ => 0, List.replicate (n ^ d) true⟩ := by
  have hspan := power_span_run d d 0 1 n (by omega) []
  simp only [Nat.zero_add, Nat.one_mul] at hspan
  have hend : powerFrom d d = powerTail 0 := dif_neg (Nat.lt_irrefl d)
  rw [hend] at hspan
  have hstart := CounterRun.next (code := powerCode d) (l := .inl ())
    (s := powerState (.inl ()) 0 n 0 0 []) rfl
    (by simpa only [powerCode, powerState_inc, Nat.zero_add] using hspan)
  have hc := clear_counter_run (powerCode d) (1 : Fin 4) (powerTail 0) (powerTail 1) (powerTail 2)
    rfl rfl (powerState (powerTail 0) (n ^ d) n 0 0 []) n
  simp only [powerState_clear] at hc
  have hp := emit_counter_run (powerCode d) (0 : Fin 4) (powerTail 2) (powerTail 3) (powerTail 4)
    (powerTail 5) true rfl rfl rfl (powerState (powerTail 2) (n ^ d) 0 0 0 []) (n ^ d) []
  simp only [powerState_print, List.append_nil] at hp
  have hh : CounterRun (powerCode d) (powerState (powerTail 5) 0 0 0 0 (List.replicate (n ^ d) true)) 1
      ⟨none, fun _ => 0, List.replicate (n ^ d) true⟩ := by
    have h := CounterRun.one (powerCode d) (powerState (powerTail 5) 0 0 0 0 (List.replicate (n ^ d) true))
      (powerTail 5) rfl
    convert h using 1
    apply CounterCfg.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have h₁ := CounterRun.trans (powerCode d) hstart hc
  have h₂ := CounterRun.trans (powerCode d) h₁ hp
  have h₃ := CounterRun.trans (powerCode d) h₂ hh
  convert h₃ using 1 <;> omega

/-- Arbitrary fixed exponents have genuine polynomial-time unary printing machines. -/
theorem unaryPower_polytime (d : Nat) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => List.replicate (xs.length ^ d) true)) := by
  apply counterProgram_polytime (powerCode d) (1 : Fin 4) (.inl ()) _
    (powerWorkPolynomial d + Polynomial.C (2 * d) + Polynomial.C 2 * Polynomial.X +
      Polynomial.C 3 * Polynomial.X ^ d + Polynomial.C 4)
  intro xs
  refine ⟨powerWork xs.length d + 2 * d + 2 * xs.length + 3 * xs.length ^ d + 4,
    ⟨none, fun _ => 0, List.replicate (xs.length ^ d) true⟩, ?_, rfl, fun _ => rfl, rfl, ?_⟩
  · have h := power_run d xs.length
    convert h using 1
    apply CounterCfg.ext
    · rfl
    · funext i; fin_cases i <;> simp [powerState]
    · rfl
  · simp

end ShiReversibleGenerator
