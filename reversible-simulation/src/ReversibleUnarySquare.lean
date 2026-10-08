import ReversibleCounterMultiply
import ReversibleCounterTM2

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A fully finite program: copy input length, multiply, clear, print and halt. -/
def squareCode (l : Fin 22) : CounterInstr (Fin 4) (Fin 22) :=
  match l.val with
  | 0 => .branch 0 4 1
  | 1 => .dec 0 2
  | 2 => .inc 1 3
  | 3 => .inc 3 0
  | 4 => .branch 3 7 5
  | 5 => .dec 3 6
  | 6 => .inc 0 4
  | 7 => .branch 0 16 8
  | 8 => .dec 0 9
  | 9 => .branch 1 13 10
  | 10 => .dec 1 11
  | 11 => .inc 2 12
  | 12 => .inc 3 9
  | 13 => .branch 3 7 14
  | 14 => .dec 3 15
  | 15 => .inc 1 13
  | 16 => .branch 1 18 17
  | 17 => .dec 1 16
  | 18 => .branch 2 21 19
  | 19 => .dec 2 20
  | 20 => .emit true 18
  | _ => .halt

def squareState (pc : Fin 22) (r q d t : Nat) (ys : List Bool) : CounterCfg (Fin 4) (Fin 22) :=
  ⟨some pc, fun i => match i.val with | 0 => r | 1 => q | 2 => d | _ => t, ys⟩

@[simp] theorem squareState_copy (p pc : Fin 22) (r q d t n m z : Nat) (ys : List Bool) :
    copyState (squareState p r q d t ys) 0 1 3 n m z pc = squareState pc n m d z ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [copyState, squareState]
  · rfl

@[simp] theorem squareState_multiply (p pc : Fin 22) (r q d t k n m : Nat) (ys : List Bool) :
    multiplyState (squareState p r q d t ys) 0 1 2 3 k n m pc = squareState pc k n m 0 ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [multiplyState, copyState, withCounter, squareState]
  · rfl

@[simp] theorem squareState_clear (p pc : Fin 22) (r q d t n : Nat) (ys : List Bool) :
    withCounter (squareState p r q d t ys) 1 n pc = squareState pc r n d t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [withCounter, squareState]
  · rfl

@[simp] theorem squareState_print (p pc : Fin 22) (r q d t n : Nat) (xs ys : List Bool) :
    printState (squareState p r q d t xs) 2 n ys pc = squareState pc r q n t ys := by
  apply CounterCfg.ext
  · rfl
  · funext i; fin_cases i <;> simp [printState, squareState]
  · rfl

/-- The concrete program's exact source execution, with every counter cleared. -/
theorem square_run (n : Nat) :
    CounterRun squareCode (squareState 0 n 0 0 0 []) (10 * (n * n) + 13 * n + 6)
      ⟨none, fun _ => 0, List.replicate (n * n) true⟩ := by
  let base := squareState 0 0 0 0 0 []
  have hcopy := copy_counter_run squareCode (0 : Fin 4) 1 3 (by decide) (by decide) (by decide)
    0 1 2 3 4 5 6 7 rfl rfl rfl rfl rfl rfl rfl base n 0
  simp only [base, squareState_copy, Nat.zero_add] at hcopy
  have hmul := multiply_counter_run squareCode (0 : Fin 4) 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    7 8 9 10 11 12 13 14 15 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl base n n 0
  simp only [base, squareState_multiply, Nat.zero_add] at hmul
  have hclear := clear_counter_run squareCode (1 : Fin 4) 16 17 18 rfl rfl
    (squareState 16 0 n (n * n) 0 []) n
  simp only [squareState_clear] at hclear
  have hprint := emit_counter_run squareCode (2 : Fin 4) 18 19 20 21 true rfl rfl rfl
    (squareState 18 0 0 (n * n) 0 []) (n * n) []
  simp only [squareState_print, List.append_nil] at hprint
  have hh : CounterRun squareCode (squareState 21 0 0 0 0 (List.replicate (n * n) true)) 1
      ⟨none, fun _ => 0, List.replicate (n * n) true⟩ := by
    have h := CounterRun.one squareCode (squareState 21 0 0 0 0 (List.replicate (n * n) true)) 21 rfl
    convert h using 1
    apply CounterCfg.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have h₁ := CounterRun.trans squareCode hcopy hmul
  have h₂ := CounterRun.trans squareCode h₁ hclear
  have h₃ := CounterRun.trans squareCode h₂ hprint
  have h₄ := CounterRun.trans squareCode h₃ hh
  convert h₄ using 1 <;> ring

/-- Squaring unary lengths is certified by a real finite TM2 with a quadratic clock. -/
theorem unarySquare_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => List.replicate (xs.length * xs.length) true)) := by
  apply counterProgram_polytime squareCode (0 : Fin 4) 0 _
    (Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 13 * Polynomial.X + Polynomial.C 6)
  intro xs
  refine ⟨10 * (xs.length * xs.length) + 13 * xs.length + 6,
    ⟨none, fun _ => 0, List.replicate (xs.length * xs.length) true⟩, ?_, rfl, fun _ => rfl, rfl, ?_⟩
  · have h := square_run xs.length
    convert h using 1
    apply CounterCfg.ext
    · rfl
    · funext i; fin_cases i <;> simp [squareState]
    · rfl
  · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, pow_two]

end ShiReversibleGenerator
