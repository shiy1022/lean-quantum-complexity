import ReversibleCounterTM2

set_option autoImplicit false
namespace ShiReversibleGenerator

inductive NormalizeLabel where
  | scan | consume | print | stop
  deriving DecidableEq

instance : Fintype NormalizeLabel where
  elems := {.scan, .consume, .print, .stop}
  complete := by intro l; cases l <;> simp

def normalizeCode : NormalizeLabel → CounterInstr Unit NormalizeLabel
  | .scan => .branch () .stop .consume
  | .consume => .dec () .print
  | .print => .emit true .scan
  | .stop => .halt

def normalizeState (pc : Option NormalizeLabel) (n : Nat) (ys : List Bool) : CounterCfg Unit NormalizeLabel :=
  ⟨pc, fun _ => n, ys⟩

@[simp] theorem unit_update (n m : Nat) :
    Function.update (fun _ : Unit => n) () m = (fun _ : Unit => m) := by
  funext u
  cases u
  simp

/-- Three instructions per input symbol and two instructions to detect the end and halt. -/
theorem normalize_run (n : Nat) (ys : List Bool) :
    CounterRun normalizeCode (normalizeState (some .scan) n ys) (3 * n + 2)
      (normalizeState none 0 (List.replicate n true ++ ys)) := by
  induction n generalizing ys with
  | zero =>
    apply CounterRun.next (code := normalizeCode) (l := .scan) rfl
    simp only [normalizeCode, CounterInstr.eval, normalizeState, if_pos rfl,
      Nat.mul_zero, Nat.zero_add, List.replicate_zero, List.nil_append]
    exact CounterRun.next (code := normalizeCode) (l := .stop) rfl (CounterRun.refl _)
  | succ n ih =>
    have hr := ih (true :: ys)
    have h₁ := CounterRun.next (code := normalizeCode) (l := NormalizeLabel.print) (s := normalizeState (some .print) n ys) rfl
      (by simpa [normalizeCode, CounterInstr.eval, normalizeState] using hr)
    have h₂ := CounterRun.next (code := normalizeCode) (l := NormalizeLabel.consume) (s := normalizeState (some .consume) (n + 1) ys) rfl
      (by simpa [normalizeCode, CounterInstr.eval, normalizeState] using h₁)
    have h₃ := CounterRun.next (code := normalizeCode) (l := NormalizeLabel.scan) (s := normalizeState (some .scan) (n + 1) ys) rfl
      (by simpa [normalizeCode, CounterInstr.eval, normalizeState] using h₂)
    simpa [normalizeState, List.replicate_succ', List.append_assoc, Nat.mul_add, Nat.add_assoc] using h₃

theorem unaryLength_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun xs => List.replicate xs.length true)) := by
  apply counterProgram_polytime normalizeCode () .scan _ (Polynomial.C 3 * Polynomial.X + Polynomial.C 2)
  intro xs
  refine ⟨3 * xs.length + 2, normalizeState none 0 (List.replicate xs.length true), ?_, rfl, ?_, rfl, ?_⟩
  · simpa [normalizeState] using normalize_run xs.length []
  · intro r; rfl
  · simp

end ShiReversibleGenerator
