import ReversibleCopyFragment
import ReversibleBudgetFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- The standard unary natural-number code, terminated by false. -/
def printedNat (n : Nat) : List Bool := List.replicate n true ++ [false]

abbrev NatEmissionLabel (L : Type) := Fin 7 ⊕ (Fin 4 ⊕ L)

def natEmissionCode (code : L → CounterInstr R L) (r buf tmp : R) (stop : L) :
    NatEmissionLabel L → CounterInstr R (NatEmissionLabel L)
  | .inl j => copyBlock r buf tmp Sum.inl (.inr (.inl 0)) j
  | .inr (.inl j) =>
    match j.val with
    | 0 => .emit false (.inr (.inl 1))
    | 1 => .branch buf (.inr (.inr stop)) (.inr (.inl 2))
    | 2 => .dec buf (.inr (.inl 3))
    | _ => .emit true (.inr (.inl 1))
  | .inr (.inr l) => (code l).relabel (fun l => .inr (.inr l))

def natEmissionState (base : CounterCfg R L) (r buf tmp : R) (n m : Nat) (ys : List Bool) (pc : L) :
    CounterCfg R L := copyState {base with output := ys} r buf tmp n m 0 pc

@[simp] theorem printState_natEmission (base : CounterCfg R L) (r buf tmp : R) (hbt : buf ≠ tmp)
    (n m v : Nat) (xs ys : List Bool) (p pc : L) :
    printState (natEmissionState base r buf tmp n m xs p) buf v ys pc =
      natEmissionState base r buf tmp n v ys pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hb : j = buf
    · subst j; simp [printState, natEmissionState, copyState, hbt]
    · by_cases ht : j = tmp
      · subst j; simp [printState, natEmissionState, copyState, Ne.symm hbt]
      · simp [printState, natEmissionState, copyState, hb, ht]
  · rfl

/-- Exact nonconsuming natural-number serialization by actual finite instructions.
Both scratch counters are zero on return and every other register is preserved. -/
theorem natEmissionCode_run (code : L → CounterInstr R L) (r buf tmp : R) (stop : L)
    (hrb : r ≠ buf) (hrt : r ≠ tmp) (hbt : buf ≠ tmp)
    (base : CounterCfg R (NatEmissionLabel L)) (n : Nat) :
    CounterRun (natEmissionCode code r buf tmp stop)
      (natEmissionState base r buf tmp n 0 base.output (.inl 0)) (10 * n + 4)
      (natEmissionState base r buf tmp n 0 (printedNat n ++ base.output) (.inr (.inr stop))) := by
  let prg := natEmissionCode code r buf tmp stop
  have hc := copy_block_run prg r buf tmp hrb hrt hbt Sum.inl (.inr (.inl 0))
    (fun _ => rfl) {base with output := base.output} n 0
  simp only [Nat.zero_add] at hc
  have he : CounterRun prg
      (natEmissionState base r buf tmp n n base.output (.inr (.inl 0))) 1
      (natEmissionState base r buf tmp n n (false :: base.output) (.inr (.inl 1))) := by
    exact CounterRun.one prg _ (.inr (.inl 0)) rfl
  have hp := emit_counter_run prg buf (.inr (.inl 1)) (.inr (.inl 2)) (.inr (.inl 3))
    (.inr (.inr stop)) true rfl rfl rfl
    (natEmissionState base r buf tmp n 0 [] (.inr (.inl 1))) n (false :: base.output)
  simp only [printState_natEmission base r buf tmp hbt] at hp
  have h₁ := CounterRun.trans prg hc he
  have h₂ := CounterRun.trans prg h₁ hp
  convert h₂ using 1 <;> (try simp [printedNat, natEmissionState, List.append_assoc]) <;> first | rfl | omega

theorem natEmissionCode_clock_polynomial (size : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n, 10 * size.eval n + 4 = p.eval n := by
  refine ⟨Polynomial.C 10 * size + Polynomial.C 4, ?_⟩
  intro n
  simp

end ShiReversibleGenerator
