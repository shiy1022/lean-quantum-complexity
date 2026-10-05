import «AMPUNI-retained-finite»
import «AMPUNI-fanout-machine»
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMBooleanIO
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev K := TopK ⊕ Bool
abbrev Gam : K → Type
  | .inl k => TopGam k
  | .inr _ => Bool
abbrev input : K := .inr false
abbrev output : K := .inr true
abbrev source : K := .inl (.inl (.inl (11 : Fin 14)))
abbrev scratch : K := .inl (.inl (.inl (3 : Fin 14)))
abbrev accumulator : K := .inl (.inl (.inl (13 : Fin 14)))

inductive Label where
  | readInput | restoreInput | ready | writeOutput | done
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList
  [.readInput, .restoreInput, .ready, .writeOutput, .done]
  (by intro l; cases l <;> simp)

/-- Boundary transfers for a Cell-based controller. Output transfer reverses
its reversed accumulator directly into the Boolean output stack. -/
def machine : Label → Stmt Gam Label Sig
  | .readInput => .pop input (fun _ b => b.map bit)
      (.branch isSome
        (.push scratch (fun v => v.getD .mark) (.goto (fun _ => .readInput)))
        (.goto (fun _ => .restoreInput)))
  | .restoreInput => .pop scratch pop
      (.branch isSome
        (.push source (fun v => v.getD .mark) (.goto (fun _ => .restoreInput)))
        (.goto (fun _ => .ready)))
  | .writeOutput => .pop accumulator pop
      (.branch isSome
        (.push output isMark (.goto (fun _ => .writeOutput)))
        (.goto (fun _ => .done)))
  | .ready | .done => .halt

def run : Option (Cfg Gam Label Sig) → Option (Cfg Gam Label Sig) :=
  fun c => c.bind (step machine)

/-- This bundle covers only boundary subroutines; its `ready` handoff must be
replaced by the complete normalizer before claiming Boolean computability. -/
def finiteMachine : Turing.FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := input
  k₁ := output
  Γ := Gam
  Λ := Label
  main := .readInput
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem read_run (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (hs : S input = xs) :
    ∃ U : ∀ j, List (Gam j),
      run^[xs.length+1] (some ⟨some .readInput, v, S⟩) =
        some ⟨some .restoreInput, none, U⟩
      ∧ U input = []
      ∧ U scratch = (xs.map bit).reverse ++ S scratch
      ∧ ∀ j, j ≠ input → j ≠ scratch → U j = S j := by
  induction xs generalizing v S with
  | nil =>
      refine ⟨S, ?_, hs, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, hs, isSome]
  | cons b xs ih =>
      let T := Function.update (Function.update S input xs) scratch (bit b :: S scratch)
      have hfirst : run (some ⟨some .readInput, v, S⟩) =
          some ⟨some .readInput, some (bit b), T⟩ := by
        simp [run, machine, step, stepAux, hs, isSome, T]
      obtain ⟨U, hr, hi, ht, hf⟩ := ih (some (bit b)) T (by simp [T])
      refine ⟨U, ?_, hi, ?_, ?_⟩
      · rw [List.length_cons, Function.iterate_succ_apply, hfirst]; exact hr
      · rw [ht]; simp [T, List.reverse_cons, List.append_assoc]
      · intro j hji hjt; rw [hf j hji hjt]; simp [T, hji, hjt]

theorem restore_run (xs : List Cell) (v : Sig) (S : ∀ j, List (Gam j))
    (hs : S scratch = xs) :
    ∃ U : ∀ j, List (Gam j),
      run^[xs.length+1] (some ⟨some .restoreInput, v, S⟩) =
        some ⟨some .ready, none, U⟩
      ∧ U scratch = []
      ∧ U source = xs.reverse ++ S source
      ∧ ∀ j, j ≠ scratch → j ≠ source → U j = S j := by
  induction xs generalizing v S with
  | nil =>
      refine ⟨S, ?_, hs, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, hs, pop, isSome]
  | cons c xs ih =>
      let T := Function.update (Function.update S scratch xs) source (c :: S source)
      have hfirst : run (some ⟨some .restoreInput, v, S⟩) =
          some ⟨some .restoreInput, some c, T⟩ := by
        simp [run, machine, step, stepAux, hs, pop, isSome, T]
      obtain ⟨U, hr, ht, hu, hf⟩ := ih (some c) T (by simp [T])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [List.length_cons, Function.iterate_succ_apply, hfirst]; exact hr
      · rw [hu]; simp [T, List.reverse_cons, List.append_assoc]
      · intro j hjt hjs; rw [hf j hjt hjs]; simp [T, hjt, hjs]

/-- Load forward Boolean input into the existing parser's forward Cell stack.
The Boolean input is consumed and scratch is returned empty. -/
theorem input_run (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (hi : S input = xs) (ht : S scratch = []) (hs : S source = []) :
    ∃ U : ∀ j, List (Gam j),
      run^[2*xs.length+2] (some ⟨some .readInput, v, S⟩) =
        some ⟨some .ready, none, U⟩
      ∧ U input = [] ∧ U scratch = [] ∧ U source = xs.map bit
      ∧ ∀ j, j ≠ input → j ≠ source → U j = S j := by
  obtain ⟨A, ha, hai, hat, haf⟩ := read_run xs v S hi
  rw [ht, List.append_nil] at hat
  obtain ⟨U, hu, hut, hus, huf⟩ := restore_run (xs.map bit).reverse none A hat
  have hasi : A source = [] := (haf source (by decide) (by decide)).trans hs
  refine ⟨U, ?_, ?_, hut, ?_, ?_⟩
  · simp only [List.length_reverse, List.length_map] at hu
    have h := ShiTMFanout.iterTwo run _ _ _ _ _ ha hu
    have hc : (xs.length+1)+(xs.length+1) = 2*xs.length+2 := by omega
    simpa only [hc] using h
  · exact (huf input (by decide) (by decide)).trans hai
  · simpa [List.reverse_reverse, hasi] using hus
  · intro j hji hjs
    by_cases hjt : j = scratch
    · subst j; exact hut.trans ht.symm
    rw [huf j hjt hjs, haf j hji hjt]

/-- The output writer accepts the bit embedding of a list, empties the Cell
accumulator, and pushes the reversed Boolean list onto the output stack. -/
theorem write_run (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (hs : S accumulator = xs.map bit) :
    ∃ U : ∀ j, List (Gam j),
      run^[xs.length+1] (some ⟨some .writeOutput, v, S⟩) =
        some ⟨some .done, none, U⟩
      ∧ U accumulator = []
      ∧ U output = xs.reverse ++ S output
      ∧ ∀ j, j ≠ accumulator → j ≠ output → U j = S j := by
  induction xs generalizing v S with
  | nil =>
      refine ⟨S, ?_, hs, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, hs, pop, isSome]
  | cons b xs ih =>
      let T := Function.update (Function.update S accumulator (xs.map bit)) output (b :: S output)
      have hfirst : run (some ⟨some .writeOutput, v, S⟩) =
          some ⟨some .writeOutput, some (bit b), T⟩ := by
        cases b <;> simp [run, machine, step, stepAux, hs, pop, isSome, isMark, bit, T]
      obtain ⟨U, hr, ha, ho, hf⟩ := ih (some (bit b)) T (by simp [T])
      refine ⟨U, ?_, ha, ?_, ?_⟩
      · rw [List.length_cons, Function.iterate_succ_apply, hfirst]; exact hr
      · rw [ho]; simp [T, List.reverse_cons, List.append_assoc]
      · intro j hja hjo; rw [hf j hja hjo]; simp [T, hja, hjo]

/-- Directly convert the normalizer's reversed accumulator into forward
Boolean output. This transfer performs the final reversal itself. -/
theorem output_run (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (hs : S accumulator = (xs.map bit).reverse) (ho : S output = []) :
    ∃ U : ∀ j, List (Gam j),
      run^[xs.length+1] (some ⟨some .writeOutput, v, S⟩) =
        some ⟨some .done, none, U⟩
      ∧ U accumulator = [] ∧ U output = xs
      ∧ ∀ j, j ≠ accumulator → j ≠ output → U j = S j := by
  obtain ⟨U, hr, ha, huo, hf⟩ := write_run xs.reverse v S (by simpa using hs)
  refine ⟨U, ?_, ha, ?_, hf⟩
  · simpa only [List.length_reverse] using hr
  · simpa [ho] using huo

end ShiTMBooleanIO
