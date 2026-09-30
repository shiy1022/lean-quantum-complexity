import «AMPUNI-selector-circuit»
import «AMPUNI-subroutine-lift»
import «AMPUNI-layout-machine»
import «AMPUNI-retained-finite»
import «AMPUNI-fanout-machine»
import Mathlib.Tactic.DeriveFintype

/-! A concrete finite-machine emitter for the fair selector used by centering.
The unary-register copy/restore proofs specialize the checked readout emitter
(AMPUNI-readout-{machine,fields,command,run}) to this smaller gate schedule.
This module proves emission only; threshold arithmetic and the family controller
are separate obligations. -/
set_option maxRecDepth 20000

set_option autoImplicit false
set_option maxRecDepth 10000
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine

/-- A bounded constructor tag/layer header, or one of four supplied wire indices. -/
abbrev Command := Fin 5 ⊕ Fin 4
inductive Gate where
  | h (r : Fin 4) | t (r : Fin 4) | cnot (p q : Fin 4)

def gateCommands : Gate → List Command
  | Gate.h r => [.inl 1, .inl 0, .inr r]
  | Gate.t r => [.inl 1, .inl 2, .inr r]
  | Gate.cnot p q => [.inl 1, .inl 4, .inr p, .inr q]

/-- The explicit 37-gate Toffoli template, with symbolic wire registers. -/
def toff (p q r : Fin 4) : List Gate :=
  [Gate.h r, Gate.t p, Gate.t q, Gate.t r, Gate.cnot p q, Gate.t q, Gate.t q,
   Gate.t q, Gate.t q, Gate.t q, Gate.t q, Gate.t q, Gate.cnot p q,
   Gate.cnot q r, Gate.t r, Gate.t r, Gate.t r, Gate.t r, Gate.t r, Gate.t r,
   Gate.t r, Gate.cnot q r, Gate.cnot p r, Gate.t r, Gate.t r, Gate.t r,
   Gate.t r, Gate.t r, Gate.t r, Gate.t r, Gate.cnot p r, Gate.cnot p r,
   Gate.cnot q r, Gate.t r, Gate.cnot q r, Gate.cnot p r, Gate.h r]

def gates : List Gate := [Gate.h 0, Gate.cnot 2 3] ++ toff 0 2 3 ++ toff 0 1 3
def program : List Command := gates.flatMap gateCommands

theorem gates_length : gates.length = 76 := by rfl
theorem program_length : program.length = 249 := by rfl

def unary (n : Nat) : List Cell := List.replicate n Cell.mark ++ [Cell.delim]
def bytes (values : Fin 4 → Nat) : Command → List Cell
  | .inl k => unary k.val
  | .inr k => unary (values k)
def programBytes (values : Fin 4 → Nat) : List Cell := (program.map (bytes values)).flatten

def commandCost (values : Fin 4 → Nat) : Command → Nat
  | .inl _ => 1
  | .inr k => 2*values k+4

def scheduleCost (values : Fin 4 → Nat) (xs : List Command) : Nat :=
  (xs.map (commandCost values)).sum

end ShiTMCenteringSelector

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev PC := Fin 250
abbrev wire (h : Fin 4) : TopK := .inl (.inl ⟨h.val+4, by omega⟩)
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
abbrev output : TopK := .inl (.inl (13 : Fin 14))

theorem wire_ne_scratch (h : Fin 4) : wire h ≠ scratch := by fin_cases h <;> decide
theorem wire_ne_output (h : Fin 4) : wire h ≠ output := by fin_cases h <;> decide

def nextPC (pc : PC) : PC := ⟨(pc.val+1)%250, Nat.mod_lt _ (by decide)⟩
def commandAt (pc : PC) : Option Command := (program.drop pc.val).head?

inductive Label where
  | dispatch (pc : PC) | copy (pc : PC) (h : Fin 4)
  | restore (pc : PC) (h : Fin 4) | delimiter (pc : PC) | finished
  deriving DecidableEq, Fintype

def pushCells : List Cell → Stmt TopGam Label Sig → Stmt TopGam Label Sig
  | [], q => q
  | c :: cs, q => .push output (cst c) (pushCells cs q)

theorem pushCells_step (xs : List Cell) (q : Stmt TopGam Label Sig)
    (v : Sig) (S : ∀ j, List (TopGam j)) :
    stepAux (pushCells xs q) v S =
      stepAux q v (Function.update S output (xs.reverse ++ S output)) := by
  induction xs generalizing S with
  | nil => simp [pushCells]
  | cons c cs ih =>
      simp only [pushCells, stepAux, cst]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def machine : Label → Stmt TopGam Label Sig
  | .dispatch pc => match commandAt pc with
      | none => .goto (fun _ => .finished)
      | some (.inl k) => pushCells (unary k.val) (.goto (fun _ => .dispatch (nextPC pc)))
      | some (.inr h) => .goto (fun _ => .copy pc h)
  | .copy pc h => .pop (wire h) pop
      (.branch isSome
        (.push output (cst Cell.mark) (.push scratch (cst Cell.mark) (.goto (fun _ => .copy pc h))))
        (.goto (fun _ => .restore pc h)))
  | .restore pc h => .pop scratch pop
      (.branch isSome
        (.push (wire h) (cst Cell.mark) (.goto (fun _ => .restore pc h)))
        (.goto (fun _ => .delimiter pc)))
  | .delimiter pc => .push output (cst Cell.delim) (.goto (fun _ => .dispatch (nextPC pc)))
  | .finished => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := wire 0
  k₁ := output
  Γ := TopGam
  Λ := Label
  main := .dispatch 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMCenteringSelector

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine ShiTMRetainedTop

/-- Copy a unary register to the output while saving its marks for restoration. -/
theorem copy_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hsrc : S (wire k) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.copy pc k), v, S⟩) =
        some ⟨some (.restore pc k), none, U⟩
      ∧ U (wire k) = []
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = List.replicate n Cell.mark ++ S scratch
      ∧ ∀ j, j ≠ wire k → j ≠ output → j ≠ scratch → U j = S j := by
  have hks := wire_ne_scratch k
  have hko := wire_ne_output k
  have hso : scratch ≠ output := by decide
  induction n generalizing v S with
  | zero =>
      have he : S (wire k) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, by simp, by simp, by intro j _ _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S (wire k) = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update (Function.update S (wire k) (List.replicate n Cell.mark))
          output (Cell.mark :: S output))
        scratch (Cell.mark :: S scratch)
      have hfirst : run (some ⟨some (.copy pc k), v, S⟩) =
          some ⟨some (.copy pc k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T,
          hks, hks.symm, hko, hko.symm, hso, hso.symm]
      obtain ⟨U, hr, hs, ho, ht, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks, hko])
      refine ⟨U, ?_, hs, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [ho]
        simp [T, hso.symm, List.replicate_add, List.append_assoc]
      · rw [ht]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjo hjs
        rw [hf j hjk hjo hjs]
        simp [T, hjk, hjo, hjs]

/-- Restore the register and clear the saved unary marks. -/
theorem restore_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hs : S scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.restore pc k), v, S⟩) =
        some ⟨some (.delimiter pc), none, U⟩
      ∧ U scratch = []
      ∧ U (wire k) = List.replicate n Cell.mark ++ S (wire k)
      ∧ ∀ j, j ≠ wire k → j ≠ scratch → U j = S j := by
  have hks := wire_ne_scratch k
  induction n generalizing v S with
  | zero =>
      have he : S scratch = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S scratch = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S scratch (List.replicate n Cell.mark))
        (wire k) (Cell.mark :: S (wire k))
      have hfirst : run (some ⟨some (.restore pc k), v, S⟩) =
          some ⟨some (.restore pc k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T, hks]
      obtain ⟨U, hr, ht, hk, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks.symm])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [hk]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjs
        rw [hf j hjk hjs]
        simp [T, hjk, hjs]

/-- Emit a unary value without consuming its register. The delimiter is a
separate control step, allowing reuse for the layer header and both operands. -/
theorem field_run (pc : PC) (k : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hsrc : S (wire k) = List.replicate n Cell.mark) (hs : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+2] (some ⟨some (.copy pc k), v, S⟩) =
        some ⟨some (.delimiter pc), none, U⟩
      ∧ U (wire k) = List.replicate n Cell.mark
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = []
      ∧ ∀ j, j ≠ wire k → j ≠ output → j ≠ scratch → U j = S j := by
  obtain ⟨T, ht, htk, hto, hts, htf⟩ := copy_run pc k n v S hsrc
  obtain ⟨U, hu, hus, huk, huf⟩ :=
    restore_run pc k n none T (by simpa [hs] using hts)
  refine ⟨U, ?_, ?_, ?_, hus, ?_⟩
  · have h := ShiTMFanout.iterTwo run (n+1) (n+1) _ _ _ ht hu
    have hc : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [hc] using h
  · rw [huk, htk, List.append_nil]
  · rw [huf output (wire_ne_output k).symm (by decide), hto]
  · intro j hjk hjo hjs
    rw [huf j hjk hjs, htf j hjk hjo hjs]

end ShiTMCenteringSelector

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine ShiTMRetainedTop

theorem wire_run (pc : PC) (h : Fin 4) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hc : commandAt pc = some (.inr h))
    (hs : S (wire h) = List.replicate n Cell.mark) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+4] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), none, U⟩
      ∧ U output = (unary n).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  have hstart : run^[1] (some ⟨some (.dispatch pc), v, S⟩) =
      some ⟨some (.copy pc h), v, S⟩ := by
    simp [run, machine, hc, step, stepAux]
  obtain ⟨V, hv, hvs, hvo, hvt, hvf⟩ := field_run pc h n v S hs ht
  let U := Function.update V output (Cell.delim :: V output)
  have hdone : run^[1] (some ⟨some (.delimiter pc), none, V⟩) =
      some ⟨some (.dispatch (nextPC pc)), none, U⟩ := by
    simp [run, machine, step, stepAux, cst, U]
  refine ⟨U, ?_, ?_, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ hstart hv
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hdone
    have hc : (1+(2*n+2))+1 = 2*n+4 := by omega
    simpa only [hc] using h2
  · simp [U, hvo, unary, List.reverse_append]
  · intro j hjo
    have hu : U j = V j := by simp [U, hjo]
    rw [hu]
    by_cases hjs : j = wire h
    · subst j; exact hvs.trans hs.symm
    by_cases hjt : j = scratch
    · subst j; exact hvt.trans ht.symm
    exact hvf j hjs hjo hjt

theorem command_run (pc : PC) (c : Command) (values : Fin 4 → Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hc : commandAt pc = some c)
    (hvalues : ∀ h, S (wire h) = List.replicate (values h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[commandCost values c] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), v', U⟩
      ∧ U output = (bytes values c).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  cases c with
  | inl k =>
      let U := Function.update S output ((unary k.val).reverse ++ S output)
      refine ⟨U, v, ?_, by simp [U, bytes], ?_⟩
      · simp [commandCost, run, machine, hc, step, pushCells_step, stepAux, U]
      · intro j hj; simp [U, hj]
  | inr h =>
      obtain ⟨U, hr, ho, hf⟩ := wire_run pc h (values h) v S hc (hvalues h) ht
      exact ⟨U, none, hr, ho, hf⟩

end ShiTMCenteringSelector

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine ShiTMRetainedTop

private theorem active_suffix (pc : PC) (c : Command) (xs : List Command)
    (hs : program.drop pc.val = c :: xs) :
    commandAt pc = some c ∧ (nextPC pc).val = pc.val+1 ∧
      program.drop (nextPC pc).val = xs := by
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_cons, program_length] at hlen
  have hnext : (nextPC pc).val = pc.val+1 := by
    apply Nat.mod_eq_of_lt
    omega
  refine ⟨?_, hnext, ?_⟩
  · simp [commandAt, hs]
  · rw [hnext, ← List.drop_drop, hs]; rfl

theorem run_suffix (xs : List Command) (values : Fin 4 → Nat)
    (pc : PC) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : program.drop pc.val = xs)
    (hvalues : ∀ h, S (wire h) = List.replicate (values h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig) (pc' : PC),
      run^[scheduleCost values xs] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch pc'), v', U⟩
      ∧ pc'.val = pc.val+xs.length
      ∧ U output = ((xs.map (bytes values)).flatten).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  induction xs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, by simp, by intro j _; rfl⟩
  | cons c xs ih =>
      obtain ⟨hc, hn, hs'⟩ := active_suffix pc c xs hs
      obtain ⟨T, w, hfirst, hTo, hTf⟩ := command_run pc c values v S hc hvalues ht
      obtain ⟨U, w', pc', hrest, hp, hUo, hUf⟩ :=
        ih (nextPC pc) w T hs'
          (fun h => (hTf (wire h) (wire_ne_output h)).trans (hvalues h))
          ((hTf scratch (by decide)).trans ht)
      refine ⟨U, w', pc', ?_, ?_, ?_, ?_⟩
      · change run^[commandCost values c + scheduleCost values xs]
          (some ⟨some (.dispatch pc), v, S⟩) =
            some ⟨some (.dispatch pc'), w', U⟩
        exact ShiTMFanout.iterTwo run _ _ _ _ _ hfirst hrest
      · rw [hn] at hp
        simp only [List.length_cons]
        omega
      · rw [hUo, hTo]
        simp [List.reverse_append, List.append_assoc]
      · intro j hj; rw [hUf j hj, hTf j hj]

/-- The fixed 76-gate fair-selector program emits its payload, retaining all four
wire registers and every other stack except output. Scratch is empty again. -/
theorem program_run (values : Fin 4 → Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (wire h) = List.replicate (values h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost values program + 1] (some ⟨some (.dispatch 0), v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U output = (programBytes values).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  obtain ⟨U, v', pc', hr, hp, ho, hf⟩ :=
    run_suffix program values 0 v S (by simp) hvalues ht
  have hc : commandAt pc' = none := by
    simp only [Fin.val_zero, Nat.zero_add] at hp
    simp [commandAt, hp]
  have hdone : run^[1] (some ⟨some (.dispatch pc'), v', U⟩) =
      some ⟨some .finished, v', U⟩ := by simp [run, machine, hc, step, stepAux]
  exact ⟨U, v', ShiTMFanout.iterTwo run _ _ _ _ _ hr hdone, ho, hf⟩

theorem scheduleCost_le (xs : List Command) (values : Fin 4 → Nat) (M : Nat)
    (hv : ∀ h, values h ≤ M) : scheduleCost values xs ≤ xs.length*(2*M+4) := by
  induction xs with
  | nil => simp [scheduleCost]
  | cons c xs ih =>
      have hc : commandCost values c ≤ 2*M+4 := by
        cases c with
        | inl k => simp [commandCost]
        | inr k => have h := hv k; simp only [commandCost]; omega
      simp only [scheduleCost, List.map_cons, List.sum_cons] at *
      simp only [List.length_cons, Nat.add_mul]
      omega

theorem program_cost_le (values : Fin 4 → Nat) (M : Nat) (hv : ∀ h, values h ≤ M) :
    scheduleCost values program + 1 ≤ 498*M+997 := by
  have h := scheduleCost_le program values M hv
  rw [program_length] at h
  omega

end ShiTMCenteringSelector
namespace ShiTMCenteringSelector
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit

/-- Exact layer payload, without the enclosing circuit-length prefix. -/
theorem programBytes_fairSelector {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) :
    programBytes (fun i => (w i).val) =
      (((fairSelectorCirc w hw).map ShiBQP.encLayer).flatten).map bit := by
  simp [programBytes, program, gates, toff, gateCommands, bytes, unary,
    fairSelectorCirc, selectorCirc, ShiExplicitCirc.toffCirc,
    ShiExplicitCirc.toffGates, ShiBQP.encLayer, ShiBQP.encStr,
    ShiBQP.encInstr, ShiBQP.encNat, bit, List.append_assoc]

/-- Emit the checked selector circuit while preserving all source registers. -/
theorem typed_selector_run {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (v : Sig) (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (wire h) = List.replicate (w h).val Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost (fun i => (w i).val) program + 1]
        (some ⟨some (.dispatch 0), v, S⟩) = some ⟨some .finished, v', U⟩
      ∧ U output =
        ((((fairSelectorCirc w hw).map ShiBQP.encLayer).flatten).map bit).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  obtain ⟨U, v', hr, ho, hf⟩ := program_run (fun i => (w i).val) v S hvalues ht
  exact ⟨U, v', hr, by simpa only [programBytes_fairSelector w hw] using ho, hf⟩

theorem typed_selector_cost_le {N : Nat} (w : Fin 4 → Fin N) :
    scheduleCost (fun i => (w i).val) program + 1 ≤ 498*N+997 :=
  program_cost_le _ N (fun h => Nat.le_of_lt (w h).isLt)

end ShiTMCenteringSelector

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringSelector.finiteMachine,
      ``ShiTMCenteringSelector.programBytes_fairSelector,
      ``ShiTMCenteringSelector.typed_selector_run,
      ``ShiTMCenteringSelector.typed_selector_cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected selector-emitter axiom {ax} in {name}"
    logInfo m!"CENTERING_SELECTOR_EMITTER_CHECKED {name}; axioms {axioms}"

/-! Coin-step wrapper and complete digit loop. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringCoin
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output unary bytes program programBytes
  scheduleCost commandCost)
end E

abbrev Label := Bool ⊕ ShiTMCenteringSelector.Label

def xHeader : List Cell := E.unary 1 ++ E.unary 3

def machine : Label → Stmt TopGam Label Sig
  | .inl false => .goto (fun _ => .inr (.dispatch 0))
  | .inl true => ShiTMSubroutine.stmt Sum.inr
      (ShiTMCenteringSelector.pushCells xHeader (.goto (fun _ => .copy 249 2)))
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMCenteringSelector.machine l)

def run := ShiTMSubroutine.run machine

def finiteMachine (b : Bool) : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := E.wire 0
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl b
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- The selector's final PC wraps to its initial PC. Starting its copy routine
here emits the X operand and then executes the complete selector schedule. -/
theorem operand_then_selector (values : Fin 4 → Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (E.wire h) = List.replicate (values h) Cell.mark)
    (ht : S E.scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      ShiTMCenteringSelector.run^[2*values 2+3 + (E.scheduleCost values E.program+1)]
        (some ⟨some (.copy 249 2), v, S⟩) = some ⟨some .finished, v', U⟩
      ∧ U E.output = (E.unary (values 2) ++ E.programBytes values).reverse ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨T, hr, hw, ho, hs, hf⟩ :=
    ShiTMCenteringSelector.field_run 249 2 (values 2) v S (hvalues 2) ht
  let V := Function.update T E.output (Cell.delim :: T E.output)
  have hd : ShiTMCenteringSelector.run^[1]
      (some ⟨some (.delimiter 249), none, T⟩) =
      some ⟨some (.dispatch 0), none, V⟩ := by
    simp [ShiTMCenteringSelector.run, ShiTMCenteringSelector.machine,
      ShiTMCenteringSelector.nextPC, step, stepAux, cst, V]
  have hvf : ∀ j, j ≠ E.output → V j = S j := by
    intro j hj
    simp only [V, Function.update_of_ne hj]
    by_cases he : j = E.wire 2
    · subst j; exact hw.trans (hvalues 2).symm
    by_cases he' : j = E.scratch
    · subst j; exact hs.trans ht.symm
    exact hf j he hj he'
  obtain ⟨U, v', hu, huo, huf⟩ := ShiTMCenteringSelector.program_run values none V
    (fun h => (hvf _ (ShiTMCenteringSelector.wire_ne_output h)).trans (hvalues h))
    ((hvf _ (by decide)).trans ht)
  refine ⟨U, v', ?_, ?_, fun j hj => (huf j hj).trans (hvf j hj)⟩
  · have h := ShiTMFanout.iterTwo ShiTMCenteringSelector.run _ _ _ _ _ hr hd
    have hc : (2*values 2+2)+1 = 2*values 2+3 := by omega
    rw [hc] at h
    exact ShiTMFanout.iterTwo ShiTMCenteringSelector.run _ _ _ _ _ h hu
  · rw [huo]
    simp [V, ho, E.unary, List.reverse_append, List.append_assoc]

def payload (values : Fin 4 → Nat) (b : Bool) : List Cell :=
  (if b then xHeader ++ E.unary (values 2) else []) ++ E.programBytes values

def cost (values : Fin 4 → Nat) (b : Bool) : Nat :=
  1 + (if b then 2*values 2+3 else 0) + (E.scheduleCost values E.program+1)

theorem program_run (values : Fin 4 → Nat) (b : Bool) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (E.wire h) = List.replicate (values h) Cell.mark)
    (ht : S E.scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost values b] (some ⟨some (.inl b), v, S⟩) =
        some ⟨some (.inr .finished), v', U⟩
      ∧ U E.output = (payload values b).reverse ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  cases b with
  | false =>
    obtain ⟨U, v', hr, ho, hf⟩ := ShiTMCenteringSelector.program_run values v S hvalues ht
    have hl := ShiTMSubroutine.run_to_terminal ShiTMCenteringSelector.machine machine
      Sum.inr .finished rfl (fun _ _ => rfl) _ _ _ rfl hr
    have he : run^[1] (some ⟨some (.inl false), v, S⟩) =
        some ⟨some (.inr (.dispatch 0)), v, S⟩ := rfl
    refine ⟨U, v', ?_, by simpa [payload] using ho, hf⟩
    exact ShiTMFanout.iterTwo run _ _ _ _ _ he hl
  | true =>
    let T := Function.update S E.output (xHeader.reverse ++ S E.output)
    have htf : ∀ j, j ≠ E.output → T j = S j := by intro j hj; simp [T, hj]
    obtain ⟨U, v', hr, ho, hf⟩ := operand_then_selector values v T
      (fun h => (htf _ (ShiTMCenteringSelector.wire_ne_output h)).trans (hvalues h))
      ((htf _ (by decide)).trans ht)
    have hl := ShiTMSubroutine.run_to_terminal ShiTMCenteringSelector.machine machine
      Sum.inr .finished rfl (fun _ _ => rfl) _ _ _ rfl hr
    have he : run^[1] (some ⟨some (.inl true), v, S⟩) =
        some ⟨some (.inr (.copy 249 2)), v, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, ShiTMSubroutine.stepAux_lift,
        ShiTMCenteringSelector.pushCells_step, stepAux, ShiTMSubroutine.cfg, T]
    refine ⟨U, v', ?_, ?_, fun j hj => (hf j hj).trans (htf j hj)⟩
    · have h := ShiTMFanout.iterTwo run _ _ _ _ _ he hl
      simpa only [cost, ↓reduceIte, Nat.add_assoc, ShiTMSubroutine.cfg, Option.map_some] using h
    · rw [ho]
      simp [payload, T, List.reverse_append, List.append_assoc]

theorem payload_coinStep {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (b : Bool) :
    payload (fun i => (w i).val) b =
      (((ShiQMACenteringCircuit.coinStep w hw b).map ShiBQP.encLayer).flatten).map bit := by
  cases b <;> simp [payload, ShiTMCenteringSelector.programBytes_fairSelector w hw,
    ShiQMACenteringCircuit.coinStep, xHeader, E.unary,
    ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encInstr, ShiBQP.encNat, bit,
    List.append_assoc]

theorem cost_le (values : Fin 4 → Nat) (b : Bool) (M : Nat)
    (hv : ∀ h, values h ≤ M) : cost values b ≤ 500*M+1001 := by
  have h := ShiTMCenteringSelector.program_cost_le values M hv
  have h2 := hv 2
  cases b <;> simp only [cost, Bool.false_eq_true, ↓reduceIte] <;> omega

end ShiTMCenteringCoin

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringCoin.finiteMachine,
      ``ShiTMCenteringCoin.program_run,
      ``ShiTMCenteringCoin.payload_coinStep,
      ``ShiTMCenteringCoin.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected coin-emitter axiom {ax} in {name}"
    logInfo m!"CENTERING_COIN_EMITTER_CHECKED {name}; axioms {axioms}"

/-! AMPUNI-centering-coin-loop -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringCoinLoop
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E

abbrev digits : TopK := .inl (.inl (8 : Fin 14))

theorem wire_ne_digits (h : Fin 4) : E.wire h ≠ digits := by fin_cases h <;> decide

theorem wire_injective : Function.Injective E.wire := by
  intro i j h
  have hv := congrArg (fun k : TopK => match k with
    | .inl (.inl t) => t.val | _ => 0) h
  change i.val + 4 = j.val + 4 at hv
  exact Fin.ext (by omega)

inductive Label where
  | dispatch | emit (l : ShiTMCenteringCoin.Label) | finished
  deriving DecidableEq, Fintype

/-- Increment each of the four unary wire registers by three. -/
def advance : Stmt TopGam Label Sig :=
  .push (E.wire 0) (cst .mark) (.push (E.wire 0) (cst .mark) (.push (E.wire 0) (cst .mark)
  (.push (E.wire 1) (cst .mark) (.push (E.wire 1) (cst .mark) (.push (E.wire 1) (cst .mark)
  (.push (E.wire 2) (cst .mark) (.push (E.wire 2) (cst .mark) (.push (E.wire 2) (cst .mark)
  (.push (E.wire 3) (cst .mark) (.push (E.wire 3) (cst .mark) (.push (E.wire 3) (cst .mark)
  (.goto (fun _ => .dispatch)))))))))))))

def machine : Label → Stmt TopGam Label Sig
  | .dispatch => .pop digits pop (.branch isSome
      (.branch isMark (.goto (fun _ => .emit (.inl true)))
        (.goto (fun _ => .emit (.inl false))))
      (.goto (fun _ => .finished)))
  | .emit (.inr .finished) => advance
  | .emit l => ShiTMSubroutine.stmt Label.emit (ShiTMCenteringCoin.machine l)
  | .finished => .halt

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := digits
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .dispatch
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def bump (S : ∀ j, List (TopGam j)) : ∀ j, List (TopGam j) :=
  Function.update (Function.update (Function.update (Function.update S
    (E.wire 0) (List.replicate 3 Cell.mark ++ S (E.wire 0)))
    (E.wire 1) (List.replicate 3 Cell.mark ++ S (E.wire 1)))
    (E.wire 2) (List.replicate 3 Cell.mark ++ S (E.wire 2)))
    (E.wire 3) (List.replicate 3 Cell.mark ++ S (E.wire 3))

theorem bump_wire (S : ∀ j, List (TopGam j)) (h : Fin 4) :
    bump S (E.wire h) = List.replicate 3 Cell.mark ++ S (E.wire h) := by
  fin_cases h <;> simp [bump, E.wire]

theorem bump_frame (S : ∀ j, List (TopGam j)) (j : TopK)
    (hj : ∀ h, j ≠ E.wire h) : bump S j = S j := by
  simp [bump, hj]

theorem advance_run (v : Sig) (S : ∀ j, List (TopGam j)) :
    run^[1] (some ⟨some (.emit (.inr .finished)), v, S⟩) =
      some ⟨some .dispatch, v, bump S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, advance, step, stepAux, cst,
    bump, E.wire, List.replicate_succ]

def shifted (values : Fin 4 → Nat) : Fin 4 → Nat := fun h => values h + 3

def payload : (Fin 4 → Nat) → List Bool → List Cell
  | _, [] => []
  | values, b :: bs => ShiTMCenteringCoin.payload values b ++ payload (shifted values) bs

def cost : (Fin 4 → Nat) → List Bool → Nat
  | _, [] => 1
  | values, b :: bs => 1 + ShiTMCenteringCoin.cost values b + 1 + cost (shifted values) bs

/-- Input digits are consumed in emission order (least significant first).
The original source circuit and all unrelated stacks are retained. -/
theorem program_run (values : Fin 4 → Nat) (bs : List Bool) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (E.wire h) = List.replicate (values h) Cell.mark)
    (ht : S E.scratch = []) (hd : S digits = bs.map bit) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost values bs] (some ⟨some .dispatch, v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U E.output = (payload values bs).reverse ++ S E.output
      ∧ U digits = []
      ∧ (∀ h, U (E.wire h) = List.replicate (values h + 3*bs.length) Cell.mark)
      ∧ ∀ j, j ≠ E.output → j ≠ digits → (∀ h, j ≠ E.wire h) → U j = S j := by
  induction bs generalizing values v S with
  | nil =>
    have hd' : S digits = [] := by simpa using hd
    refine ⟨S, none, ?_, by simp [payload], hd', ?_, by intro j _ _ _; rfl⟩
    · simp [cost, run, ShiTMSubroutine.run, machine, step, stepAux, hd', pop, isSome]
    · simpa using hvalues
  | cons b bs ih =>
    let T := Function.update S digits (bs.map bit)
    have hstart : run^[1] (some ⟨some .dispatch, v, S⟩) =
        some ⟨some (.emit (.inl b)), some (bit b), T⟩ := by
      cases b <;> simp [run, ShiTMSubroutine.run, machine, step, stepAux,
        hd, T, pop, isSome, isMark, bit]
    have htf : ∀ j, j ≠ digits → T j = S j := by intro j hj; simp [T, hj]
    obtain ⟨V, v', hcoin, hvo, hvf⟩ := ShiTMCenteringCoin.program_run values b (some (bit b)) T
      (fun h => (htf _ (wire_ne_digits h)).trans (hvalues h))
      ((htf _ (by decide)).trans ht)
    have hl := ShiTMSubroutine.run_to_terminal ShiTMCenteringCoin.machine machine
      Label.emit (.inr .finished) rfl (by
        intro l hl
        cases l with
        | inl b => cases b <;> rfl
        | inr l => cases l <;> first | rfl | exact (hl rfl).elim)
      _ _ _ rfl hcoin
    have hbvalues : ∀ h, bump V (E.wire h) = List.replicate (shifted values h) Cell.mark := by
      intro h
      rw [bump_wire, hvf _ (ShiTMCenteringSelector.wire_ne_output h),
        htf _ (wire_ne_digits h), hvalues h]
      change List.replicate 3 Cell.mark ++ List.replicate (values h) Cell.mark = _
      rw [← List.replicate_add]
      exact congrArg (fun n => List.replicate n Cell.mark) (Nat.add_comm 3 (values h))
    have hbscratch : bump V E.scratch = [] := by
      rw [bump_frame _ _ (fun h => (ShiTMCenteringSelector.wire_ne_scratch h).symm),
        hvf _ (by decide), htf _ (by decide), ht]
    have hbdigits : bump V digits = bs.map bit := by
      rw [bump_frame _ _ (fun h => (wire_ne_digits h).symm), hvf _ (by decide)]
      simp [T]
    obtain ⟨U, u, hu, huo, hud, huw, huf⟩ := ih (shifted values) v' (bump V)
      hbvalues hbscratch hbdigits
    refine ⟨U, u, ?_, ?_, hud, ?_, ?_⟩
    · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ hstart hl
      have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 (advance_run v' V)
      exact ShiTMFanout.iterTwo run _ _ _ _ _ h2 hu
    · rw [huo, bump_frame _ _ (fun h => (ShiTMCenteringSelector.wire_ne_output h).symm), hvo,
        htf _ (by decide)]
      simp [payload, List.reverse_append, List.append_assoc]
    · intro h
      have he : shifted values h + 3*bs.length = values h + 3*(b::bs).length := by
        simp only [shifted, List.length_cons]
        omega
      exact (huw h).trans (congrArg (fun n => List.replicate n Cell.mark) he)
    · intro j hjo hjd hjw
      rw [huf j hjo hjd hjw, bump_frame _ _ hjw, hvf j hjo, htf j hjd]

theorem cost_le (values : Fin 4 → Nat) (bs : List Bool) (M : Nat)
    (hv : ∀ h, values h + 3*bs.length ≤ M) :
    cost values bs ≤ bs.length*(500*M+1003)+1 := by
  induction bs generalizing values with
  | nil => simp [cost]
  | cons b bs ih =>
    have hc := ShiTMCenteringCoin.cost_le values b M (fun h => by have := hv h; omega)
    have hr := ih (shifted values) (fun h => by
      have := hv h
      simp only [shifted, List.length_cons] at *
      omega)
    simp only [cost, List.length_cons, Nat.add_mul]
    omega

end ShiTMCenteringCoinLoop

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringCoinLoop.finiteMachine,
      ``ShiTMCenteringCoinLoop.program_run,
      ``ShiTMCenteringCoinLoop.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected coin-loop axiom {ax} in {name}"
    logInfo m!"CENTERING_COIN_LOOP_CHECKED {name}; axioms {axioms}"

/-! AMPUNI-centering-coin-loop-contract -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2

namespace ShiTMCenteringCoinLoop
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit

def coinValues (base k : Nat) : Fin 4 → Nat :=
  ![base+3*k+1, base+3*k, base+3*k+2, base+3*k+3]

theorem payload_append (values : Fin 4 → Nat) (xs ys : List Bool) :
    payload values (xs ++ ys) = payload values xs ++
      payload (fun h => values h + 3*xs.length) ys := by
  induction xs generalizing values with
  | nil => simp [payload]
  | cons b xs ih =>
    simp only [List.cons_append, payload, ih, List.length_cons, List.append_assoc]
    have he : (fun h => shifted values h + 3*xs.length) =
        (fun h => values h + 3*(xs.length+1)) := by
      funext h
      simp only [shifted]
      omega
    rw [he]

/-- The machine's least-significant-first emission equals the tail-first
recursive circuit definition, including every optional X layer. -/
theorem payload_coinCircuit {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3*bs.length < N) :
    payload (coinValues base 0) bs.reverse =
      (((coinCircuit base bs h).map ShiBQP.encLayer).flatten).map bit := by
  induction bs with
  | nil => simp [payload, coinCircuit]
  | cons b bs ih =>
    have ht : base + 3*bs.length < N := by simp only [List.length_cons] at h; omega
    have hs : base + 3*(bs.length+1) < N := by simpa only [List.length_cons] using h
    have hv : (fun i => coinValues base 0 i + 3*bs.reverse.length) =
        (fun i => (coinWires base bs.length hs i).val) := by
      funext i
      fin_cases i <;> simp [coinValues, coinWires] <;> omega
    rw [List.reverse_cons, payload_append, ih ht, hv]
    simp only [payload, List.append_nil]
    rw [ShiTMCenteringCoin.payload_coinStep _ (coinWires_injective base bs.length hs)]
    simp [coinCircuit, List.map_append, List.flatten_append]

/-- Complete finite-machine contract for the dyadic-coin circuit payload. -/
theorem typed_coinCircuit_run {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3*bs.length < N) (v : Sig) (S : ∀ j, List (TopGam j))
    (hvalues : ∀ i, S (E.wire i) = List.replicate (coinValues base 0 i) Cell.mark)
    (ht : S E.scratch = []) (hd : S digits = bs.reverse.map bit) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost (coinValues base 0) bs.reverse] (some ⟨some .dispatch, v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U E.output =
        ((((coinCircuit base bs h).map ShiBQP.encLayer).flatten).map bit).reverse ++ S E.output
      ∧ U digits = []
      ∧ (∀ i, U (E.wire i) = List.replicate (coinValues base bs.length i) Cell.mark)
      ∧ ∀ j, j ≠ E.output → j ≠ digits → (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨U, v', hr, ho, hd', hw, hf⟩ := program_run (coinValues base 0) bs.reverse v S hvalues ht hd
  refine ⟨U, v', hr, ?_, hd', ?_, hf⟩
  · simpa only [payload_coinCircuit base bs h] using ho
  · intro i
    rw [hw]
    congr 1
    fin_cases i <;> simp [coinValues] <;> omega

theorem typed_coinCircuit_cost_le (base : Nat) (bs : List Bool) :
    cost (coinValues base 0) bs.reverse ≤
      bs.length * (500*(base+3*bs.length+3)+1003)+1 := by
  have h := cost_le (coinValues base 0) bs.reverse (base+3*bs.length+3) (by
    intro i
    fin_cases i <;> simp [coinValues] <;> omega)
  simpa only [List.length_reverse] using h

end ShiTMCenteringCoinLoop

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringCoinLoop.payload_coinCircuit,
      ``ShiTMCenteringCoinLoop.typed_coinCircuit_run,
      ``ShiTMCenteringCoinLoop.typed_coinCircuit_cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected coin-loop-contract axiom {ax} in {name}"
    logInfo m!"CENTERING_COIN_LOOP_CONTRACT_CHECKED {name}; axioms {axioms}"
