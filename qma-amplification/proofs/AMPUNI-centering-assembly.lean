import «AMPUNI-centering-input-prepare»
import «AMPUNI-output-header-schedule»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringPayload
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev source : TopK := .inl (.inl 11)
abbrev output : TopK := .inl (.inl 13)

inductive Label where
  | copy | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.copy, .finished]
  (by intro l; cases l <;> simp)

def machine : Label → Stmt TopGam Label Sig
  | .copy => .pop source pop (.branch isSome
      (.push output ShiTMLayoutMachine.get (.goto (fun _ => .copy)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := source
  k₁ := output
  Γ := TopGam
  Λ := Label
  main := .copy
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- Copy a forward payload onto the reversed output in exactly one step per cell
plus the empty-stack transition. Every other stack is preserved. -/
theorem copy_run (xs : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = xs) :
    ∃ U : ∀ j, List (TopGam j),
      run^[xs.length+1] (some ⟨some (.copy), v, S⟩) =
        some ⟨some (.finished), none, U⟩
      ∧ U source = []
      ∧ U output = xs.reverse ++ S output
      ∧ ∀ j, j ≠ source → j ≠ output → U j = S j := by
  induction xs generalizing v S with
  | nil =>
    refine ⟨S, ?_, hs, by simp, by intro j _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
    let T := Function.update (Function.update S source xs) output (x :: S output)
    have hfirst : run (some ⟨some (.copy), v, S⟩) =
        some ⟨some (.copy), some x, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isSome,
        ShiTMLayoutMachine.get, T, source, output]
    obtain ⟨U, hr, hu, ho, hf⟩ := ih (some x) T (by simp [T, source, output])
    refine ⟨U, ?_, hu, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, hfirst]; exact hr
    · rw [ho]
      simp [T, List.reverse_cons, List.append_assoc]
    · intro j hjs hjo
      rw [hf j hjs hjo]
      simp [T, hjs, hjo]

/-- The copier preserves the exact original circuit bytes after any header. -/
theorem copy_after_header (payload header : List Bool) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hs : S source = payload.map bit) (ho : S output = (header.map bit).reverse) :
    ∃ U : ∀ j, List (TopGam j),
      run^[payload.length+1] (some ⟨some (.copy), v, S⟩) =
        some ⟨some (.finished), none, U⟩
      ∧ U source = []
      ∧ U output = ((header ++ payload).map bit).reverse
      ∧ ∀ j, j ≠ source → j ≠ output → U j = S j := by
  obtain ⟨U, hr, hu, hout, hf⟩ := copy_run (payload.map bit) v S hs
  refine ⟨U, by simpa using hr, hu, ?_, hf⟩
  rw [hout, ho, List.map_append, List.reverse_append]

end ShiTMCenteringPayload

namespace ShiTMCenteringCoreCopy
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev source (h : Fin 4) : TopK := .inl (.inl (![0,1,2,10] h))

theorem source_ne_output (h : Fin 4) : source h ≠ E.output := by fin_cases h <;> decide
theorem source_ne_scratch (h : Fin 4) : source h ≠ E.scratch := by fin_cases h <;> decide

inductive Label where
  | copy | restore | finished
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList [.copy, .restore, .finished]
  (by intro l; cases l <;> simp)

def machine (h : Fin 4) : Label → Stmt TopGam Label Sig
  | .copy => .pop (source h) pop (.branch isSome
      (.push E.output (cst Cell.mark)
      (.push E.scratch (cst Cell.mark) (.goto (fun _ => .copy))))
      (.goto (fun _ => .restore)))
  | .restore => .pop E.scratch pop (.branch isSome
      (.push (source h) (cst Cell.mark) (.goto (fun _ => .restore)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run (h : Fin 4) := ShiTMSubroutine.run (machine h)

theorem copy_run (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (source h) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      (run h)^[n+1] (some ⟨some (.copy), v, S⟩) = some ⟨some (.restore), none, U⟩
      ∧ U (source h) = []
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ U E.scratch = List.replicate n Cell.mark ++ S E.scratch
      ∧ ∀ j, j ≠ source h → j ≠ E.scratch → j ≠ E.output → U j = S j := by
  induction n generalizing v S with
  | zero =>
    have he : S (source h) = [] := by simpa using hs
    refine ⟨S, ?_, he, by simp, by simp, by intro j _ _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
    have hm : S (source h) = Cell.mark :: List.replicate n Cell.mark := by simpa [List.replicate_succ] using hs
    let T := Function.update (Function.update (Function.update S (source h) (List.replicate n Cell.mark))
      E.output (Cell.mark :: S E.output)) E.scratch (Cell.mark :: S E.scratch)
    have hfirst : run h (some ⟨some (.copy), v, S⟩) =
        some ⟨some (.copy), some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hm, pop, isSome,
        cst, T, source_ne_output h, source_ne_scratch h,
        (source_ne_output h).symm, (source_ne_scratch h).symm, E.output, E.scratch]
    have htSrc : T (source h) = List.replicate n Cell.mark := by
      simp [T, source_ne_output h, source_ne_scratch h]
    obtain ⟨U, hr, hu, hw, ht, hf⟩ := ih (some Cell.mark) T htSrc
    refine ⟨U, ?_, hu, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact hr
    · rw [hw]
      dsimp only [T]
      rw [Function.update_of_ne (show E.output ≠ E.scratch by decide), Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S E.output)
    · rw [ht]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S E.scratch)
    · intro j hjh hjs hjw
      rw [hf j hjh hjs hjw]
      simp [T, hjs, hjw, hjh]

theorem restore_run (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S E.scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      (run h)^[n+1] (some ⟨some (.restore), v, S⟩) = some ⟨some (.finished), none, U⟩
      ∧ U E.scratch = []
      ∧ U (source h) = List.replicate n Cell.mark ++ S (source h)
      ∧ ∀ j, j ≠ source h → j ≠ E.scratch → U j = S j := by
  induction n generalizing v S with
  | zero =>
    have he : S E.scratch = [] := by simpa using hs
    refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
    have hm : S E.scratch = Cell.mark :: List.replicate n Cell.mark := by simpa [List.replicate_succ] using hs
    let T := Function.update (Function.update S E.scratch (List.replicate n Cell.mark))
      (source h) (Cell.mark :: S (source h))
    have hfirst : run h (some ⟨some (.restore), v, S⟩) =
        some ⟨some (.restore), some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hm, pop, isSome, cst, T, source_ne_scratch h, (source_ne_scratch h).symm]
    obtain ⟨U, hr, hu, hh, hf⟩ := ih (some Cell.mark) T (by simp [T, source_ne_scratch h, (source_ne_scratch h).symm])
    refine ⟨U, ?_, hu, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact hr
    · rw [hh]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S (source h))
    · intro j hjh hjs
      rw [hf j hjh hjs]
      simp [T, hjh, hjs]

/-- Add a computed header counter to the output, restoring that counter. -/
theorem field_run (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (source h) = List.replicate n Cell.mark) (ht : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      (run h)^[2*n+2] (some ⟨some (.copy), v, S⟩) = some ⟨some (.finished), none, U⟩
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨A, ha, hah, haw, has, haf⟩ := copy_run h n v S hs
  obtain ⟨U, hu, hus, huh, huf⟩ := restore_run h n none A (by simpa [ht] using has)
  refine ⟨U, ?_, ?_, ?_⟩
  · have hr := ShiTMFanout.iterTwo (run h) _ _ _ _ _ ha hu
    have he : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [he] using hr
  · rw [huf _ (source_ne_output h).symm (by decide), haw]
  · intro j hjw
    by_cases hjh : j = source h
    · subst j; rw [huh, hah, List.append_nil, hs]
    by_cases hjs : j = E.scratch
    · subst j; exact hus.trans ht.symm
    rw [huf j hjh hjs, haf j hjh hjs hjw]

end ShiTMCenteringCoreCopy

namespace ShiTMCenteringHeader
open ShiTMLayoutMachine

/-- The eight counter values available before circuit assembly. -/
inductive Atom where
  | input | witness | ancilla | oldDepth | ancExtra | outExtra | depthExtra | one
  deriving DecidableEq
instance : Fintype Atom := Fintype.ofList
  [Atom.input, Atom.witness, Atom.ancilla, Atom.oldDepth, Atom.ancExtra, Atom.outExtra, Atom.depthExtra, Atom.one]
  (by intro a; cases a <;> simp)
inductive Command where
  | add (a : Atom) | delimiter
  deriving DecidableEq, Fintype

def value (n w a d ai oi di : Nat) : Atom → Nat
  | .input => n
  | .witness => w
  | .ancilla => a
  | .oldDepth => d
  | .ancExtra => ai
  | .outExtra => oi
  | .depthExtra => di
  | .one => 1

def cells (v : Atom → Nat) : Command → List Cell
  | .add a => List.replicate (v a) Cell.mark
  | .delimiter => [Cell.delim]

def eval (v : Atom → Nat) : List Command → List Cell → List Cell
  | [], acc => acc
  | c :: cs, acc => eval v cs (cells v c ++ acc)

def field (xs : List Atom) : List Command := xs.map Command.add ++ [Command.delimiter]
def program : List Command :=
  field [Atom.witness] ++ field [Atom.ancilla, Atom.ancExtra] ++
  field [Atom.input, Atom.witness, Atom.ancilla, Atom.one, Atom.outExtra] ++
  field [Atom.oldDepth, Atom.depthExtra]

theorem eval_append (v : Atom → Nat) (xs ys : List Command) (acc : List Cell) :
    eval v (xs ++ ys) acc = eval v ys (eval v xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c xs ih => exact ih (cells v c ++ acc)

theorem eval_adds (v : Atom → Nat) (xs : List Atom) (acc : List Cell) :
    eval v (xs.map Command.add) acc = List.replicate (xs.map v).sum Cell.mark ++ acc := by
  induction xs generalizing acc with
  | nil => simp [eval]
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, eval, cells]
    rw [ih, ← List.append_assoc, ← List.replicate_add, Nat.add_comm (xs.map v).sum (v a)]

theorem eval_field (v : Atom → Nat) (xs : List Atom) (acc : List Cell) :
    eval v (field xs) acc = Cell.delim :: List.replicate (xs.map v).sum Cell.mark ++ acc := by
  rw [field, eval_append, eval_adds]
  rfl

/-- All four fields are emitted in the order of the circuit encoding. -/
theorem program_correct (n w a d ai oi di : Nat) (acc : List Cell) :
    eval (value n w a d ai oi di) program acc =
      (Cell.delim :: List.replicate (d+di) Cell.mark) ++
      (Cell.delim :: List.replicate (n+w+a+1+oi) Cell.mark) ++
      (Cell.delim :: List.replicate (a+ai) Cell.mark) ++
      (Cell.delim :: List.replicate w Cell.mark) ++ acc := by
  simp only [program, eval_append, eval_field, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, value, Nat.add_zero]
  simp only [Nat.add_assoc, List.cons_append, List.append_assoc]

/-- Substitute the exact increments computed by the digit-preparation machine. -/
theorem prepared_program_correct (n w a d : Nat) (bs : List Bool) (acc : List Cell) :
    eval (value n w a d (3*bs.length+3) (3*bs.length+2)
      (76*bs.length+bs.count true+76)) program acc =
      (Cell.delim :: List.replicate (d+(76*bs.length+bs.count true+76)) Cell.mark) ++
      (Cell.delim :: List.replicate (n+w+a+1+(3*bs.length+2)) Cell.mark) ++
      (Cell.delim :: List.replicate (a+(3*bs.length+3)) Cell.mark) ++
      (Cell.delim :: List.replicate w Cell.mark) ++ acc :=
  program_correct _ _ _ _ _ _ _ _

theorem program_correct_encoding (n w a d ai oi di : Nat) :
    eval (value n w a d ai oi di) program [] =
      ((ShiBQP.encNat w ++ ShiBQP.encNat (a+ai) ++
        ShiBQP.encNat (n+w+a+1+oi) ++ ShiBQP.encNat (d+di)).map bit).reverse := by
  rw [program_correct]
  simp [ShiBQP.encNat, bit, List.map_append, List.reverse_append, List.append_assoc]

end ShiTMCenteringHeader

namespace ShiTMCenteringBody
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev Label := ShiTMCenteringPayload.Label ⊕ ShiTMCenteringPreparedSuffix.Label

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl (.broadcast 0 .copy)))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringPayload.machine l)
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMCenteringPreparedSuffix.machine l)

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMCenteringPayload.source
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl .copy
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def cost (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) : Nat :=
  payload.length+2 + ShiTMCenteringPreparedSuffix.cost n w a out bs

/-- Assemble the original body followed by the centering suffix. The supplied
header remains at the front of the eventual forward encoding. -/
theorem body_run (n w a : Nat) (out : Fin (n+(w+(a+1))))
    (bs payload header : List Bool) (v : Sig) (S : ∀ j, List (TopGam j))
    (hn : S (ShiTMCenteringBroadcast.source 0) = List.replicate n Cell.mark)
    (hw : S (ShiTMCenteringBroadcast.source 1) = List.replicate w Cell.mark)
    (ha : S (ShiTMCenteringBroadcast.source 2) = List.replicate a Cell.mark)
    (ho : S ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark)
    (hz : ∀ i, S (E.wire i) = []) (hs : S E.scratch = [])
    (hd : S ShiTMCenteringCoinLoop.digits = bs.reverse.map bit)
    (hp : S ShiTMCenteringPayload.source = payload.map bit)
    (hh : S E.output = (header.map bit).reverse) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost n w a out bs payload] (some ⟨some (.inl .copy), v, S⟩) =
        some ⟨some (.inr (.inr ShiTMCenteringSuffix.terminal)), v', U⟩
      ∧ U E.output =
        ((header ++ payload ++ ((centeringSuffix (n+(w+(a+1))) out bs).map
          ShiBQP.encLayer).flatten).map bit).reverse
      ∧ U E.scratch = []
      ∧ U ShiTMCenteringPayload.source = []
      ∧ ∀ j, j ≠ E.output → j ≠ ShiTMCenteringPayload.source →
          j ≠ ShiTMCenteringCoinLoop.digits → (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, ar, ap, ao, af⟩ := ShiTMCenteringPayload.copy_after_header payload header v S hp hh
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringPayload.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridge : run^[1] (some ⟨some (.inl .finished), none, A⟩) =
      some ⟨some (.inr (.inl (.broadcast 0 .copy))), none, A⟩ := rfl
  have an := (af _ (by decide) (by decide)).trans hn
  have aw := (af _ (by decide) (by decide)).trans hw
  have aa := (af _ (by decide) (by decide)).trans ha
  have aout := (af _ (by decide) (by decide)).trans ho
  have az : ∀ i, A (E.wire i) = [] := by
    intro i
    rw [af _ (by fin_cases i <;> decide) (ShiTMCenteringSelector.wire_ne_output i), hz]
  have ascratch := (af _ (by decide) (by decide)).trans hs
  have ad := (af _ (by decide) (by decide)).trans hd
  obtain ⟨U, u, ur, uo, us, uf⟩ := ShiTMCenteringPreparedSuffix.prepared_suffix_run
    n w a out bs none A an aw aa aout az ascratch ad
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringPreparedSuffix.machine machine Sum.inr
    (.inr ShiTMCenteringSuffix.terminal) rfl (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, u, ?_, ?_, us, ?_, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridge
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lu
    simpa only [cost, Nat.add_assoc, show 1+1=2 from rfl, ShiTMSubroutine.cfg, Option.map_some] using h2
  · rw [uo, ao]
    simp only [List.map_append, List.reverse_append]
  · rw [uf _ (by decide) (by decide) (by intro i; fin_cases i <;> decide), ap]
  · intro j hjo hjp hjd hjw
    rw [uf j hjo hjd hjw, af j hjp hjo]

theorem cost_le (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    cost n w a out bs payload ≤
      payload.length + bs.length*(500*(n+w+a+3*bs.length+4)+1003) +
      503*(n+w+a+3*bs.length+4)+4*(n+w+a)+1025 := by
  have h := ShiTMCenteringPreparedSuffix.cost_le n w a out bs
  unfold cost
  omega

end ShiTMCenteringBody

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringPayload.finiteMachine,
      ``ShiTMCenteringCoreCopy.field_run, ``ShiTMCenteringPayload.copy_run, ``ShiTMCenteringPayload.copy_after_header,
      ``ShiTMCenteringHeader.program_correct, ``ShiTMCenteringHeader.prepared_program_correct,
      ``ShiTMCenteringHeader.program_correct_encoding, ``ShiTMCenteringBody.finiteMachine,
      ``ShiTMCenteringBody.body_run, ``ShiTMCenteringBody.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-assembly axiom {ax} in {name}"
    logInfo m!"CENTERING_ASSEMBLY_CHECKED {name}; axioms {axioms}"
