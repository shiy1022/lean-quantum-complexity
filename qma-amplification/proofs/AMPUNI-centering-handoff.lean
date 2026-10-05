import «AMPUNI-centering-selector-emitter»
import «AMPUNI-piece-entry-param-restore»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringHandoff
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E

abbrev retained : TopK := .inr 3
inductive Control where
  | clear | move (second : Bool)
  deriving DecidableEq, Fintype
abbrev Label := Control ⊕ ShiTMPieceEntry.EntryLabel
abbrev start : Label := .inl .clear
abbrev terminal : Label := .inr (.inr .done)
def source (b : Bool) : Fin 4 := if b then 1 else 2
def dest (b : Bool) : Fin 4 := if b then 2 else 3
def next (b : Bool) : Label := if b then .inr (.inr .copy) else .inl (.move true)

theorem source_ne_dest (b : Bool) : E.wire (source b) ≠ E.wire (dest b) := by
  cases b <;> decide

def machine : Label → Stmt TopGam Label Sig
  | .inl .clear => .pop (E.wire 3) pop (.branch isSome
      (.goto (fun _ => start)) (.goto (fun _ => .inl (.move false))))
  | .inl (.move b) => .pop (E.wire (source b)) pop (.branch isSome
      (.push (E.wire (dest b)) (cst Cell.mark) (.goto (fun _ => .inl (.move b))))
      (.goto (fun _ => next b)))
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMPieceEntry.machineAt 3 5 l)

def run := ShiTMSubroutine.run machine

theorem clear_run (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (E.wire 3) = List.replicate n Cell.mark) :
    run^[n+1] (some ⟨some start, v, S⟩) =
      some ⟨some (.inl (.move false)), none, Function.update S (E.wire 3) []⟩ := by
  induction n generalizing v S with
  | zero =>
    have he : S (E.wire 3) = [] := by simpa using hs
    simp [run, ShiTMSubroutine.run, machine, start, step, stepAux, he, pop, isSome]
  | succ n ih =>
    have hm : S (E.wire 3) = Cell.mark :: List.replicate n Cell.mark := by
      simpa [List.replicate_succ] using hs
    have hfirst : run (some ⟨some start, v, S⟩) =
        some ⟨some start, some Cell.mark,
          Function.update S (E.wire 3) (List.replicate n Cell.mark)⟩ := by
      simp [run, ShiTMSubroutine.run, machine, start, step, stepAux, hm, pop, isSome]
    rw [Function.iterate_succ_apply, hfirst]
    simpa using ih (some Cell.mark) (Function.update S (E.wire 3) (List.replicate n Cell.mark)) (by simp)

theorem move_run (b : Bool) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (E.wire (source b)) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.inl (.move b)), v, S⟩) =
        some ⟨some (next b), none, U⟩
      ∧ U (E.wire (source b)) = []
      ∧ U (E.wire (dest b)) = List.replicate n Cell.mark ++ S (E.wire (dest b))
      ∧ ∀ j, j ≠ E.wire (source b) → j ≠ E.wire (dest b) → U j = S j := by
  have hsd := source_ne_dest b
  induction n generalizing v S with
  | zero =>
    have he : S (E.wire (source b)) = [] := by simpa using hs
    refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
    have hm : S (E.wire (source b)) = Cell.mark :: List.replicate n Cell.mark := by
      simpa [List.replicate_succ] using hs
    let T := Function.update (Function.update S (E.wire (source b)) (List.replicate n Cell.mark))
      (E.wire (dest b)) (Cell.mark :: S (E.wire (dest b)))
    have hfirst : run (some ⟨some (.inl (.move b)), v, S⟩) =
        some ⟨some (.inl (.move b)), some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hm, pop, isSome, cst, T, hsd.symm]
    obtain ⟨U, hr, hu, hd, hf⟩ := ih (some Cell.mark) T (by simp [T, hsd])
    refine ⟨U, ?_, hu, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact hr
    · rw [hd]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S (E.wire (dest b)))
    · intro j hjs hjd
      rw [hf j hjs hjd]
      simp [T, hjs, hjd]

/-- Preserving copy of the retained original output index into the now-empty
second wire register. The marks-only entry avoids introducing a delimiter. -/
theorem copy_run (out : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (ho : S retained = List.replicate out Cell.mark) (hs : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*out+2] (some ⟨some (.inr (.inr .copy)), v, S⟩) =
        some ⟨some terminal, none, U⟩
      ∧ U retained = S retained
      ∧ U (E.wire 1) = List.replicate out Cell.mark ++ S (E.wire 1)
      ∧ U E.scratch = []
      ∧ ∀ j, j ≠ E.wire 1 → U j = S j := by
  obtain ⟨T, ht, hto, htd, hts, htf⟩ :=
    ShiTMPieceEntry.copy_marks_run_at 3 5 (by decide) out v S ho
  have hts' : T E.scratch = List.replicate out Cell.mark := by simpa [hs] using hts
  obtain ⟨U, hu, hus, huo, huf⟩ := ShiTMPieceEntry.restore_marks_run_at 3 5 out none T hts'
  have hr := ShiTMFanout.iterTwo (ShiTMPieceEntry.runAt 3 5) _ _ _ _ _ ht hu
  have hc : (out+1)+(out+1) = 2*out+2 := by omega
  rw [hc] at hr
  have hl := ShiTMSubroutine.run_to_terminal (ShiTMPieceEntry.machineAt 3 5) machine
    Sum.inr (.inr .done) rfl (fun _ _ => rfl) _ _ _ rfl hr
  have hret : U retained = S retained := by rw [huo, hto]; simpa using ho.symm
  refine ⟨U, hl, hret, ?_, hus, ?_⟩
  · rw [huf _ (by decide) (by decide)]
    exact htd
  · intro j hj
    by_cases he : j = retained
    · subst j; exact hret
    by_cases he' : j = E.scratch
    · subst j; exact hus.trans hs.symm
    rw [huf j he he', htf j he hj he']

/-- Complete register handoff after k coin digits. -/
theorem handoff_run (m k out : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hw : ∀ i, S (E.wire i) = List.replicate (ShiTMCenteringCoinLoop.coinValues m k i) Cell.mark)
    (ho : S retained = List.replicate out Cell.mark) (hs : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[3*(m+3*k)+2*out+10] (some ⟨some start, v, S⟩) =
        some ⟨some terminal, none, U⟩
      ∧ (∀ i, U (E.wire i) = List.replicate (![m+3*k+1,out,m+3*k,m+3*k+2] i) Cell.mark)
      ∧ U E.scratch = []
      ∧ ∀ j, j ≠ E.wire 1 → j ≠ E.wire 2 → j ≠ E.wire 3 → U j = S j := by
  let A := Function.update S (E.wire 3) []
  have ha := clear_run (m+3*k+3) v S (hw 3)
  obtain ⟨B, hb, hb2, hb3, hbf⟩ := move_run false (m+3*k+2) none A (by
    simp [A, source, hw, ShiTMCenteringCoinLoop.coinValues])
  obtain ⟨C, hc, hc1, hc2, hcf⟩ := move_run true (m+3*k) none B (by
    rw [hbf _ (by decide) (by decide)]
    simp [A, source, hw, ShiTMCenteringCoinLoop.coinValues])
  change B (E.wire 2) = [] at hb2
  change B (E.wire 3) = List.replicate (m+3*k+2) Cell.mark ++ A (E.wire 3) at hb3
  change C (E.wire 1) = [] at hc1
  change C (E.wire 2) = List.replicate (m+3*k) Cell.mark ++ B (E.wire 2) at hc2
  have hcf' : ∀ j, j ≠ E.wire 1 → j ≠ E.wire 2 → j ≠ E.wire 3 → C j = S j := by
    intro j hj1 hj2 hj3
    rw [hcf j hj1 hj2, hbf j hj2 hj3]
    simp [A, hj3]
  obtain ⟨U, hu, huo, hu1, hus, huf⟩ := copy_run out none C
    ((hcf' _ (by decide) (by decide) (by decide)).trans ho)
    ((hcf' _ (by decide) (by decide) (by decide)).trans hs)
  refine ⟨U, ?_, ?_, hus, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ ha hb
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hc
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 hu
    have he : ((m+3*k+3+1)+(m+3*k+2+1))+(m+3*k+1)+(2*out+2) =
        3*(m+3*k)+2*out+10 := by omega
    simpa only [he] using h3
  · intro i
    fin_cases i
    · rw [huf _ (by decide), hcf' _ (by decide) (by decide) (by decide), hw]
      rfl
    · simpa [hc1] using hu1
    · change U (E.wire 2) = List.replicate (m+3*k) Cell.mark
      rw [huf _ (by decide), hc2, hb2, List.append_nil]
    · change U (E.wire 3) = List.replicate (m+3*k+2) Cell.mark
      rw [huf _ (by decide), hcf _ (by decide) (by decide), hb3]
      simp [A]
  · intro j hj1 hj2 hj3
    exact (huf j hj1).trans (hcf' j hj1 hj2 hj3)

end ShiTMCenteringHandoff

open Lean Elab Command in
run_cmd do
  let name := ``ShiTMCenteringHandoff.handoff_run
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected handoff axiom {ax}"
  logInfo m!"CENTERING_HANDOFF_CHECKED {name}; axioms {axioms}"

namespace ShiTMCenteringSuffix
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E

abbrev Label := ShiTMCenteringCoinLoop.Label ⊕
  (ShiTMCenteringHandoff.Label ⊕ ShiTMCenteringSelector.Label)
abbrev start : Label := .inl .dispatch
abbrev terminal : Label := .inr (.inr .finished)

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl ShiTMCenteringHandoff.start))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringCoinLoop.machine l)
  | .inr (.inl (.inr (.inr .done))) => .goto (fun _ => .inr (.inr (.dispatch 0)))
  | .inr (.inl l) => ShiTMSubroutine.stmt (fun l => .inr (.inl l)) (ShiTMCenteringHandoff.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt (fun l => .inr (.inr l)) (ShiTMCenteringSelector.machine l)

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMCenteringCoinLoop.digits
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := start
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def cost (m : Nat) (out : Fin m) (bs : List Bool) : Nat :=
  ShiTMCenteringCoinLoop.cost (ShiTMCenteringCoinLoop.coinValues m 0) bs.reverse + 1 +
    (3*(m+3*bs.length)+2*out.val+10) + 1 +
    (ShiTMCenteringSelector.scheduleCost (fun i => (centeringWires m bs.length out i).val)
      ShiTMCenteringSelector.program + 1)

/-- Concrete emission of the complete centering suffix, with the original
output index retained and all unrelated non-working registers preserved. -/
theorem typed_suffix_run (m : Nat) (out : Fin m) (bs : List Bool)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hw : ∀ i, S (E.wire i) = List.replicate (ShiTMCenteringCoinLoop.coinValues m 0 i) Cell.mark)
    (ho : S ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark)
    (hs : S E.scratch = []) (hd : S ShiTMCenteringCoinLoop.digits = bs.reverse.map bit) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost m out bs] (some ⟨some start, v, S⟩) =
        some ⟨some terminal, v', U⟩
      ∧ U E.output = ((((centeringSuffix m out bs).map ShiBQP.encLayer).flatten).map bit).reverse ++ S E.output
      ∧ U ShiTMCenteringHandoff.retained = S ShiTMCenteringHandoff.retained
      ∧ U E.scratch = []
      ∧ ∀ j, j ≠ E.output → j ≠ ShiTMCenteringCoinLoop.digits →
          (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, a, ha, hao, had, haw, haf⟩ :=
    ShiTMCenteringCoinLoop.typed_coinCircuit_run (N := m+(3*bs.length+3)) m bs (by omega) v S hw hs hd
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringCoinLoop.machine machine
    Sum.inl .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim)
    _ _ _ rfl ha
  have haRet : A ShiTMCenteringHandoff.retained = S ShiTMCenteringHandoff.retained :=
    haf _ (by decide) (by decide) (by intro i; fin_cases i <;> decide)
  have haScratch : A E.scratch = [] :=
    (haf _ (by decide) (by decide) (fun i => (ShiTMCenteringSelector.wire_ne_scratch i).symm)).trans hs
  have ba : run^[1] (some ⟨some (.inl .finished), a, A⟩) =
      some ⟨some (.inr (.inl ShiTMCenteringHandoff.start)), a, A⟩ := rfl
  obtain ⟨B, hb, hbw, hbs, hbf⟩ := ShiTMCenteringHandoff.handoff_run m bs.length out.val a A haw
    (haRet.trans ho) haScratch
  have lb := ShiTMSubroutine.run_to_terminal ShiTMCenteringHandoff.machine machine
    (fun l => .inr (.inl l)) ShiTMCenteringHandoff.terminal rfl (by
      intro l hl
      cases l with
      | inl c => cases c <;> rfl
      | inr l => cases l with
        | inl t => rfl
        | inr c => cases c <;> first | rfl | exact (hl rfl).elim)
    _ _ _ rfl hb
  have bb : run^[1] (some ⟨some (.inr (.inl ShiTMCenteringHandoff.terminal)), none, B⟩) =
      some ⟨some (.inr (.inr (.dispatch 0))), none, B⟩ := rfl
  have hbw' : ∀ i, B (E.wire i) = List.replicate (centeringWires m bs.length out i).val Cell.mark := by
    intro i
    fin_cases i <;> exact hbw _
  obtain ⟨U, u, hu, huo, huf⟩ := ShiTMCenteringSelector.typed_selector_run
    (centeringWires m bs.length out) (centeringWires_injective m bs.length out) none B hbw' hbs
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringSelector.machine machine
    (fun l => .inr (.inr l)) .finished rfl (fun _ _ => rfl) _ _ _ rfl hu
  have hfinal : ∀ j, j ≠ E.output → j ≠ ShiTMCenteringCoinLoop.digits →
      (∀ i, j ≠ E.wire i) → U j = S j := by
    intro j hjo hjd hjw
    rw [huf j hjo, hbf j (hjw 1) (hjw 2) (hjw 3), haf j hjo hjd hjw]
  refine ⟨U, u, ?_, ?_, ?_, ?_, hfinal⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la ba
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lb
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 bb
    exact ShiTMFanout.iterTwo run _ _ _ _ _ h3 lu
  · rw [huo, hbf _ (by decide) (by decide) (by decide), hao]
    simp [centeringSuffix, List.map_append, List.flatten_append, List.reverse_append, List.append_assoc]
  · exact hfinal _ (by decide) (by decide) (by intro i; fin_cases i <;> decide)
  · exact (hfinal _ (by decide) (by decide)
      (fun i => (ShiTMCenteringSelector.wire_ne_scratch i).symm)).trans hs

theorem cost_le (m : Nat) (out : Fin m) (bs : List Bool) :
    cost m out bs ≤
      bs.length*(500*(m+3*bs.length+3)+1003)+503*(m+3*bs.length+3)+2*m+1010 := by
  have hl := ShiTMCenteringCoinLoop.typed_coinCircuit_cost_le m bs
  have hs := ShiTMCenteringSelector.typed_selector_cost_le (centeringWires m bs.length out)
  have ho := out.isLt
  dsimp only [cost]
  omega

end ShiTMCenteringSuffix

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringSuffix.finiteMachine,
      ``ShiTMCenteringSuffix.typed_suffix_run,
      ``ShiTMCenteringSuffix.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-suffix-machine axiom {ax} in {name}"
    logInfo m!"CENTERING_SUFFIX_MACHINE_CHECKED {name}; axioms {axioms}"
