import «AMPUNI-centering-handoff»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringBroadcast
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev source (h : Fin 3) : TopK := .inr (Fin.castAdd 1 h)

theorem source_ne_wire (h : Fin 3) (i : Fin 4) : source h ≠ E.wire i := by intro he; cases he

def addMarks (S : ∀ j, List (TopGam j)) : ∀ j, List (TopGam j) :=
  Function.update (Function.update (Function.update (Function.update S
    (E.wire 0) (Cell.mark :: S (E.wire 0)))
    (E.wire 1) (Cell.mark :: S (E.wire 1)))
    (E.wire 2) (Cell.mark :: S (E.wire 2)))
    (E.wire 3) (Cell.mark :: S (E.wire 3))

theorem addMarks_wire (S : ∀ j, List (TopGam j)) (i : Fin 4) :
    addMarks S (E.wire i) = Cell.mark :: S (E.wire i) := by
  fin_cases i <;> simp [addMarks, E.wire]

theorem addMarks_frame (S : ∀ j, List (TopGam j)) (j : TopK)
    (hj : ∀ i, j ≠ E.wire i) : addMarks S j = S j := by simp [addMarks, hj]

inductive Label where
  | copy | restore | finished
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList [.copy, .restore, .finished]
  (by intro l; cases l <;> simp)

def machine (h : Fin 3) : Label → Stmt TopGam Label Sig
  | .copy => .pop (source h) pop (.branch isSome
      (.push (E.wire 0) (cst Cell.mark) (.push (E.wire 1) (cst Cell.mark)
      (.push (E.wire 2) (cst Cell.mark) (.push (E.wire 3) (cst Cell.mark)
      (.push E.scratch (cst Cell.mark) (.goto (fun _ => .copy)))))))
      (.goto (fun _ => .restore)))
  | .restore => .pop E.scratch pop (.branch isSome
      (.push (source h) (cst Cell.mark) (.goto (fun _ => .restore)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run (h : Fin 3) := ShiTMSubroutine.run (machine h)

theorem copy_run (h : Fin 3) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (source h) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      (run h)^[n+1] (some ⟨some (.copy), v, S⟩) = some ⟨some (.restore), none, U⟩
      ∧ U (source h) = []
      ∧ (∀ i, U (E.wire i) = List.replicate n Cell.mark ++ S (E.wire i))
      ∧ U E.scratch = List.replicate n Cell.mark ++ S E.scratch
      ∧ ∀ j, j ≠ source h → j ≠ E.scratch → (∀ i, j ≠ E.wire i) → U j = S j := by
  induction n generalizing v S with
  | zero =>
    have he : S (source h) = [] := by simpa using hs
    refine ⟨S, ?_, he, by simp, by simp, by intro j _ _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
    have hm : S (source h) = Cell.mark :: List.replicate n Cell.mark := by simpa [List.replicate_succ] using hs
    let T := Function.update (addMarks (Function.update S (source h) (List.replicate n Cell.mark)))
      E.scratch (Cell.mark :: S E.scratch)
    have hfirst : run h (some ⟨some (.copy), v, S⟩) =
        some ⟨some (.copy), some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hm, pop, isSome,
        cst, T, addMarks, E.wire, E.scratch, source]
    have htSrc : T (source h) = List.replicate n Cell.mark := by
      simp [T, addMarks, E.wire, E.scratch, source]
    have htWire (i : Fin 4) : T (E.wire i) = Cell.mark :: S (E.wire i) := by
      dsimp only [T]
      rw [Function.update_of_ne (ShiTMCenteringSelector.wire_ne_scratch i), addMarks_wire,
        Function.update_of_ne (source_ne_wire h i).symm]
    obtain ⟨U, hr, hu, hw, ht, hf⟩ := ih (some Cell.mark) T htSrc
    refine ⟨U, ?_, hu, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact hr
    · intro i
      rw [hw i, htWire i]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S (E.wire i))
    · rw [ht]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S E.scratch)
    · intro j hjh hjs hjw
      rw [hf j hjh hjs hjw]
      simp only [T, Function.update_of_ne hjs, addMarks_frame _ j hjw, Function.update_of_ne hjh]

theorem restore_run (h : Fin 3) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
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
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hm, pop, isSome, cst, T, E.scratch, source]
    obtain ⟨U, hr, hu, hh, hf⟩ := ih (some Cell.mark) T (by simp [T, E.scratch, source])
    refine ⟨U, ?_, hu, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact hr
    · rw [hh]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc n (S (source h))
    · intro j hjh hjs
      rw [hf j hjh hjs]
      simp [T, hjh, hjs]

/-- Add the retained field to all four counters and restore the retained field. -/
theorem broadcast_run (h : Fin 3) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (source h) = List.replicate n Cell.mark) (ht : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      (run h)^[2*n+2] (some ⟨some (.copy), v, S⟩) = some ⟨some (.finished), none, U⟩
      ∧ (∀ i, U (E.wire i) = List.replicate n Cell.mark ++ S (E.wire i))
      ∧ ∀ j, (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, ha, hah, haw, has, haf⟩ := copy_run h n v S hs
  obtain ⟨U, hu, hus, huh, huf⟩ := restore_run h n none A (by simpa [ht] using has)
  refine ⟨U, ?_, ?_, ?_⟩
  · have hr := ShiTMFanout.iterTwo (run h) _ _ _ _ _ ha hu
    have he : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [he] using hr
  · intro i
    rw [huf _ (source_ne_wire h i).symm (ShiTMCenteringSelector.wire_ne_scratch i), haw]
  · intro j hjw
    by_cases hjh : j = source h
    · subst j; rw [huh, hah, List.append_nil, hs]
    by_cases hjs : j = E.scratch
    · subst j; exact hus.trans ht.symm
    rw [huf j hjh hjs, haf j hjh hjs hjw]

end ShiTMCenteringBroadcast

namespace ShiTMCenteringPrepare
open ShiTMLayoutMachine ShiTMRetainedTop
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E

inductive Label where
  | broadcast (h : Fin 3) (l : ShiTMCenteringBroadcast.Label) | offset | finished
  deriving DecidableEq, Fintype

def offsets : Fin 4 → Nat := ![2,1,3,4]

def offsetStacks (S : ∀ j, List (TopGam j)) : ∀ j, List (TopGam j) :=
  Function.update (Function.update (Function.update (Function.update S
    (E.wire 0) (List.replicate 2 Cell.mark ++ S (E.wire 0)))
    (E.wire 1) (List.replicate 1 Cell.mark ++ S (E.wire 1)))
    (E.wire 2) (List.replicate 3 Cell.mark ++ S (E.wire 2)))
    (E.wire 3) (List.replicate 4 Cell.mark ++ S (E.wire 3))

def offsetStmt : Stmt TopGam Label Sig :=
  .push (E.wire 0) (cst Cell.mark) (.push (E.wire 0) (cst Cell.mark)
  (.push (E.wire 1) (cst Cell.mark)
  (.push (E.wire 2) (cst Cell.mark) (.push (E.wire 2) (cst Cell.mark) (.push (E.wire 2) (cst Cell.mark)
  (.push (E.wire 3) (cst Cell.mark) (.push (E.wire 3) (cst Cell.mark) (.push (E.wire 3) (cst Cell.mark)
  (.push (E.wire 3) (cst Cell.mark) (.goto (fun _ => .finished)))))))))))

def machine : Label → Stmt TopGam Label Sig
  | .broadcast h .finished => .goto (fun _ =>
      if h.val = 0 then .broadcast 1 .copy else if h.val = 1 then .broadcast 2 .copy else .offset)
  | .broadcast h l => ShiTMSubroutine.stmt (Label.broadcast h) (ShiTMCenteringBroadcast.machine h l)
  | .offset => offsetStmt
  | .finished => .halt

def run := ShiTMSubroutine.run machine

theorem offsetStacks_wire (S : ∀ j, List (TopGam j)) (i : Fin 4) :
    offsetStacks S (E.wire i) = List.replicate (offsets i) Cell.mark ++ S (E.wire i) := by
  fin_cases i <;> simp [offsetStacks, offsets, E.wire]

theorem offsetStacks_frame (S : ∀ j, List (TopGam j)) (j : TopK)
    (hj : ∀ i, j ≠ E.wire i) : offsetStacks S j = S j := by simp [offsetStacks, hj]

theorem offset_run (v : Sig) (S : ∀ j, List (TopGam j)) :
    run^[1] (some ⟨some .offset, v, S⟩) = some ⟨some .finished, v, offsetStacks S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, offsetStmt, offsetStacks, E.wire,
    step, stepAux, cst, List.replicate_succ]

theorem field_run (h : Fin 3) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (ShiTMCenteringBroadcast.source h) = List.replicate n Cell.mark)
    (ht : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+2] (some ⟨some (.broadcast h .copy), v, S⟩) =
        some ⟨some (.broadcast h .finished), none, U⟩
      ∧ (∀ i, U (E.wire i) = List.replicate n Cell.mark ++ S (E.wire i))
      ∧ ∀ j, (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨U, hr, hw, hf⟩ := ShiTMCenteringBroadcast.broadcast_run h n v S hs ht
  have hl := ShiTMSubroutine.run_to_terminal (ShiTMCenteringBroadcast.machine h) machine
    (Label.broadcast h) .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim)
    _ _ _ rfl hr
  exact ⟨U, hl, hw, hf⟩

/-- Prepare all four initial coin-wire counters from retained n, witness and
ancilla counts. Every source field, digit and output stack is preserved. -/
theorem prepare_run (n w a : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hn : S (ShiTMCenteringBroadcast.source 0) = List.replicate n Cell.mark)
    (hw : S (ShiTMCenteringBroadcast.source 1) = List.replicate w Cell.mark)
    (ha : S (ShiTMCenteringBroadcast.source 2) = List.replicate a Cell.mark)
    (hz : ∀ i, S (E.wire i) = []) (hs : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*(n+w+a)+10] (some ⟨some (.broadcast 0 .copy), v, S⟩) =
        some ⟨some .finished, none, U⟩
      ∧ (∀ i, U (E.wire i) =
          List.replicate (ShiTMCenteringCoinLoop.coinValues (n+(w+(a+1))) 0 i) Cell.mark)
      ∧ ∀ j, (∀ i, j ≠ E.wire i) → U j = S j := by
  have hnw (h : Fin 3) (i : Fin 4) := ShiTMCenteringBroadcast.source_ne_wire h i
  have hsw (i : Fin 4) := (ShiTMCenteringSelector.wire_ne_scratch i).symm
  obtain ⟨A, ar, aw, af⟩ := field_run 0 n v S hn hs
  have ab : run^[1] (some ⟨some (.broadcast 0 .finished), none, A⟩) =
      some ⟨some (.broadcast 1 .copy), none, A⟩ := by
    simp [run, ShiTMSubroutine.run, machine, step, stepAux]
  obtain ⟨B, br, bw, bf⟩ := field_run 1 w none A ((af _ (hnw 1)).trans hw) ((af _ hsw).trans hs)
  have bb : run^[1] (some ⟨some (.broadcast 1 .finished), none, B⟩) =
      some ⟨some (.broadcast 2 .copy), none, B⟩ := by
    simp [run, ShiTMSubroutine.run, machine, step, stepAux]
  obtain ⟨C, cr, cw, cf⟩ := field_run 2 a none B
    ((bf _ (hnw 2)).trans ((af _ (hnw 2)).trans ha))
    ((bf _ hsw).trans ((af _ hsw).trans hs))
  have cb : run^[1] (some ⟨some (.broadcast 2 .finished), none, C⟩) =
      some ⟨some .offset, none, C⟩ := by simp [run, ShiTMSubroutine.run, machine, step, stepAux]
  refine ⟨offsetStacks C, ?_, ?_, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ ar ab
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 br
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 bb
    have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h3 cr
    have h5 := ShiTMFanout.iterTwo run _ _ _ _ _ h4 cb
    have h6 := ShiTMFanout.iterTwo run _ _ _ _ _ h5 (offset_run none C)
    have he : (((((2*n+2)+1)+(2*w+2))+1)+(2*a+2))+1+1 = 2*(n+w+a)+10 := by omega
    simpa only [he] using h6
  · intro i
    rw [offsetStacks_wire, cw, bw, aw, hz, List.append_nil,
      ← List.replicate_add, ← List.replicate_add, ← List.replicate_add]
    apply congrArg (fun t => List.replicate t Cell.mark)
    fin_cases i <;> simp [offsets, ShiTMCenteringCoinLoop.coinValues] <;> omega
  · intro j hj
    rw [offsetStacks_frame _ _ hj, cf j hj, bf j hj, af j hj]

end ShiTMCenteringPrepare

open Lean Elab Command in
run_cmd do
  let name := ``ShiTMCenteringPrepare.prepare_run
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected register-preparation axiom {ax}"
  logInfo m!"CENTERING_REGISTERS_CHECKED {name}; axioms {axioms}"

namespace ShiTMCenteringPreparedSuffix
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev Label := ShiTMCenteringPrepare.Label ⊕ ShiTMCenteringSuffix.Label

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr ShiTMCenteringSuffix.start)
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringPrepare.machine l)
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMCenteringSuffix.machine l)

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMCenteringCoinLoop.digits
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl (.broadcast 0 .copy)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def cost (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool) : Nat :=
  2*(n+w+a)+11 + ShiTMCenteringSuffix.cost (n+(w+(a+1))) out bs

/-- Generate the complete suffix from retained verifier size fields and zeroed
working counters; no precomputed wire-index registers are assumed. -/
theorem prepared_suffix_run (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hn : S (ShiTMCenteringBroadcast.source 0) = List.replicate n Cell.mark)
    (hw : S (ShiTMCenteringBroadcast.source 1) = List.replicate w Cell.mark)
    (ha : S (ShiTMCenteringBroadcast.source 2) = List.replicate a Cell.mark)
    (ho : S ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark)
    (hz : ∀ i, S (E.wire i) = []) (hs : S E.scratch = [])
    (hd : S ShiTMCenteringCoinLoop.digits = bs.reverse.map bit) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost n w a out bs] (some ⟨some (.inl (.broadcast 0 .copy)), v, S⟩) =
        some ⟨some (.inr ShiTMCenteringSuffix.terminal), v', U⟩
      ∧ U E.output =
        ((((centeringSuffix (n+(w+(a+1))) out bs).map ShiBQP.encLayer).flatten).map bit).reverse ++ S E.output
      ∧ U E.scratch = []
      ∧ ∀ j, j ≠ E.output → j ≠ ShiTMCenteringCoinLoop.digits →
          (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, ar, aw, af⟩ := ShiTMCenteringPrepare.prepare_run n w a v S hn hw ha hz hs
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringPrepare.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridge : run^[1] (some ⟨some (.inl .finished), none, A⟩) =
      some ⟨some (.inr ShiTMCenteringSuffix.start), none, A⟩ := rfl
  have haOut := af E.output (fun i => (ShiTMCenteringSelector.wire_ne_output i).symm)
  obtain ⟨U, u, ur, uo, uret, us, uf⟩ := ShiTMCenteringSuffix.typed_suffix_run
    (n+(w+(a+1))) out bs none A aw
    ((af _ (by intro i; fin_cases i <;> decide)).trans ho)
    ((af _ (fun i => (ShiTMCenteringSelector.wire_ne_scratch i).symm)).trans hs)
    ((af _ (fun i => (ShiTMCenteringCoinLoop.wire_ne_digits i).symm)).trans hd)
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringSuffix.machine machine Sum.inr
    ShiTMCenteringSuffix.terminal rfl (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, u, ?_, uo.trans (by rw [haOut]), us, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridge
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lu
    have he : (2*(n+w+a)+10)+1 = 2*(n+w+a)+11 := by omega
    simpa only [cost, he, ShiTMSubroutine.cfg, Option.map_some] using h2
  · intro j hjo hjd hjw
    exact (uf j hjo hjd hjw).trans (af j hjw)

theorem cost_le (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool) :
    cost n w a out bs ≤
      bs.length*(500*(n+w+a+3*bs.length+4)+1003)+
        503*(n+w+a+3*bs.length+4)+4*(n+w+a)+1023 := by
  have h := ShiTMCenteringSuffix.cost_le (n+(w+(a+1))) out bs
  dsimp only [cost]
  have he : n+(w+(a+1))+3*bs.length+3 = n+w+a+3*bs.length+4 := by omega
  rw [he] at h
  omega

end ShiTMCenteringPreparedSuffix

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringPreparedSuffix.finiteMachine,
      ``ShiTMCenteringPreparedSuffix.prepared_suffix_run,
      ``ShiTMCenteringPreparedSuffix.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected prepared-suffix axiom {ax} in {name}"
    logInfo m!"CENTERING_PREPARED_SUFFIX_CHECKED {name}; axioms {axioms}"

namespace ShiTMCenteringDigitPrepare
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev bits : TopK := .inl (.inl (9 : Fin 14))
abbrev digits := ShiTMCenteringCoinLoop.digits
abbrev ancExtra : TopK := .inl (.inl (0 : Fin 14))
abbrev depthExtra : TopK := .inl (.inl (1 : Fin 14))
abbrev outExtra : TopK := .inl (.inl (2 : Fin 14))
inductive Label where
  | start | scan | finished
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList [.start, .scan, .finished]
  (by intro l; cases l <;> simp)

def pushMarks (k : TopK) (hk : TopGam k = Cell) (n : Nat)
    (q : Stmt TopGam Label Sig) : Stmt TopGam Label Sig :=
  match n with
  | 0 => q
  | n+1 => .push k (fun _ => hk.symm ▸ Cell.mark) (pushMarks k hk n q)

theorem pushMarks_step (k : TopK) (hk : TopGam k = Cell) (n : Nat)
    (q : Stmt TopGam Label Sig) (v : Sig) (S : ∀ j, List (TopGam j)) :
    stepAux (pushMarks k hk n q) v S =
      stepAux q v (Function.update S k (List.replicate n (hk.symm ▸ Cell.mark) ++ S k)) := by
  induction n generalizing S with
  | zero => simp [pushMarks]
  | succ n ih =>
    simp only [pushMarks, stepAux]
    rw [ih]
    simp [List.replicate_succ', List.append_assoc]

def machine : Label → Stmt TopGam Label Sig
  | .start => pushMarks ancExtra rfl 3 (pushMarks depthExtra rfl 76 (pushMarks outExtra rfl 2
      (.goto (fun _ => .scan))))
  | .scan => .pop bits pop (.branch isSome
      (.push digits ShiTMLayoutMachine.get (pushMarks ancExtra rfl 3 (pushMarks outExtra rfl 3
      (.branch isMark (pushMarks depthExtra rfl 77 (.goto (fun _ => .scan)))
        (pushMarks depthExtra rfl 76 (.goto (fun _ => .scan)))))))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

def layerCount (bs : List Bool) : Nat := 76*bs.length + bs.count true

def result (bs : List Bool) (S : ∀ j, List (TopGam j)) : ∀ j, List (TopGam j) :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    bits []) digits (bs.reverse.map bit ++ S digits))
    ancExtra (List.replicate (3*bs.length) Cell.mark ++ S ancExtra))
    outExtra (List.replicate (3*bs.length) Cell.mark ++ S outExtra))
    depthExtra (List.replicate (layerCount bs) Cell.mark ++ S depthExtra)

theorem scan_run (bs : List Bool) (v : Sig) (S : ∀ j, List (TopGam j))
    (hb : S bits = bs.map bit) :
    run^[bs.length+1] (some ⟨some .scan, v, S⟩) =
      some ⟨some .finished, none, result bs S⟩ := by
  induction bs generalizing v S with
  | nil =>
    have he : S bits = [] := by simpa using hb
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, he, pop, isSome,
      result, layerCount]
    funext j
    by_cases hjb : j = bits
    · subst j; simp [bits, digits, ancExtra, outExtra, depthExtra]
    by_cases hjd : j = digits
    · subst j; simp [bits, digits, ancExtra, outExtra, depthExtra]
    by_cases hja : j = ancExtra
    · subst j; simp [bits, digits, ancExtra, outExtra, depthExtra]
    by_cases hjo : j = outExtra
    · subst j; simp [bits, digits, ancExtra, outExtra, depthExtra]
    by_cases hjt : j = depthExtra
    · subst j; simp [bits, digits, ancExtra, outExtra, depthExtra]
    simp [hjb, hjd, hja, hjo, hjt]
  | cons b bs ih =>
    let T := Function.update (Function.update (Function.update (Function.update (Function.update S
      bits (bs.map bit)) digits (bit b :: S digits))
      ancExtra (List.replicate 3 Cell.mark ++ S ancExtra))
      outExtra (List.replicate 3 Cell.mark ++ S outExtra))
      depthExtra (List.replicate (if b then 77 else 76) Cell.mark ++ S depthExtra)
    have hfirst : run (some ⟨some .scan, v, S⟩) =
        some ⟨some .scan, some (bit b), T⟩ := by
      cases b <;> simp [run, ShiTMSubroutine.run, machine, step, stepAux, hb, pop, isSome,
        isMark, ShiTMLayoutMachine.get, bit, pushMarks_step, T, bits, digits, ancExtra, outExtra, depthExtra]
    have htail : T bits = bs.map bit := by simp [T, bits, digits, ancExtra, outExtra, depthExtra]
    rw [List.length_cons, Function.iterate_succ_apply, hfirst, ih _ T htail]
    have he : result bs T = result (b::bs) S := by
      funext j
      by_cases hjb : j = bits
      · subst j; simp [result, bits, digits, ancExtra, outExtra, depthExtra]
      by_cases hjd : j = digits
      · subst j
        simp [result, T, List.reverse_cons, List.append_assoc,
          bits, digits, ancExtra, outExtra, depthExtra]
      by_cases hja : j = ancExtra
      · subst j
        change List.replicate (3*bs.length) Cell.mark ++ (List.replicate 3 Cell.mark ++ S ancExtra) =
          List.replicate (3*(b::bs).length) Cell.mark ++ S ancExtra
        rw [← List.append_assoc, ← List.replicate_add]
        apply congrArg (fun t => List.replicate t Cell.mark ++ S ancExtra)
        simp only [List.length_cons]; omega
      by_cases hjo : j = outExtra
      · subst j
        change List.replicate (3*bs.length) Cell.mark ++ (List.replicate 3 Cell.mark ++ S outExtra) =
          List.replicate (3*(b::bs).length) Cell.mark ++ S outExtra
        rw [← List.append_assoc, ← List.replicate_add]
        apply congrArg (fun t => List.replicate t Cell.mark ++ S outExtra)
        simp only [List.length_cons]; omega
      by_cases hjt : j = depthExtra
      · subst j
        change List.replicate (layerCount bs) Cell.mark ++
            (List.replicate (if b then 77 else 76) Cell.mark ++ S depthExtra) =
          List.replicate (layerCount (b::bs)) Cell.mark ++ S depthExtra
        rw [← List.append_assoc, ← List.replicate_add]
        apply congrArg (fun t => List.replicate t Cell.mark ++ S depthExtra)
        cases b <;> simp [layerCount] <;> omega
      simp [result, T, hjb, hjd, hja, hjo, hjt]
    rw [he]

/-- Reverse fractional digits for the coin loop while computing the three
exact header increments, including one extra X layer for each true digit. -/
theorem prepare_run (bs : List Bool) (v : Sig) (S : ∀ j, List (TopGam j))
    (hb : S bits = bs.map bit) (hd : S digits = [])
    (ha : S ancExtra = []) (ht : S depthExtra = []) (ho : S outExtra = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[bs.length+2] (some ⟨some .start, v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U digits = bs.reverse.map bit
      ∧ U ancExtra = List.replicate (3*bs.length+3) Cell.mark
      ∧ U depthExtra = List.replicate (76*bs.length+bs.count true+76) Cell.mark
      ∧ U outExtra = List.replicate (3*bs.length+2) Cell.mark
      ∧ U bits = []
      ∧ ∀ j, j ≠ bits → j ≠ digits → j ≠ ancExtra → j ≠ depthExtra → j ≠ outExtra → U j = S j := by
  let T := Function.update (Function.update (Function.update S ancExtra (List.replicate 3 Cell.mark))
    depthExtra (List.replicate 76 Cell.mark)) outExtra (List.replicate 2 Cell.mark)
  have hstart : run^[1] (some ⟨some .start, v, S⟩) = some ⟨some .scan, v, T⟩ := by
    simp [run, ShiTMSubroutine.run, machine, step, pushMarks_step, stepAux, T, ha, ht, ho,
      bits, digits, ancExtra, outExtra, depthExtra]
  have hr := scan_run bs v T (by simpa [T, bits, ancExtra, outExtra, depthExtra] using hb)
  refine ⟨result bs T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := ShiTMFanout.iterTwo run _ _ _ _ _ hstart hr
    have he : 1+(bs.length+1) = bs.length+2 := by omega
    simpa only [he] using h
  · simp [result, T, hd, bits, digits, ancExtra, outExtra, depthExtra]
  · simp [result, T, bits, digits, ancExtra, outExtra, depthExtra, List.replicate_add]
  · change List.replicate (layerCount bs) Cell.mark ++ List.replicate 76 Cell.mark = _
    exact (List.replicate_add _ _ _).symm
  · simp [result, T, bits, digits, ancExtra, outExtra, depthExtra, List.replicate_add]
  · simp [result, bits, digits, ancExtra, outExtra, depthExtra]
  · intro j hjb hjd hja hjt hjo
    simp [result, T, hjb, hjd, hja, hjt, hjo]

end ShiTMCenteringDigitPrepare

open Lean Elab Command in
run_cmd do
  let name := ``ShiTMCenteringDigitPrepare.prepare_run
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected digit-preparation axiom {ax}"
  logInfo m!"CENTERING_DIGITS_CHECKED {name}; axioms {axioms}"

namespace ShiTMCenteringInputs
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
export ShiTMCenteringDigitPrepare (bits digits ancExtra depthExtra outExtra)
end E
abbrev Label := ShiTMCenteringDigitPrepare.Label ⊕ ShiTMCenteringPreparedSuffix.Label

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl (.broadcast 0 .copy)))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringDigitPrepare.machine l)
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMCenteringPreparedSuffix.machine l)

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := E.bits
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl .start
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def cost (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool) : Nat :=
  bs.length+3 + ShiTMCenteringPreparedSuffix.cost n w a out bs

/-- Starting from fractional coin bits in their ordinary order and the retained
verifier fields, produce the complete suffix and all three exact header increments. -/
theorem inputs_run (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hn : S (ShiTMCenteringBroadcast.source 0) = List.replicate n Cell.mark)
    (hw : S (ShiTMCenteringBroadcast.source 1) = List.replicate w Cell.mark)
    (ha : S (ShiTMCenteringBroadcast.source 2) = List.replicate a Cell.mark)
    (ho : S ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark)
    (hz : ∀ i, S (E.wire i) = []) (hs : S E.scratch = [])
    (hb : S E.bits = bs.map bit) (hd : S E.digits = [])
    (hanc : S E.ancExtra = []) (hdepth : S E.depthExtra = []) (hout : S E.outExtra = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost n w a out bs] (some ⟨some (.inl .start), v, S⟩) =
        some ⟨some (.inr (.inr ShiTMCenteringSuffix.terminal)), v', U⟩
      ∧ U E.output =
        ((((centeringSuffix (n+(w+(a+1))) out bs).map ShiBQP.encLayer).flatten).map bit).reverse ++ S E.output
      ∧ U E.ancExtra = List.replicate (3*bs.length+3) Cell.mark
      ∧ U E.depthExtra = List.replicate (76*bs.length+bs.count true+76) Cell.mark
      ∧ U E.outExtra = List.replicate (3*bs.length+2) Cell.mark
      ∧ U E.scratch = []
      ∧ (∀ h : Fin 4, U (.inr h) = S (.inr h))
      ∧ ∀ j, j ≠ E.output → j ≠ E.bits → j ≠ E.digits → j ≠ E.ancExtra →
          j ≠ E.depthExtra → j ≠ E.outExtra → (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, ar, ad, aa, adepth, ao, ab, af⟩ := ShiTMCenteringDigitPrepare.prepare_run bs v S hb hd hanc hdepth hout
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringDigitPrepare.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridge : run^[1] (some ⟨some (.inl .finished), none, A⟩) =
      some ⟨some (.inr (.inl (.broadcast 0 .copy))), none, A⟩ := rfl
  have afHeader (h : Fin 4) : A (.inr h) = S (.inr h) :=
    af _ (by intro he; cases he) (by intro he; cases he) (by intro he; cases he)
      (by intro he; cases he) (by intro he; cases he)
  have afWire (i : Fin 4) : A (E.wire i) = S (E.wire i) := by
    apply af <;> fin_cases i <;> decide
  obtain ⟨U, u, ur, uo, us, uf⟩ := ShiTMCenteringPreparedSuffix.prepared_suffix_run n w a out bs none A
    ((afHeader 0).trans hn) ((afHeader 1).trans hw) ((afHeader 2).trans ha)
    ((afHeader 3).trans ho) (fun i => (afWire i).trans (hz i))
    ((af _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs) ad
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringPreparedSuffix.machine machine Sum.inr
    (.inr ShiTMCenteringSuffix.terminal) rfl (fun _ _ => rfl) _ _ _ rfl ur
  have ufExtra (j : TopK) (hjo : j ≠ E.output) (hjd : j ≠ E.digits)
      (hjw : ∀ i, j ≠ E.wire i) : U j = A j := uf j hjo hjd hjw
  refine ⟨U, u, ?_, ?_, ?_, ?_, ?_, us, ?_, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridge
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lu
    have he : (bs.length+2)+1 = bs.length+3 := by omega
    simpa only [cost, he, ShiTMSubroutine.cfg, Option.map_some] using h2
  · rw [uo, af _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact (ufExtra _ (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans aa
  · exact (ufExtra _ (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans adepth
  · exact (ufExtra _ (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans ao
  · intro h
    exact (ufExtra _ (by intro he; cases he) (by intro he; cases he)
      (by intro i he; cases he)).trans (afHeader h)
  · intro j hjo hjb hjd hja hjt hjout hjw
    exact (uf j hjo hjd hjw).trans (af j hjb hjd hja hjt hjout)

theorem cost_le (n w a : Nat) (out : Fin (n+(w+(a+1)))) (bs : List Bool) :
    cost n w a out bs ≤
      bs.length*(500*(n+w+a+3*bs.length+4)+1003)+
        503*(n+w+a+3*bs.length+4)+4*(n+w+a)+bs.length+1026 := by
  have h := ShiTMCenteringPreparedSuffix.cost_le n w a out bs
  dsimp only [cost]
  omega

end ShiTMCenteringInputs

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringInputs.finiteMachine,
      ``ShiTMCenteringInputs.inputs_run,
      ``ShiTMCenteringInputs.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-input axiom {ax} in {name}"
    logInfo m!"CENTERING_INPUTS_CHECKED {name}; axioms {axioms}"
