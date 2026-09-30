import «AMPUNI-centering-assembly»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringHeaderController
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMCenteringHeader
namespace E
export ShiTMCenteringSelector (scratch output)
end E
abbrev PC := Fin 15

def nextPC (pc : PC) : PC := ⟨(pc.val+1)%15, Nat.mod_lt _ (by decide)⟩
def atPC (pc : PC) : Option Command := (program.drop pc.val).head?

inductive Label where
  | dispatch (pc : PC)
  | saved (pc : PC) (h : Fin 4) (l : ShiTMPieceEntry.EntryLabel)
  | core (pc : PC) (h : Fin 4) (l : ShiTMCenteringCoreCopy.Label)
  | finished
  deriving DecidableEq, Fintype

def machine : Label → Stmt TopGam Label Sig
  | .dispatch pc => match atPC pc with
    | none => .goto (fun _ => .finished)
    | some .delimiter => .push E.output (cst Cell.delim) (.goto (fun _ => .dispatch (nextPC pc)))
    | some (.add .one) => .push E.output (cst Cell.mark) (.goto (fun _ => .dispatch (nextPC pc)))
    | some (.add .input) => .goto (fun _ => .saved pc 0 (.inr .copy))
    | some (.add .witness) => .goto (fun _ => .saved pc 1 (.inr .copy))
    | some (.add .ancilla) => .goto (fun _ => .saved pc 2 (.inr .copy))
    | some (.add .ancExtra) => .goto (fun _ => .core pc 0 .copy)
    | some (.add .depthExtra) => .goto (fun _ => .core pc 1 .copy)
    | some (.add .outExtra) => .goto (fun _ => .core pc 2 .copy)
    | some (.add .oldDepth) => .goto (fun _ => .core pc 3 .copy)
  | .saved pc _ (.inr .done) => .goto (fun _ => .dispatch (nextPC pc))
  | .saved pc h l => ShiTMSubroutine.stmt (Label.saved pc h) (ShiTMPieceEntry.machineAt h 13 l)
  | .core pc _ .finished => .goto (fun _ => .dispatch (nextPC pc))
  | .core pc h l => ShiTMSubroutine.stmt (Label.core pc h) (ShiTMCenteringCoreCopy.machine h l)
  | .finished => .halt

def run := ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (.inl 10)
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .dispatch 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def savedAtom : Fin 3 → Atom := ![Atom.input, Atom.witness, Atom.ancilla]
def coreAtom : Fin 4 → Atom := ![Atom.ancExtra, Atom.depthExtra, Atom.outExtra, Atom.oldDepth]

def Ready (v : Atom → Nat) (S : ∀ j, List (TopGam j)) : Prop :=
  (∀ h : Fin 3, S (.inr (Fin.castAdd 1 h)) = List.replicate (v (savedAtom h)) Cell.mark) ∧
  (∀ h : Fin 4, S (ShiTMCenteringCoreCopy.source h) = List.replicate (v (coreAtom h)) Cell.mark) ∧
  v Atom.one = 1 ∧ S E.scratch = []

theorem ready_frame (v : Atom → Nat) (S U : ∀ j, List (TopGam j))
    (hs : Ready v S) (hf : ∀ j, j ≠ E.output → U j = S j) : Ready v U := by
  obtain ⟨hr, hc, ho, ht⟩ := hs
  refine ⟨?_, ?_, ho, ?_⟩
  · intro h; rw [hf _ (by intro he; cases he)]; exact hr h
  · intro h; rw [hf _ (ShiTMCenteringCoreCopy.source_ne_output h)]; exact hc h
  · rw [hf _ (by decide)]; exact ht

/-- Preserving copy of a retained counter followed by the controller return. -/
theorem saved_run (pc : PC) (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (.inr h) = List.replicate n Cell.mark) (ht : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+3] (some ⟨some (.saved pc h (.inr .copy)), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), none, U⟩
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨A, ar, ah, ao, atmp, af⟩ := ShiTMPieceEntry.copy_marks_run_at h 13 (by decide) n v S hs
  obtain ⟨U, ur, ut, uh, uf⟩ := ShiTMPieceEntry.restore_marks_run_at h 13 n none A (by simpa [ht] using atmp)
  have both := ShiTMFanout.iterTwo (ShiTMPieceEntry.runAt h 13) _ _ _ _ _ ar ur
  have lifted := ShiTMSubroutine.run_to_terminal (ShiTMPieceEntry.machineAt h 13) machine
    (Label.saved pc h) (.inr .done) rfl (by
      intro l hl
      cases l with
      | inl l => rfl
      | inr c => cases c <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl both
  have bridge : run^[1] (some ⟨some (.saved pc h (.inr .done)), none, U⟩) =
      some ⟨some (.dispatch (nextPC pc)), none, U⟩ := rfl
  refine ⟨U, ?_, ?_, ?_⟩
  · have hall := ShiTMFanout.iterTwo run _ _ _ _ _ lifted bridge
    have he : (n+1)+(n+1)+1 = 2*n+3 := by omega
    simpa only [he, ShiTMSubroutine.cfg, Option.map_some] using hall
  · rw [uf _ (by intro he; cases he) (by decide)]; exact ao
  · intro j hjo
    by_cases hjh : j = .inr h
    · subst j; rw [uh, ah, List.append_nil, hs]
    by_cases hjt : j = E.scratch
    · subst j; exact ut.trans ht.symm
    rw [uf j hjh hjt, af j hjh hjo hjt]

theorem core_run (pc : PC) (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (ShiTMCenteringCoreCopy.source h) = List.replicate n Cell.mark) (ht : S E.scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*n+3] (some ⟨some (.core pc h .copy), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), none, U⟩
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨U, ur, uo, uf⟩ := ShiTMCenteringCoreCopy.field_run h n v S hs ht
  have lifted := ShiTMSubroutine.run_to_terminal (ShiTMCenteringCoreCopy.machine h) machine
    (Label.core pc h) .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ur
  have bridge : run^[1] (some ⟨some (.core pc h .finished), none, U⟩) =
      some ⟨some (.dispatch (nextPC pc)), none, U⟩ := rfl
  refine ⟨U, ?_, uo, uf⟩
  have hall := ShiTMFanout.iterTwo run _ _ _ _ _ lifted bridge
  simpa only [Nat.add_assoc, ShiTMSubroutine.cfg, Option.map_some] using hall

theorem dispatch_saved_run (pc : PC) (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (.inr h) = List.replicate n Cell.mark) (ht : S E.scratch = [])
    (hstart : run^[1] (some ⟨some (.dispatch pc), v, S⟩) =
      some ⟨some (.saved pc h (.inr .copy)), v, S⟩) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[2*n+4] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), v', U⟩
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨U, ur, uo, uf⟩ := saved_run pc h n v S hs ht
  refine ⟨U, none, ?_, uo, uf⟩
  have hall := ShiTMFanout.iterTwo run _ _ _ _ _ hstart ur
  have he : 1+(2*n+3) = 2*n+4 := by omega
  simpa only [he] using hall

theorem dispatch_core_run (pc : PC) (h : Fin 4) (n : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S (ShiTMCenteringCoreCopy.source h) = List.replicate n Cell.mark) (ht : S E.scratch = [])
    (hstart : run^[1] (some ⟨some (.dispatch pc), v, S⟩) =
      some ⟨some (.core pc h .copy), v, S⟩) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[2*n+4] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), v', U⟩
      ∧ U E.output = List.replicate n Cell.mark ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨U, ur, uo, uf⟩ := core_run pc h n v S hs ht
  refine ⟨U, none, ?_, uo, uf⟩
  have hall := ShiTMFanout.iterTwo run _ _ _ _ _ hstart ur
  have he : 1+(2*n+3) = 2*n+4 := by omega
  simpa only [he] using hall

def commandCost (vals : Atom → Nat) : Command → Nat
  | .delimiter | .add .one => 1
  | .add a => 2*vals a+4

def scheduleCost (vals : Atom → Nat) : List Command → Nat
  | [] => 0
  | c :: cs => commandCost vals c + scheduleCost vals cs

theorem command_run (pc : PC) (c : Command) (vals : Atom → Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hc : atPC pc = some c) (hs : Ready vals S) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[commandCost vals c] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch (nextPC pc)), v', U⟩
      ∧ U E.output = cells vals c ++ S E.output
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨hret, hcore, hone, ht⟩ := hs
  cases c with
  | delimiter =>
    refine ⟨Function.update S E.output (Cell.delim :: S E.output), v, ?_, ?_, ?_⟩
    · simp [commandCost, run, ShiTMSubroutine.run, machine, hc, step, stepAux, cst]
    · simp [cells]
    · intro j hj; exact Function.update_of_ne hj _ _
  | add a =>
    cases a with
    | one =>
      refine ⟨Function.update S E.output (Cell.mark :: S E.output), v, ?_, ?_, ?_⟩
      · simp [commandCost, run, ShiTMSubroutine.run, machine, hc, step, stepAux, cst]
      · simp [cells, hone]
      · intro j hj; exact Function.update_of_ne hj _ _
    | input =>
      exact dispatch_saved_run pc 0 (vals Atom.input) v S (hret 0) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | witness =>
      exact dispatch_saved_run pc 1 (vals Atom.witness) v S (hret 1) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | ancilla =>
      exact dispatch_saved_run pc 2 (vals Atom.ancilla) v S (hret 2) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | ancExtra =>
      exact dispatch_core_run pc 0 (vals Atom.ancExtra) v S (hcore 0) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | depthExtra =>
      exact dispatch_core_run pc 1 (vals Atom.depthExtra) v S (hcore 1) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | outExtra =>
      exact dispatch_core_run pc 2 (vals Atom.outExtra) v S (hcore 2) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])
    | oldDepth =>
      exact dispatch_core_run pc 3 (vals Atom.oldDepth) v S (hcore 3) ht
        (by simp [run, ShiTMSubroutine.run, machine, hc, step, stepAux])

theorem program_length : program.length = 14 := by decide

theorem active_next (pc : PC) (c : Command) (hc : atPC pc = some c) :
    (nextPC pc).val = pc.val+1 := by
  have hp : pc.val < 14 := by
    by_contra hh
    have he : pc.val = 14 := by omega
    simp [atPC, he, program, field] at hc
  exact Nat.mod_eq_of_lt (by omega)

theorem active_suffix (pc : PC) (c : Command) (cs : List Command)
    (hs : program.drop pc.val = c :: cs) :
    atPC pc = some c ∧ program.drop (nextPC pc).val = cs := by
  have hc : atPC pc = some c := by rw [atPC, hs]; rfl
  refine ⟨hc, ?_⟩
  rw [active_next pc c hc, ← List.drop_drop, hs]
  rfl

theorem suffix_run (cs : List Command) (vals : Atom → Nat) (pc : PC)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hcs : program.drop pc.val = cs) (hs : Ready vals S) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig) (pc' : PC),
      run^[scheduleCost vals cs] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch pc'), v', U⟩
      ∧ pc'.val = pc.val+cs.length
      ∧ U E.output = eval vals cs (S E.output)
      ∧ Ready vals U
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  induction cs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, rfl, hs, by intro j _; rfl⟩
  | cons c cs ih =>
    obtain ⟨hc, htail⟩ := active_suffix pc c cs hcs
    obtain ⟨A, av, ar, ao, af⟩ := command_run pc c vals v S hc hs
    obtain ⟨U, uv, up, ur, upc, uo, us, uf⟩ := ih (nextPC pc) av A htail (ready_frame vals S A hs af)
    refine ⟨U, uv, up, ?_, ?_, ?_, us, ?_⟩
    · exact ShiTMFanout.iterTwo run _ _ _ _ _ ar ur
    · have hn := active_next pc c hc
      simp only [List.length_cons] at *
      omega
    · change U E.output = eval vals cs (cells vals c ++ S E.output)
      rw [← ao]; exact uo
    · intro j hj; rw [uf j hj, af j hj]

/-- Execute all four headers and stop at an explicit terminal label. -/
theorem program_run (vals : Atom → Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : Ready vals S) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost vals program+1] (some ⟨some (.dispatch 0), v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U E.output = eval vals program (S E.output)
      ∧ Ready vals U
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨U, u, pc, ur, hp, uo, us, uf⟩ := suffix_run program vals 0 v S (by simp) hs
  have he : atPC pc = none := by
    have hv : pc.val = program.length := by simpa using hp
    simp [atPC, hv]
  have last : run^[1] (some ⟨some (.dispatch pc), u, U⟩) =
      some ⟨some .finished, u, U⟩ := by
    simp [run, ShiTMSubroutine.run, machine, he, step, stepAux]
  exact ⟨U, u, ShiTMFanout.iterTwo run _ _ _ _ _ ur last, uo, us, uf⟩

theorem program_cost (n w a d ai oi di : Nat) :
    scheduleCost (value n w a d ai oi di) program+1 =
      2*(n+2*w+2*a+d+ai+oi+di)+42 := by
  simp [program, field, scheduleCost, commandCost, value]
  omega

theorem encoded_headers_run (n w a d ai oi di : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : Ready (value n w a d ai oi di) S) (ho : S E.output = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[2*(n+2*w+2*a+d+ai+oi+di)+42] (some ⟨some (.dispatch 0), v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U E.output = ((ShiBQP.encNat w ++ ShiBQP.encNat (a+ai) ++
          ShiBQP.encNat (n+w+a+1+oi) ++ ShiBQP.encNat (d+di)).map bit).reverse
      ∧ ∀ j, j ≠ E.output → U j = S j := by
  obtain ⟨U, u, ur, uo, _, uf⟩ := program_run (value n w a d ai oi di) v S hs
  refine ⟨U, u, ?_, ?_, uf⟩
  · simpa only [program_cost] using ur
  · rw [uo, ho, program_correct_encoding]

end ShiTMCenteringHeaderController

namespace ShiTMCenteringEncodedAssembly
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev Label := ShiTMCenteringHeaderController.Label ⊕ ShiTMCenteringBody.Label

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl .copy))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringHeaderController.machine l)
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMCenteringBody.machine l)

def run := ShiTMSubroutine.run machine
def terminal : Label := .inr (.inr (.inr ShiTMCenteringSuffix.terminal))

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMCenteringPayload.source
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl (.dispatch 0)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def header (n w a d : Nat) (bs : List Bool) : List Bool :=
  ShiBQP.encNat w ++ ShiBQP.encNat (a+(3*bs.length+3)) ++
  ShiBQP.encNat (n+w+a+1+(3*bs.length+2)) ++
  ShiBQP.encNat (d+(76*bs.length+bs.count true+76))

def headerCost (n w a d : Nat) (bs : List Bool) : Nat :=
  2*(n+2*w+2*a+d+(3*bs.length+3)+(3*bs.length+2)+(76*bs.length+bs.count true+76))+42

def cost (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) : Nat :=
  headerCost n w a d bs + 1 + ShiTMCenteringBody.cost n w a out bs payload

/-- The finite header writer and body emitter produce the complete centered
encoding from the retained fields, prepared increments, and original payload. -/
theorem assembly_run (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hr : ShiTMCenteringHeaderController.Ready
      (ShiTMCenteringHeader.value n w a d (3*bs.length+3) (3*bs.length+2)
        (76*bs.length+bs.count true+76)) S)
    (ho : S ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark)
    (hz : ∀ i, S (E.wire i) = [])
    (hd : S ShiTMCenteringCoinLoop.digits = bs.reverse.map bit)
    (hp : S ShiTMCenteringPayload.source = payload.map bit) (he : S E.output = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost n w a d out bs payload] (some ⟨some (.inl (.dispatch 0)), v, S⟩) =
        some ⟨some terminal, v', U⟩
      ∧ U E.output =
        ((header n w a d bs ++ payload ++ ((centeringSuffix (n+(w+(a+1))) out bs).map
          ShiBQP.encLayer).flatten).map bit).reverse
      ∧ U E.scratch = []
      ∧ U ShiTMCenteringPayload.source = []
      ∧ ∀ j, j ≠ E.output → j ≠ ShiTMCenteringPayload.source →
          j ≠ ShiTMCenteringCoinLoop.digits → (∀ i, j ≠ E.wire i) → U j = S j := by
  obtain ⟨A, av, ar, ao, af⟩ := ShiTMCenteringHeaderController.encoded_headers_run
    n w a d (3*bs.length+3) (3*bs.length+2) (76*bs.length+bs.count true+76) v S hr he
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringHeaderController.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridge : run^[1] (some ⟨some (.inl .finished), av, A⟩) =
      some ⟨some (.inr (.inl .copy)), av, A⟩ := rfl
  have an : A (ShiTMCenteringBroadcast.source 0) = List.replicate n Cell.mark := by
    rw [af _ (by decide)]; exact hr.1 0
  have aw : A (ShiTMCenteringBroadcast.source 1) = List.replicate w Cell.mark := by
    rw [af _ (by decide)]; exact hr.1 1
  have aa : A (ShiTMCenteringBroadcast.source 2) = List.replicate a Cell.mark := by
    rw [af _ (by decide)]; exact hr.1 2
  have aout := (af _ (by decide)).trans ho
  have az : ∀ i, A (E.wire i) = [] := by
    intro i; rw [af _ (ShiTMCenteringSelector.wire_ne_output i), hz]
  have ascratch : A E.scratch = [] := by rw [af _ (by decide)]; exact hr.2.2.2
  have ad := (af _ (by decide)).trans hd
  have ap := (af _ (by decide)).trans hp
  obtain ⟨U, uv, ur, uo, us, up, uf⟩ := ShiTMCenteringBody.body_run
    n w a out bs payload (header n w a d bs) av A an aw aa aout az ascratch ad ap ao
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringBody.machine machine Sum.inr
    (.inr (.inr ShiTMCenteringSuffix.terminal)) rfl (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, uv, ?_, uo, us, up, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridge
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lu
    simpa only [cost, headerCost, terminal, ShiTMSubroutine.cfg, Option.map_some] using h2
  · intro j hjo hjp hjd hjw
    rw [uf j hjo hjp hjd hjw, af j hjo]

theorem headerCost_le (n w a d : Nat) (bs : List Bool) :
    headerCost n w a d bs ≤ 2*n+4*w+4*a+2*d+166*bs.length+204 := by
  have h := List.count_le_length (a := true) (l := bs)
  unfold headerCost
  omega

theorem cost_le (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    cost n w a d out bs payload ≤
      payload.length + bs.length*(500*(n+w+a+3*bs.length+4)+1003) +
      503*(n+w+a+3*bs.length+4)+4*(n+w+a) +
      2*n+4*w+4*a+2*d+166*bs.length+1230 := by
  have hb := ShiTMCenteringBody.cost_le n w a out bs payload
  have hh := headerCost_le n w a d bs
  unfold cost
  omega

end ShiTMCenteringEncodedAssembly

namespace ShiTMCenteringDepthParser
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev source : TopK := .inl (.inl 11)
abbrev depth : TopK := .inl (.inl 10)
inductive Label where
  | scan | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [Label.scan, Label.finished]
  (by intro l; cases l <;> simp)

def machine : Label → Stmt TopGam Label Sig
  | .scan => .pop source pop (.branch isMark
      (.push depth (cst Cell.mark) (.goto (fun _ => .scan)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

/-- Parse the old circuit depth while preserving all remaining gate bytes. -/
theorem parse_run (d : Nat) (payload : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = List.replicate d Cell.mark ++ Cell.delim :: payload) :
    ∃ U : ∀ j, List (TopGam j),
      run^[d+1] (some ⟨some .scan, v, S⟩) = some ⟨some .finished, some Cell.delim, U⟩
      ∧ U source = payload
      ∧ U depth = List.replicate d Cell.mark ++ S depth
      ∧ ∀ j, j ≠ source → j ≠ depth → U j = S j := by
  induction d generalizing v S with
  | zero =>
    refine ⟨Function.update S source payload, ?_, by simp, ?_, ?_⟩
    · simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isMark]
    · simp [source, depth]
    · intro j hj _; exact Function.update_of_ne hj _ _
  | succ d ih =>
    let T := Function.update (Function.update S source (List.replicate d Cell.mark ++ Cell.delim :: payload))
      depth (Cell.mark :: S depth)
    have hfirst : run (some ⟨some .scan, v, S⟩) = some ⟨some .scan, some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, List.replicate_succ,
        pop, isMark, cst, T, source, depth]
    obtain ⟨U, ur, us, ud, uf⟩ := ih (some Cell.mark) T (by simp [T, source, depth])
    refine ⟨U, ?_, us, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hfirst]; exact ur
    · rw [ud]
      simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using
        ShiTMPieceEntry.replicate_mark_snoc d (S depth)
    · intro j hjs hjd; rw [uf j hjs hjd]; simp [T, hjs, hjd]

theorem encoded_depth_run (d : Nat) (payload : List Bool) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = (ShiBQP.encNat d ++ payload).map bit) (hd : S depth = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[d+1] (some ⟨some .scan, v, S⟩) = some ⟨some .finished, some Cell.delim, U⟩
      ∧ U source = payload.map bit
      ∧ U depth = List.replicate d Cell.mark
      ∧ ∀ j, j ≠ source → j ≠ depth → U j = S j := by
  have hs' : S source = List.replicate d Cell.mark ++ Cell.delim :: payload.map bit := by
    simpa [ShiBQP.encNat, bit, List.map_append] using hs
  obtain ⟨U, ur, us, ud, uf⟩ := parse_run d (payload.map bit) v S hs'
  exact ⟨U, ur, us, by simpa [hd] using ud, uf⟩

end ShiTMCenteringDepthParser

namespace ShiTMCenteringAssemblyInputs
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringSelector (wire scratch output)
export ShiTMCenteringDigitPrepare (bits digits ancExtra depthExtra outExtra)
export ShiTMCenteringDepthParser (source depth)
end E
abbrev Label := ShiTMCenteringDepthParser.Label ⊕
  (ShiTMCenteringDigitPrepare.Label ⊕ ShiTMCenteringEncodedAssembly.Label)

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl .start))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringDepthParser.machine l)
  | .inr (.inl .finished) => .goto (fun _ => .inr (.inr (.inl (.dispatch 0))))
  | .inr (.inl l) => ShiTMSubroutine.stmt (fun l => .inr (.inl l)) (ShiTMCenteringDigitPrepare.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt (fun l => .inr (.inr l)) (ShiTMCenteringEncodedAssembly.machine l)

def run := ShiTMSubroutine.run machine
def terminal : Label := .inr (.inr ShiTMCenteringEncodedAssembly.terminal)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := E.source
  k₁ := E.output
  Γ := TopGam
  Λ := Label
  main := .inl .scan
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

def cost (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) : Nat :=
  d+bs.length+5 + ShiTMCenteringEncodedAssembly.cost n w a d out bs payload

/-- Full assembly after the four retained fields have been parsed: read old
depth, prepare ordinary-order coin bits, write headers, copy old gates, emit suffix. -/
theorem inputs_run (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hn : S (.inr 0) = List.replicate n Cell.mark)
    (hw : S (.inr 1) = List.replicate w Cell.mark)
    (ha : S (.inr 2) = List.replicate a Cell.mark)
    (ho : S (.inr 3) = List.replicate out.val Cell.mark)
    (hp : S E.source = (ShiBQP.encNat d ++ payload).map bit)
    (hb : S E.bits = bs.map bit)
    (hdepth : S E.depth = []) (hd : S E.digits = [])
    (hai : S E.ancExtra = []) (hti : S E.depthExtra = []) (hoi : S E.outExtra = [])
    (hz : ∀ i, S (E.wire i) = []) (hs : S E.scratch = []) (he : S E.output = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[cost n w a d out bs payload] (some ⟨some (.inl .scan), v, S⟩) =
        some ⟨some terminal, v', U⟩
      ∧ U E.output =
        ((ShiTMCenteringEncodedAssembly.header n w a d bs ++ payload ++
          ((centeringSuffix (n+(w+(a+1))) out bs).map ShiBQP.encLayer).flatten).map bit).reverse
      ∧ U E.scratch = []
      ∧ U E.source = []
      ∧ (∀ h : Fin 4, U (.inr h) = S (.inr h)) := by
  obtain ⟨A, ar, ap, adepth, af⟩ := ShiTMCenteringDepthParser.encoded_depth_run d payload v S hp hdepth
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringDepthParser.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridgeA : run^[1] (some ⟨some (.inl .finished), some Cell.delim, A⟩) =
      some ⟨some (.inr (.inl .start)), some Cell.delim, A⟩ := rfl
  have ab := (af _ (by decide) (by decide)).trans hb
  have ad := (af _ (by decide) (by decide)).trans hd
  have aa := (af _ (by decide) (by decide)).trans hai
  have atmp := (af _ (by decide) (by decide)).trans hti
  have ao := (af _ (by decide) (by decide)).trans hoi
  obtain ⟨B, br, bd, bai, bti, boi, _, bf⟩ :=
    ShiTMCenteringDigitPrepare.prepare_run bs (some Cell.delim) A ab ad aa atmp ao
  have lb := ShiTMSubroutine.run_to_terminal ShiTMCenteringDigitPrepare.machine machine
    (fun l => .inr (.inl l)) .finished rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl br
  have bridgeB : run^[1] (some ⟨some (.inr (.inl .finished)), none, B⟩) =
      some ⟨some (.inr (.inr (.inl (.dispatch 0)))), none, B⟩ := rfl
  have bret (h : Fin 4) : B (.inr h) = S (.inr h) := by
    rw [bf _ (by intro he; cases he) (by intro he; cases he) (by intro he; cases he)
      (by intro he; cases he) (by intro he; cases he),
      af _ (by intro he; cases he) (by intro he; cases he)]
  have ready : ShiTMCenteringHeaderController.Ready
      (ShiTMCenteringHeader.value n w a d (3*bs.length+3) (3*bs.length+2)
        (76*bs.length+bs.count true+76)) B := by
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro h
      rw [bret]
      fin_cases h
      · exact hn
      · exact hw
      · exact ha
    · intro h
      fin_cases h
      · exact bai
      · exact bti
      · exact boi
      · change B E.depth = List.replicate d Cell.mark
        rw [bf _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact adepth
    · rw [bf _ (by decide) (by decide) (by decide) (by decide) (by decide),
        af _ (by decide) (by decide), hs]
  have bout : B ShiTMCenteringHandoff.retained = List.replicate out.val Cell.mark := by
    rw [bret 3]; exact ho
  have bz : ∀ i, B (E.wire i) = [] := by
    intro i
    rw [bf _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide),
      af _ (by fin_cases i <;> decide) (by fin_cases i <;> decide), hz]
  have bp : B E.source = payload.map bit := by
    rw [bf _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ap
  have be : B E.output = [] := by
    rw [bf _ (by decide) (by decide) (by decide) (by decide) (by decide),
      af _ (by decide) (by decide), he]
  obtain ⟨U, uv, ur, uo, us, up, uf⟩ := ShiTMCenteringEncodedAssembly.assembly_run
    n w a d out bs payload none B ready bout bz bd bp be
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringEncodedAssembly.machine machine
    (fun l => .inr (.inr l)) ShiTMCenteringEncodedAssembly.terminal rfl
    (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, uv, ?_, uo, us, up, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridgeA
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lb
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 bridgeB
    have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h3 lu
    have hcost : ((d+1)+1+(bs.length+2))+1 = d+bs.length+5 := by omega
    simpa only [cost, hcost, terminal, ShiTMSubroutine.cfg, Option.map_some] using h4
  · intro h
    rw [uf _ (by intro he; cases he) (by intro he; cases he) (by intro he; cases he)
      (by intro i he; cases he), bret]

theorem cost_le (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    cost n w a d out bs payload ≤
      payload.length + bs.length*(500*(n+w+a+3*bs.length+4)+1003) +
      503*(n+w+a+3*bs.length+4)+4*(n+w+a) +
      2*n+4*w+4*a+3*d+167*bs.length+1235 := by
  have h := ShiTMCenteringEncodedAssembly.cost_le n w a d out bs payload
  unfold cost
  omega

end ShiTMCenteringAssemblyInputs

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringHeaderController.finiteMachine,
      ``ShiTMCenteringHeaderController.command_run,
      ``ShiTMCenteringHeaderController.program_run,
      ``ShiTMCenteringHeaderController.program_cost,
      ``ShiTMCenteringHeaderController.encoded_headers_run,
      ``ShiTMCenteringEncodedAssembly.finiteMachine,
      ``ShiTMCenteringEncodedAssembly.assembly_run,
      ``ShiTMCenteringEncodedAssembly.headerCost_le,
      ``ShiTMCenteringEncodedAssembly.cost_le,
      ``ShiTMCenteringDepthParser.encoded_depth_run,
      ``ShiTMCenteringAssemblyInputs.finiteMachine,
      ``ShiTMCenteringAssemblyInputs.inputs_run,
      ``ShiTMCenteringAssemblyInputs.cost_le] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected header-controller axiom {ax} in {name}"
    logInfo m!"CENTERING_HEADER_CONTROLLER_CHECKED {name}; axioms {axioms}"
