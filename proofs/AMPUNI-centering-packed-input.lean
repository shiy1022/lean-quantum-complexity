import «AMPUNI-centering-header-controller»
import «AMPUNI-boolean-controller-overhead»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMCenteringCoinInput
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev source : TopK := .inl (.inl 11)
abbrev temporary : TopK := .inl (.inl 12)
abbrev bits : TopK := .inl (.inl 9)

/-- A true tag precedes each data bit; a false tag terminates the coin coinPrefix. -/
def coinPrefix : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: coinPrefix bs

theorem prefix_length (bs : List Bool) : (coinPrefix bs).length = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [coinPrefix, List.length_cons, ih]; omega

inductive Label where
  | tag | digit | reverse | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [Label.tag, Label.digit, Label.reverse, Label.finished]
  (by intro l; cases l <;> simp)

def machine : Label → Stmt TopGam Label Sig
  | .tag => .pop source pop (.branch isMark (.goto (fun _ => .digit)) (.goto (fun _ => .reverse)))
  | .digit => .pop source pop (.push temporary ShiTMLayoutMachine.get (.goto (fun _ => .tag)))
  | .reverse => .pop temporary pop (.branch isSome
      (.push bits ShiTMLayoutMachine.get (.goto (fun _ => .reverse))) (.goto (fun _ => .finished)))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

theorem scan_run (bs : List Bool) (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = (coinPrefix bs).map bit ++ rest) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*bs.length+1] (some ⟨some .tag, v, S⟩) = some ⟨some .reverse, some Cell.delim, U⟩
      ∧ U source = rest
      ∧ U temporary = (bs.map bit).reverse ++ S temporary
      ∧ ∀ j, j ≠ source → j ≠ temporary → U j = S j := by
  induction bs generalizing v S with
  | nil =>
    refine ⟨Function.update S source rest, ?_, by simp, ?_, ?_⟩
    · simp [coinPrefix, bit, run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isMark]
    · simp [source, temporary]
    · intro j hj _; exact Function.update_of_ne hj _ _
  | cons b bs ih =>
    let A := Function.update S source (bit b :: (coinPrefix bs).map bit ++ rest)
    let B := Function.update (Function.update S source ((coinPrefix bs).map bit ++ rest))
      temporary (bit b :: S temporary)
    have first : run^[1] (some ⟨some .tag, v, S⟩) = some ⟨some .digit, some Cell.mark, A⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, coinPrefix, bit, pop, isMark, A]
    have second : run^[1] (some ⟨some .digit, some Cell.mark, A⟩) = some ⟨some .tag, some (bit b), B⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, A, B, pop, ShiTMLayoutMachine.get, source, temporary]
    obtain ⟨U, ur, us, ut, uf⟩ := ih (some (bit b)) B (by simp [B, source, temporary])
    refine ⟨U, ?_, us, ?_, ?_⟩
    · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ first second
      have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 ur
      have hc : 1+1+(2*bs.length+1) = 2*(b::bs).length+1 := by simp; omega
      simpa only [hc] using h2
    · rw [ut]; simp [B, List.reverse_cons, List.append_assoc]
    · intro j hjs hjt; rw [uf j hjs hjt]; simp [B, hjs, hjt]

theorem reverse_run (xs : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S temporary = xs) :
    ∃ U : ∀ j, List (TopGam j),
      run^[xs.length+1] (some ⟨some .reverse, v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U temporary = []
      ∧ U bits = xs.reverse ++ S bits
      ∧ ∀ j, j ≠ temporary → j ≠ bits → U j = S j := by
  induction xs generalizing v S with
  | nil =>
    refine ⟨S, ?_, hs, by simp, by intro j _ _; rfl⟩
    simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
    let T := Function.update (Function.update S temporary xs) bits (x :: S bits)
    have first : run (some ⟨some .reverse, v, S⟩) = some ⟨some .reverse, some x, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, pop, isSome,
        ShiTMLayoutMachine.get, T, temporary, bits]
    obtain ⟨U, ur, ut, ub, uf⟩ := ih (some x) T (by simp [T, temporary, bits])
    refine ⟨U, ?_, ut, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, first]; exact ur
    · rw [ub]; simp [T, List.reverse_cons, List.append_assoc]
    · intro j hjt hjb; rw [uf j hjt hjb]; simp [T, hjt, hjb]

theorem input_run (bs : List Bool) (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = (coinPrefix bs).map bit ++ rest) (ht : S temporary = []) (hb : S bits = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[3*bs.length+2] (some ⟨some .tag, v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U source = rest ∧ U bits = bs.map bit ∧ U temporary = []
      ∧ ∀ j, j ≠ source → j ≠ bits → U j = S j := by
  obtain ⟨A, ar, asrc, atmp, af⟩ := scan_run bs rest v S hs
  obtain ⟨U, ur, ut, ub, uf⟩ := reverse_run (bs.map bit).reverse (some Cell.delim) A (by simpa [ht] using atmp)
  refine ⟨U, ?_, ?_, ?_, ut, ?_⟩
  · have h := ShiTMFanout.iterTwo run _ _ _ _ _ ar ur
    simpa only [List.length_reverse, List.length_map, show 2*bs.length+1+(bs.length+1)=3*bs.length+2 by omega] using h
  · rw [uf _ (by decide) (by decide)]; exact asrc
  · rw [ub, af _ (by decide) (by decide), hb]; simp
  · intro j hjs hjb
    by_cases hjt : j = temporary
    · subst j; exact ut.trans ht.symm
    rw [uf j hjt hjb, af j hjs hjt]

end ShiTMCenteringCoinInput

namespace ShiTMCenteringFields
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev source : TopK := .inl (.inl 11)
inductive Label where
  | scan (h : Fin 4) | finished
  deriving DecidableEq, Fintype

def next (h : Fin 4) : Label :=
  if hh : h.val < 3 then .scan ⟨h.val+1, by omega⟩ else .finished

def machine : Label → Stmt TopGam Label Sig
  | .scan h => .pop source pop (.branch isMark
      (.push (.inr h) (cst Cell.mark) (.goto (fun _ => .scan h)))
      (.goto (fun _ => next h)))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

theorem field_run (h : Fin 4) (n : Nat) (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = (ShiBQP.encNat n).map bit ++ rest) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+1] (some ⟨some (.scan h), v, S⟩) = some ⟨some (next h), some Cell.delim, U⟩
      ∧ U source = rest
      ∧ U (.inr h) = List.replicate n Cell.mark ++ S (.inr h)
      ∧ ∀ j, j ≠ source → j ≠ .inr h → U j = S j := by
  induction n generalizing v S with
  | zero =>
    refine ⟨Function.update S source rest, ?_, by simp, by simp [source], ?_⟩
    · simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, ShiBQP.encNat, bit, pop, isMark]
    · intro j hj _; exact Function.update_of_ne hj _ _
  | succ n ih =>
    let T := Function.update (Function.update S source ((ShiBQP.encNat n).map bit ++ rest))
      (.inr h) (Cell.mark :: S (.inr h))
    have first : run (some ⟨some (.scan h), v, S⟩) = some ⟨some (.scan h), some Cell.mark, T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hs, ShiBQP.encNat, bit,
        List.replicate_succ, pop, isMark, cst, T, source]
    obtain ⟨U, ur, us, uh, uf⟩ := ih (some Cell.mark) T (by simp [T, source])
    refine ⟨U, ?_, us, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, first]; exact ur
    · rw [uh]; simp only [T, Function.update_self]
      simpa only [List.replicate_succ, List.cons_append] using ShiTMPieceEntry.replicate_mark_snoc n (S (.inr h))
    · intro j hjs hjh; rw [uf j hjs hjh]; simp [T, hjs, hjh]

def headers (n w a out : Nat) : List Bool :=
  ShiBQP.encNat n ++ ShiBQP.encNat w ++ ShiBQP.encNat a ++ ShiBQP.encNat out

theorem fields_run (n w a out : Nat) (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = (headers n w a out).map bit ++ rest) :
    ∃ U : ∀ j, List (TopGam j),
      run^[n+w+a+out+4] (some ⟨some (.scan 0), v, S⟩) = some ⟨some .finished, some Cell.delim, U⟩
      ∧ U source = rest
      ∧ (∀ h : Fin 4, U (.inr h) = List.replicate (![n,w,a,out] h) Cell.mark ++ S (.inr h))
      ∧ ∀ j, j ≠ source → (∀ h : Fin 4, j ≠ .inr h) → U j = S j := by
  let r3 := (ShiBQP.encNat out).map bit ++ rest
  let r2 := (ShiBQP.encNat a).map bit ++ r3
  let r1 := (ShiBQP.encNat w).map bit ++ r2
  obtain ⟨A, ar, asrc, ah, af⟩ := field_run 0 n r1 v S (by simpa [headers, r1, r2, r3, List.map_append, List.append_assoc] using hs)
  obtain ⟨B, br, bsrc, bh, bf⟩ := field_run 1 w r2 (some Cell.delim) A asrc
  obtain ⟨C, cr, csrc, ch, cf⟩ := field_run 2 a r3 (some Cell.delim) B bsrc
  obtain ⟨U, ur, usrc, uh, uf⟩ := field_run 3 out rest (some Cell.delim) C csrc
  refine ⟨U, ?_, usrc, ?_, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ ar br
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 cr
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 ur
    have he : ((n+1)+(w+1))+(a+1)+(out+1)=n+w+a+out+4 := by omega
    simpa only [he, show next 3 = Label.finished from rfl] using h3
  · intro h; fin_cases h
    · change U (.inr 0) = List.replicate n Cell.mark ++ S (.inr 0)
      rw [uf _ (by decide) (by decide), cf _ (by decide) (by decide), bf _ (by decide) (by decide)]; exact ah
    · change U (.inr 1) = List.replicate w Cell.mark ++ S (.inr 1)
      rw [uf _ (by decide) (by decide), cf _ (by decide) (by decide), bh, af _ (by decide) (by decide)]
    · change U (.inr 2) = List.replicate a Cell.mark ++ S (.inr 2)
      rw [uf _ (by decide) (by decide), ch, bf _ (by decide) (by decide), af _ (by decide) (by decide)]
    · change U (.inr 3) = List.replicate out Cell.mark ++ S (.inr 3)
      rw [uh, cf _ (by decide) (by decide), bf _ (by decide) (by decide), af _ (by decide) (by decide)]
  · intro j hjs hjh
    rw [uf j hjs (hjh 3), cf j hjs (hjh 2), bf j hjs (hjh 1), af j hjs (hjh 0)]

end ShiTMCenteringFields

namespace ShiTMCenteringPacked
open ShiTMLayoutMachine ShiTMRetainedTop ShiQMACenteringCircuit
namespace E
export ShiTMCenteringCoinInput (source bits)
export ShiTMCenteringSelector (wire scratch output)
end E
abbrev Label := ShiTMCenteringCoinInput.Label ⊕
  (ShiTMCenteringFields.Label ⊕ ShiTMCenteringAssemblyInputs.Label)

noncomputable instance : DecidableEq Label := by classical exact inferInstance

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl (.scan 0)))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringCoinInput.machine l)
  | .inr (.inl .finished) => .goto (fun _ => .inr (.inr (.inl .scan)))
  | .inr (.inl l) => ShiTMSubroutine.stmt (fun l => .inr (.inl l)) (ShiTMCenteringFields.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt (fun l => .inr (.inr l)) (ShiTMCenteringAssemblyInputs.machine l)

def run := ShiTMSubroutine.run machine
def main : Label := .inl .tag
def terminal : Label := .inr (.inr ShiTMCenteringAssemblyInputs.terminal)

def packed (n w a d out : Nat) (bs payload : List Bool) : List Bool :=
  ShiTMCenteringCoinInput.coinPrefix bs ++ ShiTMCenteringFields.headers n w a out ++
  ShiBQP.encNat d ++ payload

def result (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) : List Bool :=
  ShiTMCenteringEncodedAssembly.header n w a d bs ++ payload ++
  ((centeringSuffix (n+(w+(a+1))) out bs).map ShiBQP.encLayer).flatten

def cost (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) : Nat :=
  3*bs.length+n+w+a+out.val+8 + ShiTMCenteringAssemblyInputs.cost n w a d out bs payload

/-- Run the entire centering assembly from a single packed source string,
with all work stacks initially empty. -/
theorem packed_run (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    ∃ (U : ∀ j, List (TopGam j)) (v : Sig),
      run^[cost n w a d out bs payload]
        (some ⟨some main, none, ShiTMBooleanWrapper.initialTop (packed n w a d out.val bs payload)⟩) =
        some ⟨some terminal, v, U⟩
      ∧ U E.output = ((result n w a d out bs payload).map bit).reverse := by
  let S := ShiTMBooleanWrapper.initialTop (packed n w a d out.val bs payload)
  let rest := ((ShiBQP.encNat d ++ payload).map bit)
  let fields := (ShiTMCenteringFields.headers n w a out.val).map bit ++ rest
  have hs : S E.source = (ShiTMCenteringCoinInput.coinPrefix bs).map bit ++ fields := by
    simp [S, ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource, packed, fields, rest,
      E.source, List.map_append, List.append_assoc]
  have empty (j : TopK) (hj : j ≠ E.source) : S j = [] := by
    simp [S, ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource, E.source] at hj ⊢
    exact Function.update_of_ne hj _ _
  obtain ⟨A, ar, asrc, abits, _, af⟩ := ShiTMCenteringCoinInput.input_run bs fields none S hs
    (empty _ (by decide)) (empty _ (by decide))
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringCoinInput.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridgeA : run^[1] (some ⟨some (.inl .finished), none, A⟩) =
      some ⟨some (.inr (.inl (.scan 0))), none, A⟩ := rfl
  obtain ⟨B, br, bsrc, bret, bf⟩ := ShiTMCenteringFields.fields_run n w a out.val rest none A asrc
  have lb := ShiTMSubroutine.run_to_terminal ShiTMCenteringFields.machine machine
    (fun l => .inr (.inl l)) .finished rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl br
  have bridgeB : run^[1] (some ⟨some (.inr (.inl .finished)), some Cell.delim, B⟩) =
      some ⟨some (.inr (.inr (.inl .scan))), some Cell.delim, B⟩ := rfl
  have retained (h : Fin 4) : B (.inr h) = List.replicate (![n,w,a,out.val] h) Cell.mark := by
    rw [bret, af _ (by intro he; cases he) (by intro he; cases he), empty _ (by intro he; cases he), List.append_nil]
  have coreEmpty (i : Fin 14) (hi : i ≠ 11) (hib : i ≠ 9) : B (.inl (.inl i)) = [] := by
    rw [bf _ (by simpa [ShiTMCenteringFields.source] using hi) (by intro h he; cases he),
      af _ (by simpa [E.source] using hi) (by simpa [E.bits] using hib)]
    exact empty _ (by simpa [E.source] using hi)
  have bitsReady : B ShiTMCenteringDigitPrepare.bits = bs.map bit := by
    rw [bf _ (by decide) (by intro h he; cases he)]; exact abits
  have wiresReady : ∀ h, B (E.wire h) = [] := by
    intro h; fin_cases h <;> exact coreEmpty _ (by decide) (by decide)
  obtain ⟨U, uv, ur, uo, _, _, _⟩ := ShiTMCenteringAssemblyInputs.inputs_run n w a d out bs payload
    (some Cell.delim) B (retained 0) (retained 1) (retained 2) (retained 3) bsrc bitsReady
    (coreEmpty _ (by decide) (by decide)) (coreEmpty _ (by decide) (by decide))
    (coreEmpty _ (by decide) (by decide)) (coreEmpty _ (by decide) (by decide))
    (coreEmpty _ (by decide) (by decide)) wiresReady
    (coreEmpty _ (by decide) (by decide)) (coreEmpty _ (by decide) (by decide))
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringAssemblyInputs.machine machine
    (fun l => .inr (.inr l)) ShiTMCenteringAssemblyInputs.terminal rfl
    (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, uv, ?_, uo⟩
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridgeA
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lb
  have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 bridgeB
  have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h3 lu
  have hc : ((3*bs.length+2)+1+(n+w+a+out.val+4))+1 = 3*bs.length+n+w+a+out.val+8 := by omega
  simpa only [cost, hc, main, terminal, ShiTMSubroutine.cfg, Option.map_some] using h4

theorem cost_le (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    cost n w a d out bs payload ≤
      payload.length + bs.length*(500*(n+w+a+3*bs.length+4)+1003) +
      503*(n+w+a+3*bs.length+4)+6*(n+w+a) +
      2*n+4*w+4*a+3*d+170*bs.length+1243 := by
  have h := ShiTMCenteringAssemblyInputs.cost_le n w a d out bs payload
  have ho := out.isLt
  unfold cost
  omega

theorem packed_length (n w a d out : Nat) (bs payload : List Bool) :
    (packed n w a d out bs payload).length =
      2*bs.length+n+w+a+out+d+payload.length+6 := by
  simp [packed, ShiTMCenteringFields.headers, ShiBQP.encNat,
    ShiTMCenteringCoinInput.prefix_length]
  omega

/-- A uniform quadratic clock in the length of the actual packed input. -/
theorem cost_quadratic (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool) :
    cost n w a d out bs payload ≤
      10000*((packed n w a d out.val bs payload).length+1)^2 := by
  let t := (packed n w a d out.val bs payload).length+1
  have ht : 1 ≤ t := by omega
  have hl := packed_length n w a d out.val bs payload
  have hk : bs.length ≤ t := by dsimp [t]; omega
  have hN : n+w+a ≤ t := by dsimp [t]; omega
  have hd : d ≤ t := by dsimp [t]; omega
  have hp : payload.length ≤ t := by dsimp [t]; omega
  have hwidth : n+w+a+3*bs.length+4 ≤ 4*t := by dsimp [t]; omega
  have hterm : 500*(n+w+a+3*bs.length+4)+1003 ≤ 3003*t := by omega
  have hmul := Nat.mul_le_mul hk hterm
  have hb := cost_le n w a d out bs payload
  change cost n w a d out bs payload ≤ 10000*t^2
  nlinarith [Nat.le_mul_self t]

/-- The existing generic wrapper converts the verified reversed accumulator
into canonical Boolean output with linear overhead. -/
theorem boolean_outputs :
    ∃ C : Nat, ∀ (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool),
      Nonempty (Turing.TM2OutputsInTime
        (ShiTMBooleanWrapper.finiteMachine machine main terminal)
        (packed n w a d out.val bs payload) (some (result n w a d out bs payload))
        (C*cost n w a d out bs payload+4*(packed n w a d out.val bs payload).length+28)) := by
  obtain ⟨C, hc⟩ := ShiTMBooleanWrapper.finite_body_overhead machine main terminal rfl
  refine ⟨C, ?_⟩
  intro n w a d out bs payload
  obtain ⟨U, v, hr, ho⟩ := packed_run n w a d out bs payload
  exact hc _ _ _ _ _ hr ho

/-- Canonical Boolean output on every valid packed input, with one quadratic
bound independent of its verifier fields and coin bits. -/
theorem boolean_quadratic_outputs :
    ∃ C : Nat, ∀ (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool),
      Nonempty (Turing.TM2OutputsInTime
        (ShiTMBooleanWrapper.finiteMachine machine main terminal)
        (packed n w a d out.val bs payload) (some (result n w a d out bs payload))
        (C*cost n w a d out bs payload+4*(packed n w a d out.val bs payload).length+28)) ∧
      C*cost n w a d out bs payload+4*(packed n w a d out.val bs payload).length+28 ≤
        (10000*C+32)*((packed n w a d out.val bs payload).length+1)^2 := by
  obtain ⟨C, hc⟩ := boolean_outputs
  refine ⟨C, ?_⟩
  intro n w a d out bs payload
  refine ⟨hc n w a d out bs payload, ?_⟩
  have hq := Nat.mul_le_mul_left C (cost_quadratic n w a d out bs payload)
  let L := (packed n w a d out.val bs payload).length
  change C*cost n w a d out bs payload+4*L+28 ≤ (10000*C+32)*(L+1)^2
  have hs : 4*L+28 ≤ 32*(L+1)^2 := by nlinarith
  nlinarith

end ShiTMCenteringPacked

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringCoinInput.input_run, ``ShiTMCenteringCoinInput.prefix_length,
      ``ShiTMCenteringFields.fields_run, ``ShiTMCenteringPacked.packed_run,
      ``ShiTMCenteringPacked.cost_le, ``ShiTMCenteringPacked.cost_quadratic,
      ``ShiTMCenteringPacked.boolean_outputs, ``ShiTMCenteringPacked.boolean_quadratic_outputs] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected packed-input axiom {ax} in {name}"
    logInfo m!"CENTERING_PACKED_INPUT_CHECKED {name}; axioms {axioms}"
