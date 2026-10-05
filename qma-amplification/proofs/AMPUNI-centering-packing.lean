import «AMPUNI-centering-transducer»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
open Turing Turing.TM2
noncomputable section

namespace ShiTMCenteringTag
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev source : TopK := .inl (.inl 11)
abbrev count : TopK := .inl (.inl 10)
abbrev output : TopK := .inl (.inl 13)

inductive Label where
  | scan | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [Label.scan, Label.finished]
  (by intro l; cases l <;> simp)

/-- Consume exactly the counted coin bits and emit their tagged encoding.
The uncounted source suffix is left for the payload copier. -/
def machine : Label → Stmt TopGam Label Sig
  | .scan => .pop count pop (.branch isSome
      (.pop source pop (.push output (cst Cell.mark)
        (.push output ShiTMLayoutMachine.get (.goto (fun _ => .scan)))))
      (.push output (cst Cell.delim) (.goto (fun _ => .finished))))
  | .finished => .halt

def run := ShiTMSubroutine.run machine

theorem tag_run (bs : List Bool) (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : S source = bs.map bit ++ rest) (hc : S count = List.replicate bs.length Cell.mark) :
    ∃ U : ∀ j, List (TopGam j),
      run^[bs.length+1] (some ⟨some .scan, v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U source = rest ∧ U count = []
      ∧ U output = ((ShiTMCenteringCoinInput.coinPrefix bs).map bit).reverse ++ S output
      ∧ ∀ j, j ≠ source → j ≠ count → j ≠ output → U j = S j := by
  induction bs generalizing v S with
  | nil =>
    have hz : S count = [] := by simpa using hc
    have hu : Function.update S count [] = S := by
      rw [← hz]
      exact Function.update_eq_self _ _
    refine ⟨Function.update S output (Cell.delim :: S output), ?_, ?_, ?_, ?_, ?_⟩
    · simp [run, ShiTMSubroutine.run, machine, step, stepAux, hc, pop, isSome, cst, hu]
    · simpa [source, output] using hs
    · simp [count, output, hc]
    · simp [ShiTMCenteringCoinInput.coinPrefix, bit]
    · intro j _ _ hj; exact Function.update_of_ne hj _ _
  | cons b bs ih =>
    let T := Function.update (Function.update (Function.update S count (List.replicate bs.length Cell.mark))
      source (bs.map bit ++ rest)) output (bit b :: Cell.mark :: S output)
    have first : run (some ⟨some .scan, v, S⟩) = some ⟨some .scan, some (bit b), T⟩ := by
      simp [run, ShiTMSubroutine.run, machine, step, stepAux, hc, hs, pop, isSome,
        ShiTMLayoutMachine.get, cst, T, source, count, output, List.replicate_succ]
    obtain ⟨U, ur, us, uc, uo, uf⟩ := ih (some (bit b)) T
      (by simp [T, source, count, output]) (by simp [T, source, count, output])
    refine ⟨U, ?_, us, uc, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, first]; exact ur
    · rw [uo]
      simp [ShiTMCenteringCoinInput.coinPrefix, List.reverse_cons, List.append_assoc, T, bit]
    · intro j hjs hjc hjo; rw [uf j hjs hjc hjo]; simp [T, hjs, hjc, hjo]

end ShiTMCenteringTag

namespace ShiTMCenteringPacking
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev Label := ShiTMCenteringDepthParser.Label ⊕ (ShiTMCenteringTag.Label ⊕ ShiTMCenteringPayload.Label)
instance : DecidableEq Label := by classical exact inferInstance

def machine : Label → Stmt TopGam Label Sig
  | .inl .finished => .goto (fun _ => .inr (.inl .scan))
  | .inl l => ShiTMSubroutine.stmt Sum.inl (ShiTMCenteringDepthParser.machine l)
  | .inr (.inl .finished) => .goto (fun _ => .inr (.inr .copy))
  | .inr (.inl l) => ShiTMSubroutine.stmt (fun l => .inr (.inl l)) (ShiTMCenteringTag.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt (fun l => .inr (.inr l)) (ShiTMCenteringPayload.machine l)

def run := ShiTMSubroutine.run machine
def main : Label := .inl .scan
def terminal : Label := .inr (.inr .finished)

def input (bs rest : List Bool) : List Bool := ShiBQP.encNat bs.length ++ bs ++ rest
def result (bs rest : List Bool) : List Bool := ShiTMCenteringCoinInput.coinPrefix bs ++ rest

theorem input_length (bs rest : List Bool) : (input bs rest).length = 2*bs.length+rest.length+1 := by
  simp [input, ShiBQP.encNat]; omega

/-- Parse the length, tag precisely that many bits, then copy the entire suffix.
The body takes input length plus four steps on every valid packed pair. -/
theorem packing_run (bs rest : List Bool) :
    ∃ U : ∀ j, List (TopGam j),
      run^[2*bs.length+rest.length+5]
        (some ⟨some main, none, ShiTMBooleanWrapper.initialTop (input bs rest)⟩) =
          some ⟨some terminal, none, U⟩
      ∧ U ShiTMCenteringTag.output = ((result bs rest).map bit).reverse := by
  let S := ShiTMBooleanWrapper.initialTop (input bs rest)
  have hs : S ShiTMCenteringDepthParser.source = (ShiBQP.encNat bs.length ++ (bs ++ rest)).map bit := by
    simp [S, ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource,
      ShiTMCenteringDepthParser.source, input, List.append_assoc]
  have hc : S ShiTMCenteringDepthParser.depth = [] := by
    simp [S, ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource, ShiTMCenteringDepthParser.depth]
  have ho : S ShiTMCenteringTag.output = [] := by
    simp [S, ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource, ShiTMCenteringTag.output]
  obtain ⟨A, ar, asrc, acount, af⟩ := ShiTMCenteringDepthParser.encoded_depth_run bs.length (bs++rest) none S hs hc
  have la := ShiTMSubroutine.run_to_terminal ShiTMCenteringDepthParser.machine machine Sum.inl
    .finished rfl (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl ar
  have bridgeA : run^[1] (some ⟨some (.inl .finished), some Cell.delim, A⟩) =
      some ⟨some (.inr (.inl .scan)), some Cell.delim, A⟩ := rfl
  obtain ⟨B, br, bsrc, _, bout, _⟩ := ShiTMCenteringTag.tag_run bs (rest.map bit) (some Cell.delim) A
    (by simpa only [List.map_append] using asrc) acount
  have lb := ShiTMSubroutine.run_to_terminal ShiTMCenteringTag.machine machine
    (fun l => .inr (.inl l)) .finished rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim) _ _ _ rfl br
  have bridgeB : run^[1] (some ⟨some (.inr (.inl .finished)), none, B⟩) =
      some ⟨some (.inr (.inr .copy)), none, B⟩ := rfl
  have bout' : B ShiTMCenteringPayload.output = ((ShiTMCenteringCoinInput.coinPrefix bs).map bit).reverse := by
    rw [bout, af _ (by decide) (by decide), ho, List.append_nil]
  obtain ⟨U, ur, _, uo, _⟩ := ShiTMCenteringPayload.copy_after_header rest
    (ShiTMCenteringCoinInput.coinPrefix bs) none B bsrc bout'
  have lu := ShiTMSubroutine.run_to_terminal ShiTMCenteringPayload.machine machine
    (fun l => .inr (.inr l)) .finished rfl (fun _ _ => rfl) _ _ _ rfl ur
  refine ⟨U, ?_, uo⟩
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ la bridgeA
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 lb
  have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 bridgeB
  have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h3 lu
  have ht : ((bs.length+1)+1+(bs.length+1))+1+(rest.length+1) = 2*bs.length+rest.length+5 := by omega
  simpa only [ht, main, terminal, ShiTMSubroutine.cfg, Option.map_some] using h4

/-- The canonical Boolean packing machine has a uniform linear valid-input bound. -/
theorem boolean_linear_outputs :
    ∃ C : Nat, ∀ bs rest : List Bool,
      Nonempty (Turing.TM2OutputsInTime
        (ShiTMBooleanWrapper.finiteMachine machine main terminal)
        (input bs rest) (some (result bs rest))
        (C*(2*bs.length+rest.length+5)+4*(input bs rest).length+28)) ∧
      C*(2*bs.length+rest.length+5)+4*(input bs rest).length+28 ≤
        (5*C+32)*((input bs rest).length+1) := by
  obtain ⟨C, hC⟩ := ShiTMBooleanWrapper.finite_body_overhead machine main terminal rfl
  refine ⟨C, ?_⟩
  intro bs rest
  obtain ⟨U, hr, ho⟩ := packing_run bs rest
  refine ⟨hC _ _ _ _ _ hr ho, ?_⟩
  have hl := input_length bs rest
  have hb : 2*bs.length+rest.length+5 ≤ 5*((input bs rest).length+1) := by omega
  have hm := Nat.mul_le_mul_left C hb
  nlinarith

/-- Total polynomial-time serialization of a length-delimited pair into
exactly the tagged format consumed by the centering assembler. -/
theorem polynomial_transducer :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ bs rest : List Bool, g (input bs rest) = result bs rest := by
  obtain ⟨C, hc⟩ := boolean_linear_outputs
  let tm := ShiTMBooleanWrapper.finiteMachine machine main terminal
  let ein : Bool ≃ tm.Γ tm.k₀ := Equiv.refl Bool
  let full := ShiTMTotalPolynomialClocked.finiteMachine tm ein 0 (5*C+32)
  obtain ⟨P, hP⟩ := ShiTMTotalPolynomialClocked.total_polynomial tm ein 0 (5*C+32)
  have hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (Turing.TM2OutputsInTime full (xs.map (Equiv.refl Bool).symm)
        (some (ys.map (Equiv.refl Bool).symm)) (P.eval xs.length)) := by
    intro xs
    obtain ⟨ys, hy⟩ := hP xs
    have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
    have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
    have heq := congrArg₂ (fun (a b : List Bool) =>
      Nonempty (Turing.TM2OutputsInTime full a (some b) (P.eval xs.length))) hin hout
    exact ⟨ys, heq.mpr hy⟩
  obtain ⟨g, hg, hunique⟩ := ShiTMTotalFunction.function_of_total_polynomial full
    (Equiv.refl Bool) (Equiv.refl Bool) P hall
  obtain ⟨Q, hQ⟩ := ShiTMTotalPolynomialClocked.valid_run_polynomial tm ein 0 (5*C+32)
  refine ⟨g, hg, ?_⟩
  intro bs rest
  let xs := input bs rest
  let ys := result bs rest
  obtain ⟨⟨⟨⟨steps, hr⟩, hb⟩⟩, hbound⟩ := hc bs rest
  have hin : xs.map ein = xs := List.map_id xs
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm (xs.map ein))) = some (Turing.haltList tm ys) := by
    exact (congrArg (fun input : List (tm.Γ tm.k₀) =>
      (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm input))) hin).trans hr
  have hsteps : steps ≤ (5*C+32)*(xs.length+1)^(0+1) := by simpa using hb.trans hbound
  have hf := hQ xs steps (Turing.haltList tm ys).var (Turing.haltList tm ys).stk hr' hsteps
  have hout : (Turing.haltList tm ys).stk tm.k₁ = ys := by
    simp only [Turing.haltList]
    rw [dif_pos trivial]
    rfl
  have hf' : Nonempty (Turing.TM2OutputsInTime full xs (some ys) (Q.eval xs.length)) :=
    (congrArg (fun output : List Bool =>
      Nonempty (Turing.TM2OutputsInTime full xs (some output) (Q.eval xs.length))) hout).mp hf
  apply hunique xs ys (Q.eval xs.length)
  have hin' : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
  have hout' : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
  exact (congrArg₂ (fun (a b : List Bool) =>
    Nonempty (Turing.TM2OutputsInTime full a (some b) (Q.eval xs.length))) hin' hout').mpr hf'

/-- Use the reconstructed composition proof, whose dependencies contain no
reference placeholders. -/
theorem polyTimeComputable_comp (f g : PvsNP.Str → PvsNP.Str)
    (hf : PvsNP.PolyTimeComputable f) (hg : PvsNP.PolyTimeComputable g) :
    PvsNP.PolyTimeComputable (g ∘ f) := by
  exact QMAReferenceRebuilt.«QMAReferenceValidation.candidate0» f g hf hg

/-- A length-delimited coin/source pair suffices to generate the centered
verifier. Both the packing machine and the assembler are constructed here. -/
theorem centered_encoding_from_pair_transducer :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (F : ShiClassQMA.QMAFamily) (bits : Nat → List Bool) (n : Nat),
        g (input (bits n) (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)) =
          ShiClassQMAU.encQMAFamilyAt (ShiQMACenteringCircuit.centeredFamily F bits) n := by
  obtain ⟨pack, hpack, hp⟩ := polynomial_transducer
  obtain ⟨assemble, hassemble, ha⟩ := ShiTMCenteringPacked.centered_encoding_transducer
  refine ⟨assemble ∘ pack, polyTimeComputable_comp pack assemble hpack hassemble, ?_⟩
  intro F bits n
  rw [Function.comp_apply, hp]
  simpa only [result, List.append_assoc] using ha F bits n

end ShiTMCenteringPacking

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringTag.tag_run, ``ShiTMCenteringPacking.input_length,
      ``ShiTMCenteringPacking.packing_run, ``ShiTMCenteringPacking.boolean_linear_outputs,
      ``ShiTMCenteringPacking.polynomial_transducer, ``ShiTMCenteringPacking.polyTimeComputable_comp,
      ``ShiTMCenteringPacking.centered_encoding_from_pair_transducer] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-packing axiom {ax} in {name}"
    logInfo m!"CENTERING_PACKING_CHECKED {name}; axioms {axioms}"
