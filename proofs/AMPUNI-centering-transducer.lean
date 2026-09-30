import «AMPUNI-centering-packed-input»
import «AMPUNI-general-gap-centered-family»
import «AMPUNI-total-polynomial-clocked-bounds»
import «AMPUNI-total-polynomial-function»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
noncomputable section

namespace ShiTMCenteringPacked

/-- One total polynomial-time transformer assembles every valid packed
centering input. Its clock also halts on malformed strings. -/
theorem polynomial_transducer :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (n w a d : Nat) (out : Fin (n+(w+(a+1)))) (bs payload : List Bool),
        g (packed n w a d out.val bs payload) = result n w a d out bs payload := by
  obtain ⟨C, hc⟩ := boolean_quadratic_outputs
  let tm := ShiTMBooleanWrapper.finiteMachine machine main terminal
  let ein : Bool ≃ tm.Γ tm.k₀ := Equiv.refl Bool
  let full := ShiTMTotalPolynomialClocked.finiteMachine tm ein 1 (10000*C+32)
  obtain ⟨P, hP⟩ := ShiTMTotalPolynomialClocked.total_polynomial tm ein 1 (10000*C+32)
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
  obtain ⟨Q, hQ⟩ := ShiTMTotalPolynomialClocked.valid_run_polynomial tm ein 1 (10000*C+32)
  refine ⟨g, hg, ?_⟩
  intro n w a d out bs payload
  let xs := packed n w a d out.val bs payload
  let ys := result n w a d out bs payload
  obtain ⟨⟨⟨⟨steps, hr⟩, hb⟩⟩, hbound⟩ := hc n w a d out bs payload
  have hin : xs.map ein = xs := List.map_id xs
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm (xs.map ein))) = some (Turing.haltList tm ys) := by
    exact (congrArg (fun input : List (tm.Γ tm.k₀) =>
      (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm input))) hin).trans hr
  have hf := hQ xs steps (Turing.haltList tm ys).var (Turing.haltList tm ys).stk
    hr' (hb.trans hbound)
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

open ShiClassQMA ShiClassQMAU ShiBQP ShiShallow ShiQMACenteringCircuit

/-- The packed format is precisely tagged coin data followed by the
length-aware encoding of the original verifier. -/
theorem packed_family (F : QMAFamily) (bs : List Bool) (n : Nat) :
    packed n (F.wit n) (F.anc n) (depth (F.circ n)) (F.out n).val bs
      ((F.circ n).map encLayer).flatten =
      ShiTMCenteringCoinInput.coinPrefix bs ++ encNat n ++ encQMAFamilyAt F n := by
  simp only [packed, ShiTMCenteringFields.headers, encQMAFamilyAt, encCirc,
    encStr, List.length_map, depth, List.append_assoc]

/-- The assembled headers and unchanged original payload match the
quantum centering construction exactly. -/
theorem result_family (F : QMAFamily) (bits : Nat → List Bool) (n : Nat) :
    result n (F.wit n) (F.anc n) (depth (F.circ n)) (F.out n) (bits n)
      ((F.circ n).map encLayer).flatten = encQMAFamilyAt (centeredFamily F bits) n := by
  rw [centeredFamily_encoding, centeringSuffix_depth_exact]
  simp only [result, ShiTMCenteringEncodedAssembly.header, centeringExtra,
    Nat.add_assoc, List.append_assoc]

/-- Universal polynomial-time centering assembly, with no assumed
centering transducer. The caller supplies the tagged coin bits and source encoding. -/
theorem centered_encoding_transducer :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (F : QMAFamily) (bits : Nat → List Bool) (n : Nat),
        g (ShiTMCenteringCoinInput.coinPrefix (bits n) ++ encNat n ++ encQMAFamilyAt F n) =
          encQMAFamilyAt (centeredFamily F bits) n := by
  obtain ⟨g, hg, h⟩ := polynomial_transducer
  refine ⟨g, hg, ?_⟩
  intro F bits n
  rw [← packed_family F (bits n) n, h, result_family]

end ShiTMCenteringPacked

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMCenteringPacked.polynomial_transducer,
      ``ShiTMCenteringPacked.packed_family, ``ShiTMCenteringPacked.result_family,
      ``ShiTMCenteringPacked.centered_encoding_transducer] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-transducer axiom {ax} in {name}"
    logInfo m!"CENTERING_TRANSDUCER_CHECKED {name}; axioms {axioms}"
