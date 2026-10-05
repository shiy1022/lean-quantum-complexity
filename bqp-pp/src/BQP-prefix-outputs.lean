import «BQP-prefix-inputs»
import «BQP-counting-normalization»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPPrefixMachine
open Turing Turing.TM2

 theorem encodePair_eq (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (x w : List Bool) : encodePair tm ea x w = (PvsNP.encodePair (x,w)).map ea.symm := by
  simp [encodePair, PvsNP.encodePair, List.map_append, List.map_map, Function.comp_def]

 def good_outputs (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x w : List Bool) (b : Bool)
    (out : List (tm.Γ tm.k₁)) (t : ℕ)
    (h : TM2OutputsInTime tm (encodePair tm ea x w) (some out) t) :
    TM2OutputsInTime (machine tm ea eb) (encodePair tm ea x (b::b::w))
      (some out) (t+2*x.length+3) := by
  refine { steps := (2*x.length+3)+h.steps
           steps_le_m := by
             have hb := h.steps_le_m
             omega
           evals_in_steps := ?_ }
  have hd := delegated_run tm ea eb h.steps (some (initList tm (encodePair tm ea x w)))
  have he : (ShiTMSubroutine.run tm.m)^[h.steps]
      (some (initList tm (encodePair tm ea x w))) = some (haltList tm out) := h.evals_in_steps
  have hh := hd.trans (congrArg (Option.map (embed tm)) he)
  simp only [Option.map_some, embedded_halt tm ea eb] at hh
  exact iterate_chain _ _ _ _ _ _ (good_prefix tm ea eb x w b) hh

 theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [Polynomial.eval_add]; exact Nat.add_le_add hr hs
  | monomial k a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul (Nat.le_refl a) (Nat.pow_le_pow_left h k)

/-- Two matching witness bits can be removed in polynomial time while preserving
 the full instance. Both rejecting and delegated runs meet the clean-output contract. -/
theorem pairedPrefix_polyTime (R : PvsNP.Str × PvsNP.Str → Bool)
    (hR : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker (BQPCounting.pairedPrefix R) := by
  obtain ⟨M⟩ := hR
  refine ⟨{
    tm := machine M.tm M.inputAlphabet M.outputAlphabet
    inputAlphabet := M.inputAlphabet
    outputAlphabet := M.outputAlphabet
    time := M.time + Polynomial.C 2 * Polynomial.X + Polynomial.C 4
    outputsFun := ?_ }⟩
  rintro ⟨x,w⟩
  let q := M.time + Polynomial.C 2 * Polynomial.X + Polynomial.C 4
  suffices h : TM2OutputsInTime (machine M.tm M.inputAlphabet M.outputAlphabet)
    (encodePair M.tm M.inputAlphabet x w)
    (some [M.outputAlphabet.symm (BQPCounting.pairedPrefix R (x,w))])
    (q.eval (x.length+w.length)) by
    simpa only [machine, framed, encodePair_eq, Computability.encodeBool, List.pure_def, Equiv.invFun_as_coe, List.map_cons, List.map_nil,
      PvsNP.encodePair, List.length_append, List.length_map, q] using h
  have hq : ∀ n, q.eval n = M.time.eval n + 2*n+4 := by
    intro n
    simp [q]
  cases w with
  | nil =>
      refine { steps := 2*x.length+3
               evals_in_steps := empty_witness M.tm M.inputAlphabet M.outputAlphabet x
               steps_le_m := ?_ }
      rw [hq]
      simp only [List.length_nil, Nat.add_zero]
      omega
  | cons b w =>
    cases w with
    | nil =>
      refine { steps := 2*x.length+4
               evals_in_steps := singleton_witness M.tm M.inputAlphabet M.outputAlphabet x b
               steps_le_m := ?_ }
      rw [hq]
      simp only [List.length_cons, List.length_nil]
      omega
    | cons d w =>
      by_cases hbd : b = d
      · subst d
        have ho : TM2OutputsInTime M.tm (encodePair M.tm M.inputAlphabet x w)
            (some [M.outputAlphabet.symm (R (x,w))])
            (M.time.eval (x.length+w.length)) := by
          simpa only [encodePair_eq, Computability.encodeBool, List.pure_def, Equiv.invFun_as_coe, List.map_cons, List.map_nil,
            PvsNP.encodePair, List.length_append, List.length_map] using M.outputsFun (x,w)
        let h := good_outputs M.tm M.inputAlphabet M.outputAlphabet x w b _ _ ho
        have hm : M.time.eval (x.length+w.length) ≤
            M.time.eval (x.length+(b::b::w).length) :=
          eval_mono M.time (by simp only [List.length_cons]; omega)
        have he : BQPCounting.pairedPrefix R (x,b::b::w) = R (x,w) := by
          simp [BQPCounting.pairedPrefix]
        rw [he]
        have ht : h.steps ≤ q.eval (x.length+(b::b::w).length) := by
          have hb := h.steps_le_m
          rw [hq]
          simp only [List.length_cons] at hm ⊢
          omega
        exact { h with steps_le_m := ht }
      · have he : BQPCounting.pairedPrefix R (x,b::d::w) = false := by
          simp [BQPCounting.pairedPrefix, hbd]
        rw [he]
        refine { steps := 2*x.length+w.length+4
                 evals_in_steps := unequal_witness M.tm M.inputAlphabet M.outputAlphabet x w b d hbd
                 steps_le_m := ?_ }
        rw [hq]
        simp only [List.length_cons]
        omega

end BQPPrefixMachine
