import «BQP-map-first-outputs»
import «BQP-closed-references»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2 Polynomial
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin

private theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [Polynomial.eval_add]; exact Nat.add_le_add hr hs
  | monomial k a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul (Nat.le_refl a) (Nat.pow_le_pow_left h k)

/-- Compute on the first component while retaining the entire witness. The
machine and its polynomial clock are constructed from the source computation. -/
theorem map_first_polyTime (f : PvsNP.Str → PvsNP.Str) (hf : PvsNP.PolyTimeComputable f) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : PvsNP.Str × PvsNP.Str => (f p.1,p.2))) := by
  obtain ⟨M⟩ := hf
  obtain ⟨c,hc⟩ := BQPChecked.reference32 M.tm.m
  let q : Polynomial ℕ := (1+C (2*c))*M.time + C 4*X + C 5
  refine ⟨{ tm := machine M.tm M.inputAlphabet M.outputAlphabet
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := q
            outputsFun := ?_ }⟩
  rintro ⟨x,w⟩
  have ho : TM2OutputsInTime M.tm (x.map M.inputAlphabet.symm)
      (some ((f x).map M.outputAlphabet.symm)) (M.time.eval x.length) := M.outputsFun x
  have hy := BQPChecked.reference38 c hc _ _ _ ho
  simp only [List.length_map] at hy
  have hm := eval_mono M.time (Nat.le_add_right x.length w.length)
  have h := outputs M.tm M.inputAlphabet M.outputAlphabet x (f x) w _ ho
  have ht : h.steps ≤ q.eval (x.length+w.length) := by
    have hb := h.steps_le_m
    simp only [q, eval_add, eval_mul, eval_one, eval_C, eval_X]
    nlinarith
  suffices hout : TM2OutputsInTime (machine M.tm M.inputAlphabet M.outputAlphabet)
      (pair x w) (some (pair (f x) w)) (q.eval (x.length+w.length)) by
    simpa only [machine, framed, pair, PvsNP.encodePair, Equiv.refl_symm,
      Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id, List.length_append, List.length_map] using hout
  exact { h with steps_le_m := ht }

/-- Output length is derived from the finite source machine's stack growth. -/
theorem map_first_length_bound (f : PvsNP.Str → PvsNP.Str) (hf : PvsNP.PolyTimeComputable f) :
    ∃ q : Polynomial ℕ, ∀ p : PvsNP.Str × PvsNP.Str,
      (PvsNP.encodePair (f p.1,p.2)).length ≤ q.eval (PvsNP.encodePair p).length := by
  obtain ⟨M⟩ := hf
  obtain ⟨c,hc⟩ := BQPChecked.reference32 M.tm.m
  refine ⟨X + C c * M.time, ?_⟩
  rintro ⟨x,w⟩
  have hy := BQPChecked.reference38 c hc _ _ _ (M.outputsFun x)
  simp only [id_eq, List.length_map] at hy
  have hm := eval_mono M.time (Nat.le_add_right x.length w.length)
  simp only [PvsNP.encodePair, List.length_append, List.length_map,
    eval_add, eval_mul, eval_X, eval_C]
  nlinarith

/-- Checker preprocessing preserves the witness and requires no separate size
or runtime premise beyond polynomial-time computability of the string function. -/
theorem checker_preprocess (f : PvsNP.Str → PvsNP.Str)
    (R : PvsNP.Str × PvsNP.Str → Bool) (hf : PvsNP.PolyTimeComputable f)
    (hR : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker (fun p => R (f p.1,p.2)) := by
  obtain ⟨A⟩ := map_first_polyTime f hf
  obtain ⟨B⟩ := hR
  obtain ⟨q,hq⟩ := map_first_length_bound f hf
  obtain ⟨M, _⟩ := BQPChecked.reference2.2.2.2.2.2.1 R
    (fun p => (f p.1,p.2)) q A B hq
  exact ⟨M⟩

end BQPMapFirst
