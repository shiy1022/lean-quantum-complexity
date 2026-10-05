import «AMPUNI-readout-fields»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadout
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

end ShiTMReadout
