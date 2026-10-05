import «AMPUNI-readout-scratch-prepare»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadoutScratch
open ShiTMLayoutMachine ShiTMRetainedTop

def value (n w a : Nat) : Nat := 3*n+3*w+3*a+3
def cost (n w a : Nat) (S : ∀ k, List (TopGam k)) : Nat :=
  ShiTMFanoutPrepare.cost n w a S+1+(2*n+2)+1+(2*a+2)+1+
    ((S (core 7)).length+1)+(value n w a+1)
def Stable (k : TopK) : Prop := k ≠ core 0 ∧ k ≠ core 1 ∧ k ≠ core 2 ∧ k ≠ core 7

/-- Construct the fourth readout operand from retained resource headers.
Every stack outside the three work registers and register 7 is preserved. -/
theorem prepare_run (n w a : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : ShiTMFanoutPrepare.Retained n w a S) (h3 : S (core 3) = []) :
    ∃ U : ∀ k, List (TopGam k),
      run^[cost n w a S] (some ⟨some (prepLabel (.clear 0)), v, S⟩) =
        some ⟨some (localLabel 2), none, U⟩
      ∧ U (core 7) = List.replicate (value n w a) Cell.mark
      ∧ U (core 2) = [] ∧ U (core 3) = []
      ∧ ∀ k, Stable k → U k = S k := by
  obtain ⟨T, hp, _, _, hT2, hT3, hretT, hTf⟩ :=
    ShiTMFanoutPrepare.prepare_run true n w a v S hret h3
  obtain ⟨A, hn, hA2, hAf⟩ := add_run false n none T (by simpa [source, ShiTMFanoutPrepare.source] using hretT.1) hT3
  obtain ⟨B, ha, hB2, hBf⟩ := add_run true a none A
    (by rw [hAf _ (by simp [core])]; simpa [source, ShiTMFanoutPrepare.source] using hretT.2.2)
    (by rw [hAf _ (by decide)]; exact hT3)
  have hB7 : B (core 7) = S (core 7) := by
    rw [hBf _ (by decide), hAf _ (by decide), hTf _ (by simp [ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, core])]
  have hT2' : T (core 2) = List.replicate (ShiTMFanoutPrepare.base true n w a) Cell.mark := by
    simpa [ShiTMFanoutPrepare.port, ShiTMFanout.port, core] using hT2
  have hbase : Cell.mark :: B (core 2) = List.replicate (value n w a) Cell.mark := by
    rw [hB2, hA2, hT2']
    rw [← List.replicate_add, ← List.replicate_add, ← List.replicate_succ]
    congr 1
    simp [value, ShiTMFanoutPrepare.base]
    omega
  let C := Function.update (Function.update B (core 7) []) (core 2) (Cell.mark :: B (core 2))
  have hc := clear_run (S (core 7)) none B hB7
  obtain ⟨U, hu, hU2, hU7, hUf⟩ := transfer_run (value n w a) none C (by simpa [C] using hbase)
  have hframe (k : TopK) (hk : Stable k) : U k = S k := by
    rcases hk with ⟨hk0, hk1, hk2, hk7⟩
    rw [hUf k hk2 hk7]
    simp only [C, Function.update_of_ne hk2, Function.update_of_ne hk7]
    rw [hBf k hk2, hAf k hk2]
    exact hTf k ⟨hk0, hk1, hk2⟩
  have hj0 : run^[1] (some ⟨some (prepLabel .finished), none, T⟩) =
      some ⟨some (addLabel false (.inr .copy)), none, T⟩ := by
    simp [run, ShiTMSubroutine.run, machine, prepLabel, step, stepAux]
  have hj1 : run^[1] (some ⟨some (addLabel false (.inr .done)), none, A⟩) =
      some ⟨some (addLabel true (.inr .copy)), none, A⟩ := by
    simp [run, ShiTMSubroutine.run, machine, addLabel, step, stepAux]
  have hj2 : run^[1] (some ⟨some (addLabel true (.inr .done)), none, B⟩) =
      some ⟨some (localLabel 0), none, B⟩ := by
    simp [run, ShiTMSubroutine.run, machine, addLabel, step, stepAux]
  have h0 := prep_run _ _ _ _ _ hp
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ h0 hj0
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hn
  have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 hj1
  have h5 := ShiTMFanout.iterTwo run _ _ _ _ _ h4 ha
  have h6 := ShiTMFanout.iterTwo run _ _ _ _ _ h5 hj2
  have h7 := ShiTMFanout.iterTwo run _ _ _ _ _ h6 hc
  have h8 := ShiTMFanout.iterTwo run _ _ _ _ _ h7 hu
  refine ⟨U, h8, ?_, hU2, ?_, hframe⟩
  · simpa [C, core] using hU7
  · rw [hframe _ (by simp [Stable, core])]; exact h3

/-- Linear overhead beyond the old contents of the four cleared stacks. -/
theorem cost_le (n w a L : Nat) (S : ∀ k, List (TopGam k))
    (hlen : n+w+a+1 ≤ L) :
    cost n w a S ≤ (S (core 0)).length+(S (core 1)).length+
      (S (core 2)).length+(S (core 7)).length+30*L := by
  have h0 : (S (ShiTMFanoutPrepare.port 0)).length = (S (core 0)).length := rfl
  have h1 : (S (ShiTMFanoutPrepare.port 1)).length = (S (core 1)).length := rfl
  have h2 : (S (ShiTMFanoutPrepare.port 2)).length = (S (core 2)).length := rfl
  unfold cost value ShiTMFanoutPrepare.cost ShiTMFanoutPrepare.clearCost
  rw [h0, h1, h2]
  omega

end ShiTMReadoutScratch
