import «AMPUNI-readout-command»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadout
open ShiTMLayoutMachine ShiTMRetainedTop

private theorem active_suffix (pc : PC) (c : Command) (xs : List Command)
    (hs : program.drop pc.val = c :: xs) :
    commandAt pc = some c ∧ (nextPC pc).val = pc.val+1 ∧
      program.drop (nextPC pc).val = xs := by
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_cons, program_length] at hlen
  have hnext : (nextPC pc).val = pc.val+1 := by
    apply Nat.mod_eq_of_lt
    omega
  refine ⟨?_, hnext, ?_⟩
  · simp [commandAt, hs]
  · rw [hnext, ← List.drop_drop, hs]; rfl

theorem run_suffix (xs : List Command) (values : Fin 4 → Nat)
    (pc : PC) (v : Sig) (S : ∀ j, List (TopGam j))
    (hs : program.drop pc.val = xs)
    (hvalues : ∀ h, S (wire h) = List.replicate (values h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig) (pc' : PC),
      run^[scheduleCost values xs] (some ⟨some (.dispatch pc), v, S⟩) =
        some ⟨some (.dispatch pc'), v', U⟩
      ∧ pc'.val = pc.val+xs.length
      ∧ U output = ((xs.map (bytes values)).flatten).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  induction xs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, by simp, by intro j _; rfl⟩
  | cons c xs ih =>
      obtain ⟨hc, hn, hs'⟩ := active_suffix pc c xs hs
      obtain ⟨T, w, hfirst, hTo, hTf⟩ := command_run pc c values v S hc hvalues ht
      obtain ⟨U, w', pc', hrest, hp, hUo, hUf⟩ :=
        ih (nextPC pc) w T hs'
          (fun h => (hTf (wire h) (wire_ne_output h)).trans (hvalues h))
          ((hTf scratch (by decide)).trans ht)
      refine ⟨U, w', pc', ?_, ?_, ?_, ?_⟩
      · change run^[commandCost values c + scheduleCost values xs]
          (some ⟨some (.dispatch pc), v, S⟩) =
            some ⟨some (.dispatch pc'), w', U⟩
        exact ShiTMFanout.iterTwo run _ _ _ _ _ hfirst hrest
      · rw [hn] at hp
        simp only [List.length_cons]
        omega
      · rw [hUo, hTo]
        simp [List.reverse_append, List.append_assoc]
      · intro j hj; rw [hUf j hj, hTf j hj]

/-- The fixed 111-gate readout program emits its payload, retaining all four
wire registers and every other stack except output. Scratch is empty again. -/
theorem program_run (values : Fin 4 → Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (wire h) = List.replicate (values h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost values program + 1] (some ⟨some (.dispatch 0), v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U output = (programBytes values).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  obtain ⟨U, v', pc', hr, hp, ho, hf⟩ :=
    run_suffix program values 0 v S (by simp) hvalues ht
  have hc : commandAt pc' = none := by
    simp only [Fin.val_zero, Nat.zero_add] at hp
    simp [commandAt, hp]
  have hdone : run^[1] (some ⟨some (.dispatch pc'), v', U⟩) =
      some ⟨some .finished, v', U⟩ := by simp [run, machine, hc, step, stepAux]
  exact ⟨U, v', ShiTMFanout.iterTwo run _ _ _ _ _ hr hdone, ho, hf⟩

theorem scheduleCost_le (xs : List Command) (values : Fin 4 → Nat) (M : Nat)
    (hv : ∀ h, values h ≤ M) : scheduleCost values xs ≤ xs.length*(2*M+4) := by
  induction xs with
  | nil => simp [scheduleCost]
  | cons c xs ih =>
      have hc : commandCost values c ≤ 2*M+4 := by
        cases c with
        | inl k => simp [commandCost]
        | inr k => have h := hv k; simp only [commandCost]; omega
      simp only [scheduleCost, List.map_cons, List.sum_cons] at *
      simp only [List.length_cons, Nat.add_mul]
      omega

theorem program_cost_le (values : Fin 4 → Nat) (M : Nat) (hv : ∀ h, values h ≤ M) :
    scheduleCost values program + 1 ≤ 726*M+1453 := by
  have h := scheduleCost_le program values M hv
  rw [program_length] at h
  omega

end ShiTMReadout
