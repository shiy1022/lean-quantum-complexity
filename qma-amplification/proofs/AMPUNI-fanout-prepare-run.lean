import «AMPUNI-fanout-prepare-fields»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2
namespace ShiTMFanoutPrepare
open ShiTMLayoutMachine ShiTMRetainedTop

def Retained (n w a : Nat) (S : ∀ j, List (TopGam j)) : Prop :=
  S (source 0) = List.replicate n Cell.mark ∧
  S (source 1) = List.replicate w Cell.mark ∧
  S (source 2) = List.replicate a Cell.mark

theorem retained_frame {n w a : Nat} {S U : ∀ j, List (TopGam j)}
    (hret : Retained n w a S) (hf : ∀ h : Fin 3, U (source h) = S (source h)) :
    Retained n w a U :=
  ⟨(hf 0).trans hret.1, (hf 1).trans hret.2.1, (hf 2).trans hret.2.2⟩

def Stable (j : TopK) : Prop := j ≠ port 0 ∧ j ≠ port 1 ∧ j ≠ port 2

def base (second : Bool) (n w a : Nat) : Nat :=
  if second then 2*n+3*w+2*a+2 else n+3*w+a+1

def clearCost (S : ∀ j, List (TopGam j)) : Nat :=
  (S (port 0)).length + (S (port 1)).length + (S (port 2)).length + 3

def cost (n w a : Nat) (S : ∀ j, List (TopGam j)) : Nat :=
  clearCost S + 2*(n+w+a) + 7

theorem clear_all_run (second : Bool) (v : Sig) (S : ∀ j, List (TopGam j)) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[clearCost S] (some ⟨some (.clear 0), v, S⟩) =
        some ⟨some .start, none, U⟩
      ∧ U (port 0) = [] ∧ U (port 1) = [] ∧ U (port 2) = []
      ∧ ∀ j, Stable j → U j = S j := by
  let T := Function.update S (port 0) []
  let V := Function.update T (port 1) []
  let U := Function.update V (port 2) []
  have h0 := clear_run second 0 (S (port 0)) v S rfl
  have h1 := clear_run second 1 (S (port 1)) none T (by simp [T])
  have h2 := clear_run second 2 (S (port 2)) none V (by simp [V, T])
  rw [show afterClear 0 = .clear 1 from rfl] at h0
  rw [show afterClear 1 = .clear 2 from rfl] at h1
  rw [show afterClear 2 = .start from rfl] at h2
  have h01 := ShiTMFanout.iterTwo (run second) _ _ _ _ _ h0 h1
  have h012 := ShiTMFanout.iterTwo (run second) _ _ _ _ _ h01 h2
  refine ⟨U, ?_, by simp [U, V, T], by simp [U, V], by simp [U], ?_⟩
  · have hc : ((S (port 0)).length+1+((S (port 1)).length+1)) +
        ((S (port 2)).length+1) = clearCost S := by unfold clearCost; omega
    simpa only [hc] using h012
  · intro j hj
    simp [U, V, T, hj.1, hj.2.1, hj.2.2]

/-- The three retained headers build both fanout registers in linear time.
All other stacks, including output, source circuit, and archive, are unchanged. -/
theorem fields_run (second : Bool) (n w a : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hret : Retained n w a S)
    (h0 : S (port 0) = []) (h2 : S (port 2) = []) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[2*(n+w+a)+7] (some ⟨some .start, v, S⟩) =
        some ⟨some .finished, none, U⟩
      ∧ U (port 0) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate (base second n w a) Cell.mark
      ∧ U scratch = []
      ∧ ∀ j, j ≠ port 0 → j ≠ port 2 → U j = S j := by
  let T := Function.update S (port 2) (List.replicate (seed second) Cell.mark)
  have hstart : (run second)^[1] (some ⟨some .start, v, S⟩) =
      some ⟨some (.copy 0), v, T⟩ := by
    simp [run, machine, step, pushMarks_step, stepAux, h2, T]
  obtain ⟨A, ha, hA0, hA2, hAt, hAf⟩ :=
    field_run second 0 n v T (by simpa [T] using hret.1) (by simpa [T] using ht)
  obtain ⟨B, hb, hB0, hB2, hBt, hBf⟩ :=
    field_run second 1 w none A
      (by rw [hAf (source 1) (by simp) (by simp)]; simpa [T] using hret.2.1) hAt
  obtain ⟨U, hu, hU0, hU2, hUt, hUf⟩ :=
    field_run second 2 a none B
      (by rw [hBf (source 2) (by simp) (by simp),
              hAf (source 2) (by simp) (by simp)]; simpa [T] using hret.2.2) hBt
  rw [show afterField 0 = .copy 1 from rfl] at ha
  rw [show afterField 1 = .copy 2 from rfl] at hb
  rw [show afterField 2 = .finished from rfl] at hu
  refine ⟨U, ?_, ?_, ?_, hUt, ?_⟩
  · have hsa := ShiTMFanout.iterTwo (run second) _ _ _ _ _ hstart ha
    have hsab := ShiTMFanout.iterTwo (run second) _ _ _ _ _ hsa hb
    have hall := ShiTMFanout.iterTwo (run second) _ _ _ _ _ hsab hu
    have hc : ((1+(2*n+2))+(2*w+2))+(2*a+2) = 2*(n+w+a)+7 := by omega
    simpa only [hc] using hall
  · rw [hU0, hB0, hA0]
    simp [countCoeff, T, h0]
  · rw [hU2, hB2, hA2]
    simp only [T, Function.update_self]
    rw [← List.replicate_add, ← List.replicate_add, ← List.replicate_add]
    congr 1
    cases second <;> norm_num [base, baseCoeff, seed, show (2 : Fin 3) ≠ 1 by decide] <;> omega
  · intro j hj0 hj2
    rw [hUf j hj0 hj2, hBf j hj0 hj2, hAf j hj0 hj2]
    simp [T, hj2]

/-- Ready-to-emit state from retained headers and arbitrary old work registers.
Scratch must be empty; all three work registers are explicitly cleared first. -/
theorem prepare_run (second : Bool) (n w a : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hret : Retained n w a S) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      (run second)^[cost n w a S] (some ⟨some (.clear 0), v, S⟩) =
        some ⟨some .finished, none, U⟩
      ∧ U (port 0) = List.replicate n Cell.mark
      ∧ U (port 1) = []
      ∧ U (port 2) = List.replicate (base second n w a) Cell.mark
      ∧ U scratch = []
      ∧ Retained n w a U
      ∧ ∀ j, Stable j → U j = S j := by
  obtain ⟨T, hc, h0, h1, h2, hf⟩ := clear_all_run second v S
  have hretT : Retained n w a T := by
    exact retained_frame hret (fun h => hf (source h) (by simp [Stable]))
  have htT : T scratch = [] := by rw [hf scratch (by simp [Stable]), ht]
  obtain ⟨U, hr, hu0, hu2, hut, huf⟩ := fields_run second n w a none T hretT h0 h2 htT
  have hframe : ∀ j, Stable j → U j = S j := by
    intro j hj
    rw [huf j hj.1 hj.2.2, hf j hj]
  refine ⟨U, ?_, hu0, ?_, hu2, hut, ?_, hframe⟩
  · simpa [cost, Nat.add_assoc] using
      ShiTMFanout.iterTwo (run second) _ _ _ _ _ hc hr
  · rw [huf (port 1) (by decide) (by decide), h1]
  · exact retained_frame hret (fun h => hframe (source h) (by simp [Stable]))

end ShiTMFanoutPrepare
