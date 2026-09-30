import «AMPUNI-fanout-machine»
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2

namespace ShiTMFanout

open ShiTMLayoutMachine ShiTMOuterLift

def unary (n : Nat) : List Cell := List.replicate n .mark ++ [.delim]
def gateBytes (b j : Nat) : List Cell := unary 4 ++ unary j ++ unary (b+j)
def recordBytes (b : Nat) : Nat → Nat → List Cell
  | _, 0 => []
  | j, n+1 => gateBytes b j ++ recordBytes b (j+1) n

def loopCost (b : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | j, n+1 => (2*b+4*j+7) + loopCost b (j+1) n

def Outside (k : OuterK) : Prop :=
  k ≠ port 0 ∧ k ≠ port 1 ∧ k ≠ port 2 ∧ k ≠ scratch ∧ k ≠ output

/-- Emit one CNOT, advance both unary indices, and consume one gate-count
mark. The retained source and layer counter are outside the write set. -/
theorem cycle_run (b j n : Nat) (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate (n+1) Cell.mark)
    (hj : S (port 1) = List.replicate j Cell.mark)
    (hb : S (port 2) = List.replicate (b+j) Cell.mark)
    (hs : S scratch = []) :
    ∃ Z : ∀ k, List (OuterGam k),
      run^[2*b+4*j+7] (some ⟨some .driver, v, S⟩) =
        some ⟨some .driver, none, Z⟩
      ∧ Z (port 0) = List.replicate n Cell.mark
      ∧ Z (port 1) = List.replicate (j+1) Cell.mark
      ∧ Z (port 2) = List.replicate (b+(j+1)) Cell.mark
      ∧ Z scratch = []
      ∧ Z output = (gateBytes b j).reverse ++ S output
      ∧ ∀ k, Outside k → Z k = S k := by
  let T := Function.update
    (Function.update S (port 0) (List.replicate n Cell.mark))
    output (Cell.delim :: List.replicate 4 Cell.mark ++ S output)
  have hfirst : run^[1] (some ⟨some .driver, v, S⟩) =
      some ⟨some (.copy 1), some Cell.mark, T⟩ := by
    have hn' : S (.inl (0 : Fin 14)) = List.replicate (n+1) Cell.mark := hn
    simp [run, machine, step, stepAux, hn', List.replicate_succ,
      pop, isSome, cst, T, port, output]
  obtain ⟨U, hu, huj, huo, hus, huf⟩ :=
    field_run 1 j (some Cell.mark) T
      (by simpa [T, port, output] using hj)
      (by simpa [T, port, output, scratch] using hs)
  let V := Function.update U output (Cell.delim :: U output)
  have hdelim1 : run^[1] (some ⟨some (.delimiter 1), none, U⟩) =
      some ⟨some (.copy 2), none, V⟩ := by
    simp [run, machine, step, stepAux, cst, V]
  have hVb : V (port 2) = List.replicate (b+j) Cell.mark := by
    have h := huf (port 2) (by decide) (by decide) (by decide)
    simpa [V, T, port, output] using h.trans (by simpa [T, port, output] using hb)
  obtain ⟨W, hw, hwb, hwo, hws, hwf⟩ :=
    field_run 2 (b+j) none V hVb (by simpa [V, scratch, output] using hus)
  let Z := Function.update
    (Function.update (Function.update W output (Cell.delim :: W output))
      (port 1) (Cell.mark :: W (port 1)))
    (port 2) (Cell.mark :: W (port 2))
  have hdelim2 : run^[1] (some ⟨some (.delimiter 2), none, W⟩) =
      some ⟨some .driver, none, Z⟩ := by
    simp [run, machine, step, stepAux, cst, Z, port, output]
  have hWj : W (port 1) = List.replicate j Cell.mark := by
    rw [hwf (port 1) (by decide) (by decide) (by decide)]
    simpa [V, port, output] using huj
  have hWn : W (port 0) = List.replicate n Cell.mark := by
    rw [hwf (port 0) (by decide) (by decide) (by decide)]
    have h := huf (port 0) (by decide) (by decide) (by decide)
    simpa [V, T, port, output] using h
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := iterTwo run 1 (2*j+2) _ _ _ hfirst hu
    have h2 := iterTwo run (1+(2*j+2)) 1 _ _ _ h1 hdelim1
    have h3 := iterTwo run ((1+(2*j+2))+1) (2*(b+j)+2) _ _ _ h2 hw
    have h4 := iterTwo run (((1+(2*j+2))+1)+(2*(b+j)+2)) 1 _ _ _ h3 hdelim2
    have hc : (((1+(2*j+2))+1)+(2*(b+j)+2))+1 = 2*b+4*j+7 := by omega
    simpa only [hc] using h4
  · simpa [Z, port, output] using hWn
  · simpa [Z, port, output, List.replicate_succ] using
      congrArg (fun xs => Cell.mark :: xs) hWj
  · have ha : b+(j+1) = (b+j)+1 := by omega
    simpa [Z, port, output, ha, List.replicate_succ] using
      congrArg (fun xs => Cell.mark :: xs) hwb
  · simpa [Z, port, output, scratch] using hws
  · simp [Z, port, output, hwo, V, huo, T, gateBytes, unary,
      List.reverse_append, List.append_assoc]
  · intro k hk
    rcases hk with ⟨hk0, hk1, hk2, hks, hko⟩
    have hZ : Z k = W k := by simp [Z, hk1, hk2, hko]
    rw [hZ, hwf k hk2 hko hks]
    have hV : V k = U k := by simp [V, hko]
    rw [hV, huf k hk1 hko hks]
    simp [T, hk0, hko]

/-- All gate records are emitted in order, with exact residual register
values. The statement includes zero gates and an arbitrary output accumulator. -/
theorem loop_run (b j n : Nat) (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate n Cell.mark)
    (hj : S (port 1) = List.replicate j Cell.mark)
    (hb : S (port 2) = List.replicate (b+j) Cell.mark)
    (hs : S scratch = []) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[loopCost b j n] (some ⟨some .driver, v, S⟩) =
        some ⟨some .finished, none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate (j+n) Cell.mark
      ∧ U (port 2) = List.replicate (b+(j+n)) Cell.mark
      ∧ U scratch = []
      ∧ U output = (recordBytes b j n).reverse ++ S output
      ∧ ∀ k, Outside k → U k = S k := by
  induction n generalizing j v S with
  | zero =>
      have he : S (port 0) = [] := by simpa using hn
      refine ⟨S, ?_, he, by simpa using hj, by simpa using hb, hs,
        by simp [recordBytes], by intro k _; rfl⟩
      simp [loopCost, run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      obtain ⟨T, ht, htn, htj, htb, hts, hto, htf⟩ := cycle_run b j n v S hn hj hb hs
      obtain ⟨U, hu, hun, huj, hub, hus, huo, huf⟩ :=
        ih (j+1) none T htn htj htb hts
      refine ⟨U, ?_, hun, ?_, ?_, hus, ?_, ?_⟩
      · exact iterTwo run (2*b+4*j+7) (loopCost b (j+1) n) _ _ _ ht hu
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using huj
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hub
      · rw [huo, hto]
        simp [recordBytes, List.reverse_append, List.append_assoc]
      · intro k hk
        rw [huf k hk, htf k hk]

theorem loopCost_eq (b j n : Nat) :
    loopCost b j n = 2*n*n + n*(2*b+4*j+5) + 1 := by
  induction n generalizing j with
  | zero => simp [loopCost]
  | succ n ih =>
      rw [loopCost, ih]
      ring

/-- One complete fanout layer, including its unary gate count. Preparation
of the count and target-base registers remains an enclosing-controller task. -/
theorem fanout_run (n b : Nat) (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate n Cell.mark)
    (hj : S (port 1) = []) (hb : S (port 2) = List.replicate b Cell.mark)
    (hs : S scratch = []) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[2*n*n + n*(2*b+7) + 4] (some ⟨some (.copy 0), v, S⟩) =
        some ⟨some .finished, none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate (b+n) Cell.mark
      ∧ U scratch = []
      ∧ U output = (unary n ++ recordBytes b 0 n).reverse ++ S output
      ∧ ∀ k, Outside k → U k = S k := by
  obtain ⟨T, ht, htn, hto, hts, htf⟩ := field_run 0 n v S hn hs
  let V := Function.update T output (Cell.delim :: T output)
  have hd : run^[1] (some ⟨some (.delimiter 0), none, T⟩) =
      some ⟨some .driver, none, V⟩ := by
    simp [run, machine, step, stepAux, cst, V]
  have hVn : V (port 0) = List.replicate n Cell.mark := by
    simpa [V, port, output] using htn
  have hVj : V (port 1) = List.replicate 0 Cell.mark := by
    have h := htf (port 1) (by decide) (by decide) (by decide)
    simpa [V, port, output] using h.trans hj
  have hVb : V (port 2) = List.replicate (b+0) Cell.mark := by
    have h := htf (port 2) (by decide) (by decide) (by decide)
    simpa [V, port, output] using h.trans hb
  obtain ⟨U, hu, hun, huj, hub, hus, huo, huf⟩ := loop_run b 0 n none V hVn hVj hVb
    (by simpa [V, scratch, output] using hts)
  refine ⟨U, ?_, hun, by simpa using huj, by simpa using hub, hus, ?_, ?_⟩
  · have h1 := iterTwo run (2*n+2) 1 _ _ _ ht hd
    have h2 := iterTwo run ((2*n+2)+1) (loopCost b 0 n) _ _ _ h1 hu
    have hc : ((2*n+2)+1) + loopCost b 0 n = 2*n*n+n*(2*b+7)+4 := by
      rw [loopCost_eq]
      ring
    simpa only [hc] using h2
  · rw [huo]
    simp [V, hto, unary, List.reverse_append, List.append_assoc]
  · intro k hk
    rcases hk with ⟨hk0, hk1, hk2, hks, hko⟩
    rw [huf k ⟨hk0, hk1, hk2, hks, hko⟩]
    have hV : V k = T k := by simp [V, hko]
    rw [hV, htf k hk0 hko hks]

/-- The recursive emission order is the circuit encoder's finite-index order. -/
theorem recordBytes_finRange (b j n : Nat) :
    recordBytes b j n =
      ((List.finRange n).map (fun i => gateBytes b (j+i.val))).flatten := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      simp [recordBytes, List.finRange_succ, ih, List.map_map,
        Function.comp_def, Nat.add_comm, Nat.add_left_comm]

end ShiTMFanout
