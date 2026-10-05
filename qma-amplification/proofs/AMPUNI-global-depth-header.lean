import «AMPUNI-outer-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMGlobalDepthHeader

open ShiTMLayoutMachine ShiTMOuterLift

abbrev source : OuterK := .inl (11 : Fin 14)
abbrev output : OuterK := .inl (13 : Fin 14)
abbrev counter : OuterK := .inr (0 : Fin 2)

/-- A fixed finite statement, not a loop with an unbounded control state. -/
def pushMarks : Nat → Stmt OuterGam Bool Sig → Stmt OuterGam Bool Sig
  | 0, q => q
  | n + 1, q => .push output (cst .mark) (pushMarks n q)

theorem stepAux_pushMarks (n : Nat) (q : Stmt OuterGam Bool Sig)
    (v : Sig) (S : ∀ k, List (OuterGam k)) :
    stepAux (pushMarks n q) v S =
      stepAux q v (Function.update S output
        (List.replicate n Cell.mark ++ S output)) := by
  induction n generalizing S with
  | zero => simp [pushMarks]
  | succ n ih =>
      simp only [pushMarks, stepAux]
      rw [ih]
      simp [cst, List.replicate_succ', List.append_assoc]

/-- Read depth `d`, retain `d` layer-counter marks, and emit the reverse
encoding of `3*d+113`. The finished label is an integration handoff. -/
def machine : Bool → Stmt OuterGam Bool Sig
  | true => .halt
  | false =>
      .pop source pop
        (.branch isSome
          (.branch isMark
            (.push counter (cst .mark)
              (pushMarks 3 (.goto (fun _ => false))))
            (pushMarks 113
              (.push output (cst .delim) (.goto (fun _ => true)))))
          .halt)

def run : Option (Cfg OuterGam Bool Sig) → Option (Cfg OuterGam Bool Sig) :=
  fun c => c.bind (step machine)

/-- A fixed finite machine; callers supply the circuit header on stack 11. -/
def finiteMachine : Turing.FinTM2 where
  K := OuterK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := source
  k₁ := output
  Γ := OuterGam
  Λ := Bool
  main := false
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- The global-depth output is produced in exactly `d+1` TM2 steps. All
other stacks are framed, so layout tables and the retained archive survive. -/
theorem global_header_run (d : Nat) (rest : List Cell) (v : Sig)
    (S : ∀ k, List (OuterGam k))
    (hsrc : S source = (List.replicate d true ++ [false]).map bit ++ rest) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[d + 1] (some ⟨some false, v, S⟩) =
        some ⟨some true, some Cell.delim, U⟩
      ∧ U source = rest
      ∧ U counter = List.replicate d Cell.mark ++ S counter
      ∧ U output = Cell.delim :: List.replicate (3*d+113) Cell.mark ++ S output
      ∧ ∀ k, k ≠ source → k ≠ counter → k ≠ output → U k = S k := by
  induction d generalizing v S with
  | zero =>
      have hd : S source = Cell.delim :: rest := by
        simpa [bit] using hsrc
      let U := Function.update (Function.update S source rest) output
        (Cell.delim :: List.replicate 113 Cell.mark ++ S output)
      refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
      · simp [run, machine, step, stepAux, hd, pop, isSome, isMark,
          stepAux_pushMarks, cst, U, source, output]
      · simp [U, source, output]
      · simp [U, source, output, counter]
      · simp [U]
      · intro k hs hc ho
        simp [U, hs, ho]
  | succ d ih =>
      have hm : S source = Cell.mark :: ((List.replicate d true ++ [false]).map bit ++ rest) := by
        simpa [bit, List.replicate_succ, List.append_assoc] using hsrc
      let T := Function.update
        (Function.update
          (Function.update S source ((List.replicate d true ++ [false]).map bit ++ rest))
          counter (Cell.mark :: S counter))
        output (List.replicate 3 Cell.mark ++ S output)
      have hfirst : run (some ⟨some false, v, S⟩) =
          some ⟨some false, some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, isMark,
          stepAux_pushMarks, cst, T, source, counter, output]
      obtain ⟨U, hrun, hs, hc, ho, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, source, counter, output])
      refine ⟨U, ?_, hs, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hrun
      · rw [hc]
        simp [T, source, counter, output, List.replicate_add, List.append_assoc]
      · rw [ho]
        simp only [T, Function.update_self]
        have ha : 3 * (d + 1) + 113 = (3*d+113) + 3 := by omega
        simp only [ha, List.replicate_add, List.cons_append, List.append_assoc]
      · intro k hs hc ho
        rw [hf k hs hc ho]
        simp [T, hs, hc, ho]

/-- The stack expression in the run theorem is exactly the required unary
encoding, in the controller's reverse-output orientation. -/
theorem global_header_bytes (d : Nat) (acc : List Cell) :
    Cell.delim :: List.replicate (3*d+113) Cell.mark ++ acc =
      ((List.replicate (3*d+113) true ++ [false]).map bit).reverse ++ acc := by
  simp [bit, List.reverse_append]

end ShiTMGlobalDepthHeader
