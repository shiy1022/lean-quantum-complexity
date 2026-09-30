import «AMPUNI-nested-circuit-layers»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPayload

open ShiTMLayoutMachine ShiTMOuterLift

/-- A new entry label strips only the circuit header. The existing nested
parser still emits every layer header and every translated instruction. -/
abbrev PayloadLabel := Option OuterLabel

def liftCfg (c : Cfg OuterGam OuterLabel Sig) : Cfg OuterGam PayloadLabel Sig :=
  ⟨c.l.map some, c.var, c.stk⟩

def liftStmt : Stmt OuterGam OuterLabel Sig → Stmt OuterGam PayloadLabel Sig
  | .push k f q => .push k f (liftStmt q)
  | .peek k f q => .peek k f (liftStmt q)
  | .pop k f q => .pop k f (liftStmt q)
  | .load f q => .load f (liftStmt q)
  | .branch f a b => .branch f (liftStmt a) (liftStmt b)
  | .goto f => .goto (fun v => some (f v))
  | .halt => .halt

def machine : PayloadLabel → Stmt OuterGam PayloadLabel Sig
  | some l => liftStmt (nestedMachine l)
  | none =>
      .pop (.inl (11 : Fin 14)) pop
        (.branch isSome
          (.branch isMark
            (.push (.inr (0 : Fin 2)) (cst .mark)
              (.goto (fun _ => none)))
            (.goto (fun _ => some (.inr .layerDriver))))
          .halt)

def run : Option (Cfg OuterGam PayloadLabel Sig) →
    Option (Cfg OuterGam PayloadLabel Sig) :=
  fun c => c.bind (step machine)

theorem stepAux_lift (q : Stmt OuterGam OuterLabel Sig) (v : Sig)
    (S : ∀ k, List (OuterGam k)) :
    stepAux (liftStmt q) v S = liftCfg (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih => exact ih (f v (S k).head?) S
  | pop k f q ih => exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f a b iha ihb =>
      simp only [liftStmt, stepAux]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => rfl
  | halt => rfl

theorem run_lift (c : Option (Cfg OuterGam OuterLabel Sig)) :
    run (c.map liftCfg) = (nestedRun c).map liftCfg := by
  cases c with
  | none => rfl
  | some c =>
      cases c with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l =>
              change some (stepAux (liftStmt (nestedMachine l)) v S) =
                some (liftCfg (stepAux (nestedMachine l) v S))
              rw [stepAux_lift]

theorem run_iter_lift (n : Nat) (c : Option (Cfg OuterGam OuterLabel Sig)) :
    run^[n] (c.map liftCfg) = (nestedRun^[n] c).map liftCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_lift]
      exact ih (nestedRun c)

/-- Consume the local depth header in exactly `n+1` steps, load the layer
counter, and leave the entire output stack unchanged. -/
theorem strip_header_run (n : Nat) (rest : List Cell) (v : Sig)
    (S : ∀ k, List (OuterGam k))
    (hsrc : S (.inl (11 : Fin 14)) = (ShiBQP.encNat n).map bit ++ rest) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[n + 1] (some ⟨some none, v, S⟩) =
        some ⟨some (some (.inr .layerDriver)), some Cell.delim, U⟩
      ∧ U (.inl (11 : Fin 14)) = rest
      ∧ U (.inr (0 : Fin 2)) = List.replicate n Cell.mark ++ S (.inr 0)
      ∧ ∀ k, k ≠ .inl (11 : Fin 14) → k ≠ .inr (0 : Fin 2) → U k = S k := by
  induction n generalizing v S with
  | zero =>
      have hd : S (.inl (11 : Fin 14)) = Cell.delim :: rest := by
        simpa [ShiBQP.encNat, bit] using hsrc
      let U := Function.update S (.inl (11 : Fin 14)) rest
      refine ⟨U, ?_, ?_, ?_, ?_⟩
      · simp [run, machine, step, stepAux, hd, pop, isSome, isMark, U]
      · simp [U]
      · simp [U]
      · intro k hs hc
        simp [U, hs]
  | succ n ih =>
      have hm : S (.inl (11 : Fin 14)) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        simpa [ShiBQP.encNat, bit, List.replicate_succ, List.append_assoc] using hsrc
      let T := Function.update
        (Function.update S (.inl (11 : Fin 14)) ((ShiBQP.encNat n).map bit ++ rest))
        (.inr (0 : Fin 2)) (Cell.mark :: S (.inr 0))
      have hfirst : run (some ⟨some none, v, S⟩) =
          some ⟨some none, some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, isMark, cst, T]
      obtain ⟨U, hrun, hs, hc, hf⟩ := ih (some Cell.mark) T (by simp [T])
      refine ⟨U, ?_, hs, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hrun
      · rw [hc]
        simp [T, List.replicate_add, List.append_assoc]
      · intro k hs hc
        rw [hf k hs hc]
        simp [T, hs, hc]

/-- Exhausting the header source halts immediately; no unbounded empty-stack loop. -/
theorem strip_header_empty (v : Sig) (S : ∀ k, List (OuterGam k))
    (hsrc : S (.inl (11 : Fin 14)) = []) :
    run (some ⟨some none, v, S⟩) = some ⟨none, none, S⟩ := by
  simp [run, machine, step, stepAux, hsrc, pop, isSome]

end ShiTMPayload
