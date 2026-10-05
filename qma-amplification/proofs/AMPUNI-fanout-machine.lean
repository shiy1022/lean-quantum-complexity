import «AMPUNI-outer-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMFanout

open ShiTMLayoutMachine ShiTMOuterLift

/-- Count, control index, target index occupy core stacks 0,1,2. The
layer counter and source/archive stacks are not used by this emitter. -/
abbrev port (k : Fin 3) : OuterK := .inl ⟨k.val, by omega⟩
abbrev scratch : OuterK := .inl (3 : Fin 14)
abbrev output : OuterK := .inl (13 : Fin 14)

theorem port_ne_scratch (k : Fin 3) : port k ≠ scratch := by
  intro h
  have hv := congrArg Fin.val (Sum.inl.inj h)
  have hk := k.isLt
  change k.val = 3 at hv
  omega

theorem port_ne_output (k : Fin 3) : port k ≠ output := by
  intro h
  have hv := congrArg Fin.val (Sum.inl.inj h)
  have hk := k.isLt
  change k.val = 13 at hv
  omega

theorem port_injective : Function.Injective port := by
  intro a b h
  have hv := congrArg (fun x : OuterK => match x with
    | .inl i => i.val
    | .inr _ => 0) h
  exact Fin.ext hv

inductive Label where
  | copy (k : Fin 3)
  | restore (k : Fin 3)
  | delimiter (k : Fin 3)
  | driver
  | finished
deriving DecidableEq

instance : Fintype Label := Fintype.ofList
  ([.copy 0, .copy 1, .copy 2, .restore 0, .restore 1, .restore 2,
    .delimiter 0, .delimiter 1, .delimiter 2, .driver, .finished])
  (by
    intro l
    cases l with
    | copy k => fin_cases k <;> simp
    | restore k => fin_cases k <;> simp
    | delimiter k => fin_cases k <;> simp
    | driver => simp
    | finished => simp)

def machine : Label → Stmt OuterGam Label Sig
  | .copy k =>
      .pop (port k) pop
        (.branch isSome
          (.push output (cst .mark)
            (.push scratch (cst .mark) (.goto (fun _ => .copy k))))
          (.goto (fun _ => .restore k)))
  | .restore k =>
      .pop scratch pop
        (.branch isSome
          (.push (port k) (cst .mark) (.goto (fun _ => .restore k)))
          (.goto (fun _ => .delimiter k)))
  | .delimiter k =>
      .push output (cst .delim)
        (if k = 0 then .goto (fun _ => .driver)
         else if k = 1 then .goto (fun _ => .copy 2)
         else .push (port 1) (cst .mark)
           (.push (port 2) (cst .mark) (.goto (fun _ => .driver))))
  | .driver =>
      .pop (port 0) pop
        (.branch isSome
          (.push output (cst .mark) (.push output (cst .mark)
            (.push output (cst .mark) (.push output (cst .mark)
              (.push output (cst .delim) (.goto (fun _ => .copy 1)))))))
          (.goto (fun _ => .finished)))
  | .finished => .halt

def run : Option (Cfg OuterGam Label Sig) → Option (Cfg OuterGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := OuterK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := port 0
  k₁ := output
  Γ := OuterGam
  Λ := Label
  main := .copy 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Copy a unary register to the output while saving its marks for restoration. -/
theorem copy_run (k : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (OuterGam j)) (hsrc : S (port k) = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (OuterGam j),
      run^[n+1] (some ⟨some (.copy k), v, S⟩) =
        some ⟨some (.restore k), none, U⟩
      ∧ U (port k) = []
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = List.replicate n Cell.mark ++ S scratch
      ∧ ∀ j, j ≠ port k → j ≠ output → j ≠ scratch → U j = S j := by
  have hks := port_ne_scratch k
  have hko := port_ne_output k
  have hso : scratch ≠ output := by decide
  induction n generalizing v S with
  | zero =>
      have he : S (port k) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, by simp, by simp, by intro j _ _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S (port k) = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update (Function.update S (port k) (List.replicate n Cell.mark))
          output (Cell.mark :: S output))
        scratch (Cell.mark :: S scratch)
      have hfirst : run (some ⟨some (.copy k), v, S⟩) =
          some ⟨some (.copy k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T,
          hks, hks.symm, hko, hko.symm, hso, hso.symm]
      obtain ⟨U, hr, hs, ho, ht, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks, hko])
      refine ⟨U, ?_, hs, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [ho]
        simp [T, hso.symm, List.replicate_add, List.append_assoc]
      · rw [ht]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjo hjs
        rw [hf j hjk hjo hjs]
        simp [T, hjk, hjo, hjs]

/-- Restore the register and clear the saved unary marks. -/
theorem restore_run (k : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (OuterGam j)) (hs : S scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ j, List (OuterGam j),
      run^[n+1] (some ⟨some (.restore k), v, S⟩) =
        some ⟨some (.delimiter k), none, U⟩
      ∧ U scratch = []
      ∧ U (port k) = List.replicate n Cell.mark ++ S (port k)
      ∧ ∀ j, j ≠ port k → j ≠ scratch → U j = S j := by
  have hks := port_ne_scratch k
  induction n generalizing v S with
  | zero =>
      have he : S scratch = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro j _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S scratch = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S scratch (List.replicate n Cell.mark))
        (port k) (Cell.mark :: S (port k))
      have hfirst : run (some ⟨some (.restore k), v, S⟩) =
          some ⟨some (.restore k), some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T, hks]
      obtain ⟨U, hr, ht, hk, hf⟩ :=
        ih (some Cell.mark) T (by simp [T, hks.symm])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]
        exact hr
      · rw [hk]
        simp [T, List.replicate_add, List.append_assoc]
      · intro j hjk hjs
        rw [hf j hjk hjs]
        simp [T, hjk, hjs]

/-- Emit a unary value without consuming its register. The delimiter is a
separate control step, allowing reuse for the layer header and both operands. -/
theorem field_run (k : Fin 3) (n : Nat) (v : Sig)
    (S : ∀ j, List (OuterGam j))
    (hsrc : S (port k) = List.replicate n Cell.mark) (hs : S scratch = []) :
    ∃ U : ∀ j, List (OuterGam j),
      run^[2*n+2] (some ⟨some (.copy k), v, S⟩) =
        some ⟨some (.delimiter k), none, U⟩
      ∧ U (port k) = List.replicate n Cell.mark
      ∧ U output = List.replicate n Cell.mark ++ S output
      ∧ U scratch = []
      ∧ ∀ j, j ≠ port k → j ≠ output → j ≠ scratch → U j = S j := by
  obtain ⟨T, ht, htk, hto, hts, htf⟩ := copy_run k n v S hsrc
  obtain ⟨U, hu, hus, huk, huf⟩ :=
    restore_run k n none T (by simpa [hs] using hts)
  refine ⟨U, ?_, ?_, ?_, hus, ?_⟩
  · have h := iterTwo run (n+1) (n+1) _ _ _ ht hu
    have hc : (n+1)+(n+1) = 2*n+2 := by omega
    simpa only [hc] using h
  · rw [huk, htk, List.append_nil]
  · rw [huf output (port_ne_output k).symm (by decide), hto]
  · intro j hjk hjo hjs
    rw [huf j hjk hjs, htf j hjk hjo hjs]

end ShiTMFanout
