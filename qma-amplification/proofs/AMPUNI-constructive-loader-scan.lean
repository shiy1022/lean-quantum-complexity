import «AMPUNI-constructive-loader-duplicate»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- The startup scan consumes precisely the leading unary `true^n false`
field, leaving the verifier code and saving `n` true bits on header bank 0. -/
theorem actual_scan_run
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (htrue : decodeInput (encodeInput true) = true)
    (hfalse : decodeInput (encodeInput false) = false)
    (n : Nat) (code : List (G input))
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (v : Option Bool) (parity : Bool) (w : W)
    (hs : S (.inl input) =
      List.replicate n (encodeInput true) ++ encodeInput false :: code) :
    (ShiTMSubroutine.run
      (machine p M entry terminal input output decodeInput decodeOutput encodeInput))^[n + 1]
      (some ⟨some scan, (v, (parity, w)), S⟩) =
        some ⟨some duplicate,
          (some false, (parity, w)),
          Function.update (Function.update S (.inl input) code)
            (.inr (ShiTMRepeatController.header false))
            (List.replicate n true ++
              S (.inr (ShiTMRepeatController.header false)))⟩ := by
  induction n generalizing S v with
  | zero =>
      have hstack :
          Function.update S (.inl input) code =
            Function.update (Function.update S (.inl input) code)
              (.inr (ShiTMRepeatController.header false))
              (S (.inr (ShiTMRepeatController.header false))) := by
        funext j
        cases j with
        | inl j =>
            by_cases hj : j = input
            · subst j; simp
            · simp [hj]
        | inr j =>
            by_cases hj : j = ShiTMRepeatController.header false
            · subst j; simp
            · simp [hj]
      simpa [ShiTMSubroutine.run, machine, scan, duplicate,
        step, stepAux, hs, hfalse] using
        congrArg
          (fun T : ∀ j, List (ShiTMRepeatController.Gam G j) =>
            some (⟨some duplicate,
              (some false, (parity, w)), T⟩ :
                Cfg (ShiTMRepeatController.Gam G) (Label L)
                  (Option Bool × (Bool × W))))
          hstack
  | succ n ih =>
      let S₁ := Function.update
        (Function.update S (.inl input)
          (List.replicate n (encodeInput true) ++
            encodeInput false :: code))
        (.inr (ShiTMRepeatController.header false))
          (true :: S (.inr (ShiTMRepeatController.header false)))
      have hs₁ : S₁ (.inl input) =
          List.replicate n (encodeInput true) ++ encodeInput false :: code := by
        simp [S₁]
      have hstep : ShiTMSubroutine.run
          (machine p M entry terminal input output decodeInput decodeOutput encodeInput)
            (some ⟨some scan, (v, (parity, w)), S⟩) =
          some ⟨some scan, (some true, (parity, w)), S₁⟩ := by
        simp [ShiTMSubroutine.run, machine, scan, duplicate,
          step, stepAux, hs, htrue, S₁, List.replicate_succ]
      have h := ih S₁ (some true) hs₁
      rw [Nat.succ_add, Function.iterate_succ_apply, hstep, h]
      congr 1
      congr 1
      funext j
      by_cases hji : j = Sum.inl input
      · subst j
        simp [S₁]
      · by_cases hjh : j = Sum.inr (ShiTMRepeatController.header false)
        · subst j
          simp [S₁, List.replicate_succ, List.append_assoc]
          calc
            List.replicate n true ++ true ::
                S (.inr (ShiTMRepeatController.header false)) =
                (List.replicate n true ++ [true]) ++
                  S (.inr (ShiTMRepeatController.header false)) := by
              simp [List.append_assoc]
            _ = true :: (List.replicate n true ++
                  S (.inr (ShiTMRepeatController.header false))) := by
              rw [← List.replicate_succ', List.replicate_succ]
              simp [List.append_assoc]
        · simp [S₁, hji, hjh]

end ShiTMConstructiveIntegrated
