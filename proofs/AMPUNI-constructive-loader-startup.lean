import «AMPUNI-constructive-loader-frame-entry»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private theorem iterTwo {A : Type} (f : A → A)
    (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega,
    Function.iterate_add_apply, hxy, hyz]

/-- The integrated scanner, header copier, and seed instruction put the
machine at the checked logarithm-loader entry after `2*n+3` steps. -/
theorem startup_to_framed_loader
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
    (v : Option Bool) (w : W)
    (hi : S (.inl input) =
      List.replicate n (encodeInput true) ++
        encodeInput false :: code)
    (h0 : S (.inr (ShiTMRepeatController.header false)) = [])
    (h1 : S (.inr (ShiTMRepeatController.header true)) = [])
    (hs : S (.inr ShiTMRepeatController.scratch) = [])
    (hc : S (.inr ShiTMRepeatController.counter) = []) :
    ∃ B : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[2 * n + 3]
        (some ⟨some scan, (v, (true, w)), S⟩) =
      some (ShiTMSubroutine.cfg loader
        (ShiTMScaledLogControllerFrame.cfg
          (fun j => B (.inl j)) (List.replicate n true) w
          (ShiTMUnaryLog.cfg (.scan false) false none true
            (List.replicate (n + 1) true) [] []))) ∧
      B (.inl input) = code ∧
      (∀ j : K, j ≠ input → B (.inl j) = S (.inl j)) := by
  let f := ShiTMSubroutine.run
    (machine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
  let A := Function.update (Function.update S (.inl input) code)
    (.inr (ShiTMRepeatController.header false))
    (List.replicate n true ++
      S (.inr (ShiTMRepeatController.header false)))
  have hscan : f^[n + 1]
      (some ⟨some scan, (v, (true, w)), S⟩) =
      some ⟨some duplicate, (some false, (true, w)), A⟩ := by
    exact actual_scan_run p M entry terminal input output
      decodeInput decodeOutput encodeInput htrue hfalse
      n code S v true w hi
  have hA0 : A (.inr (ShiTMRepeatController.header false)) =
      List.replicate n true := by simp [A, h0]
  have hA1 : A (.inr (ShiTMRepeatController.header true)) = [] := by
    simpa [A, ShiTMRepeatController.header] using h1
  have hAs : A (.inr ShiTMRepeatController.scratch) = [] := by
    simpa [A, ShiTMRepeatController.header,
      ShiTMRepeatController.scratch] using hs
  obtain ⟨B, hdup, hB0, hBs, hB1, hBc, hBi⟩ :=
    actual_duplicate_header p M entry terminal input output
      decodeInput decodeOutput encodeInput n A (some false) true w
      hA0 hAs hA1
  have hAc : A (.inr ShiTMRepeatController.counter) = [] := by
    simpa [A, ShiTMRepeatController.header,
      ShiTMRepeatController.counter] using hc
  have hseed := seed_to_framed_loader p M entry terminal
    input output decodeInput decodeOutput encodeInput n B
    hBs hB0 hB1 (hBc.trans hAc) w
  have hseed1 : f^[1]
      (some ⟨some seed, (none, (true, w)), B⟩) =
      some (ShiTMSubroutine.cfg loader
        (ShiTMScaledLogControllerFrame.cfg
          (fun j => B (.inl j)) (List.replicate n true) w
          (ShiTMUnaryLog.cfg (.scan false) false none true
            (List.replicate (n + 1) true) [] []))) := by
    simpa [f] using hseed
  have hrun := iterTwo f _ _ _ _ _
    (iterTwo f _ _ _ _ _ hscan hdup) hseed1
  refine ⟨B, ?_, ?_, ?_⟩
  · simpa [show (n + 1) + (n + 1) + 1 = 2 * n + 3 by omega]
      using hrun
  · rw [hBi]
    simp [A]
  · intro j hj
    rw [hBi]
    simp [A, hj]

end ShiTMConstructiveIntegrated
