import «AMPUNI-constructive-loader-startup»

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

/-- The scaled logarithm loader and the controller's prefix restoration
reach the first source-machine call with the exact constructive counter. -/
theorem loader_to_first_body
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat) (S : ∀ j, List (G j)) (w : W) :
    ∃ parity : Bool,
    ∃ S' : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[
            ShiTMUnaryLogCost.work (n + 1) + n + 3]
        (some (ShiTMSubroutine.cfg loader
          (ShiTMScaledLogControllerFrame.cfg
            S (List.replicate n true) w
            (ShiTMUnaryLog.cfg (.scan false) false none true
              (List.replicate (n + 1) true) [] [])))) =
      some ⟨some (controller
        (ShiTMRepeatController.body false entry)),
        (none, (parity, w)), S'⟩ ∧
      S' (.inl input) =
        (List.replicate n true).map encodeInput ++
          encodeInput false :: S input ∧
      S' (.inr (ShiTMRepeatController.header true)) = [] ∧
      S' (.inr (ShiTMRepeatController.header false)) =
        List.replicate n true ∧
      S' (.inr ShiTMRepeatController.scratch) = [] ∧
      S' (.inr ShiTMRepeatController.counter) =
        List.replicate
          (ShiQMAConstructiveSchedule.rounds p n - 1) true ∧
      (∀ j : K, j ≠ input → S' (.inl j) = S j) := by
  obtain ⟨direction, parity, hr⟩ :=
    actual_loader_to_done p M entry terminal input output
      decodeInput decodeOutput encodeInput n S w
  let F := ShiTMScaledLogControllerFrame.cfg
    S (List.replicate n true) w
    (ShiTMUnaryLog.cfg .done direction none parity [] []
      (List.replicate
        (p.natDegree * Nat.log 2 (n + 1)) true))
  have hF : F.l = some ShiTMUnaryLog.Label.done ∧
      F.var = (none, (parity, w)) := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMScaledLogControllerFrame.stateEquiv,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMScaledLogAux.cfg, ShiTMUnaryLog.cfg]
  have hFi : F.stk (.inl input) = S input := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks]
  have hFh1 : F.stk (.inr (ShiTMRepeatController.header true)) =
      List.replicate n true := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks, ShiTMScaledLogAux.cfg,
      ShiTMScaledLogAux.embedStacks,
      ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
  have hFh0 : F.stk (.inr (ShiTMRepeatController.header false)) =
      [] := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks, ShiTMScaledLogAux.cfg,
      ShiTMScaledLogAux.embedStacks, ShiTMUnaryLog.cfg,
      ShiTMUnaryLog.storeFn,
      ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
    cases direction <;> rfl
  have hFs : F.stk (.inr ShiTMRepeatController.scratch) = [] := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks, ShiTMScaledLogAux.cfg,
      ShiTMScaledLogAux.embedStacks, ShiTMUnaryLog.cfg,
      ShiTMUnaryLog.storeFn,
      ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
    cases direction <;> rfl
  have hFc : F.stk (.inr ShiTMRepeatController.counter) =
      List.replicate
        (p.natDegree * Nat.log 2 (n + 1)) true := by
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks, ShiTMScaledLogAux.cfg,
      ShiTMScaledLogAux.embedStacks, ShiTMUnaryLog.cfg,
      ShiTMUnaryLog.storeFn,
      ShiTMRepeatController.header,
      ShiTMRepeatController.scratch,
      ShiTMRepeatController.counter]
    cases direction <;> rfl
  obtain ⟨S', hf, hi', hh1', hh0', hs', hc', ho'⟩ :=
    finish_to_first_body p M entry terminal input output
      decodeInput decodeOutput encodeInput n (S input) F.stk
      parity w hFi hFh1 hFh0 hFs hFc
  refine ⟨parity, S', ?_, hi', hh1', hh0', hs', hc', ?_⟩
  · have hdone :
        (some (ShiTMSubroutine.cfg loader F) :
          Option (Cfg (ShiTMRepeatController.Gam G)
            (Label L) (Option Bool × (Bool × W)))) =
        some ⟨some (loader .done), (none, (parity, w)), F.stk⟩ := by
      rcases hF with ⟨hl, hv⟩
      simp [ShiTMSubroutine.cfg, hl, hv]
    have hrun := iterTwo
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))
      _ _ _ _ _ (hr.trans hdone) hf
    exact hrun
  · intro j hj
    rw [ho' j hj]
    simp [F, ShiTMScaledLogControllerFrame.cfg,
      ShiTMStateReindex.cfg, ShiTMRightFrame.cfg,
      ShiTMStackFrame.extendStacks]

end ShiTMConstructiveIntegrated
