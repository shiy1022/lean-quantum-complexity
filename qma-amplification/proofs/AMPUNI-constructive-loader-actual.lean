import «AMPUNI-constructive-loader-reference»
import «AMPUNI-terminal-exception»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private abbrev Cfg' :=
  Cfg (ShiTMRepeatController.Gam G) (Label L)
    (Option Bool × (Bool × W))

private def atLoaderDone (c : Option (Cfg' (G := G) (L := L) (W := W))) : Prop :=
  ∃ v S, c = some ⟨some (loader .done), v, S⟩

private def closed (c : Option (Cfg' (G := G) (L := L) (W := W))) : Prop :=
  c = none ∨ ∃ v S, c = some ⟨none, v, S⟩

private theorem closed_disjoint
    (c : Option (Cfg' (G := G) (L := L) (W := W)))
    (hc : closed c) : ¬ atLoaderDone c := by
  intro ht
  rcases ht with ⟨v, S, hv⟩
  rcases hc with h | ⟨v', S', h⟩
  · simp [h] at hv
  · simp [h] at hv

private theorem reference_done_halts
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (c : Option (Cfg' (G := G) (L := L) (W := W)))
    (hc : atLoaderDone c) :
    closed (ShiTMSubroutine.run
      (referenceMachine p M entry terminal input output
        decodeInput decodeOutput encodeInput) c) := by
  obtain ⟨v, S, rfl⟩ := hc
  exact Or.inr ⟨v, S, by
    simp [ShiTMSubroutine.run, referenceMachine, loader,
      ShiTMScaledLogControllerFrame.liftMachine,
      ShiTMScaledLogBody.machine,
      ShiTMScaledLogAux.liftMachine,
      ShiTMStateReindex.machine,
      ShiTMRightFrame.machine,
      ShiTMStateReindex.stmt,
      ShiTMRightFrame.stmt,
      ShiTMScaledLogAux.stmt,
      ShiTMSubroutine.stmt, step]⟩

private theorem closed_stays
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (c : Option (Cfg' (G := G) (L := L) (W := W)))
    (hc : closed c) :
    closed (ShiTMSubroutine.run
      (referenceMachine p M entry terminal input output
        decodeInput decodeOutput encodeInput) c) := by
  rcases hc with rfl | ⟨v, S, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

private theorem actual_agrees_before_done
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (c : Option (Cfg' (G := G) (L := L) (W := W)))
    (hc : ¬ atLoaderDone c) :
    ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput) c =
    ShiTMSubroutine.run
      (referenceMachine p M entry terminal input output
        decodeInput decodeOutput encodeInput) c := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          cases l with
          | inr i => rfl
          | inl l =>
              cases l with
              | inl cl => rfl
              | inr ll =>
                  cases ll with
                  | scan b => rfl
                  | check b => rfl
                  | done =>
                      exact False.elim (hc ⟨v, S, rfl⟩)

/-- The actual integrated machine has the same checked loader prefix as
the reference program. Its different finish instruction is not executed
until after the active finish configuration is reached. -/
theorem actual_loader_to_done
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat) (S : ∀ j, List (G j)) (w : W) :
    ∃ direction parity : Bool,
      (ShiTMSubroutine.run
        (machine p M entry terminal input output
          decodeInput decodeOutput encodeInput))^[
          ShiTMUnaryLogCost.work (n + 1)]
        (some (ShiTMSubroutine.cfg loader
          (ShiTMScaledLogControllerFrame.cfg
            S (List.replicate n true) w
            (ShiTMUnaryLog.cfg (.scan false) false none true
              (List.replicate (n + 1) true) [] [])))) =
      some (ShiTMSubroutine.cfg loader
        (ShiTMScaledLogControllerFrame.cfg
          S (List.replicate n true) w
          (ShiTMUnaryLog.cfg .done direction none parity [] []
            (List.replicate
              (p.natDegree * Nat.log 2 (n + 1)) true)))) := by
  obtain ⟨direction, parity, href⟩ :=
    reference_loader_to_done p M entry terminal input output
      decodeInput decodeOutput encodeInput n S w
  refine ⟨direction, parity, ?_⟩
  let f := ShiTMSubroutine.run
    (machine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
  let g := ShiTMSubroutine.run
    (referenceMachine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
  have hn : ∀ c, atLoaderDone c → ∀ k, 0 < k →
      ¬ atLoaderDone (g^[k] c) :=
    ShiTMTerminalException.no_return_of_closed
      g atLoaderDone closed
      (reference_done_halts p M entry terminal input output
        decodeInput decodeOutput encodeInput)
      (closed_stays p M entry terminal input output
        decodeInput decodeOutput encodeInput)
      closed_disjoint
  have ht : atLoaderDone
      (g^[ShiTMUnaryLogCost.work (n + 1)]
        (some (ShiTMSubroutine.cfg loader
          (ShiTMScaledLogControllerFrame.cfg
            S (List.replicate n true) w
            (ShiTMUnaryLog.cfg (.scan false) false none true
              (List.replicate (n + 1) true) [] []))))) := by
    rw [href]
    exact ⟨_, _, rfl⟩
  exact (ShiTMTerminalException.iterate_agree_until_terminal
    f g atLoaderDone
    (actual_agrees_before_done p M entry terminal input output
      decodeInput decodeOutput encodeInput)
    hn _ _ ht).trans href

end ShiTMConstructiveIntegrated
