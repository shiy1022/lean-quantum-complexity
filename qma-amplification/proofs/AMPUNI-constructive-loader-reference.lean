import «AMPUNI-constructive-integrated-machine»
import «AMPUNI-scaled-log-controller-frame-any»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- A proof-only program with the loader finish label treated as a halt.
All non-loader phases are identical to the integrated machine. -/
def referenceMachine (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input) :
    Label L → Stmt (ShiTMRepeatController.Gam G) (Label L)
      (Option Bool × (Bool × W))
  | .inl (.inr l) =>
      ShiTMSubroutine.stmt loader
        (ShiTMScaledLogControllerFrame.liftMachine
          (G := G) (W := W)
          (ShiTMScaledLogBody.machine p.natDegree
            (ShiTMScaledLog.scheduleOffset p)) l)
  | l => machine p M entry terminal input output
      decodeInput decodeOutput encodeInput l

/-- The reference integrated machine executes the checked scaled loader
until its active finish label, preserving arbitrary source stacks and the
saved length header. -/
theorem reference_loader_to_done
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (n : Nat) (S : ∀ j, List (G j)) (w : W) :
    ∃ direction parity : Bool,
      (ShiTMSubroutine.run
        (referenceMachine p M entry terminal input output
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
  let small := ShiTMScaledLogBody.machine p.natDegree
    (ShiTMScaledLog.scheduleOffset p)
  let framed := ShiTMScaledLogControllerFrame.liftMachine
    (G := G) (W := W) small
  obtain ⟨direction, parity, hsmall⟩ :=
    ShiTMScaledLogBody.full_run p.natDegree
      (ShiTMScaledLog.scheduleOffset p) (n + 1)
      false none []
  refine ⟨direction, parity, ?_⟩
  have hframe :=
    ShiTMScaledLogControllerFrame.run_iter_frame_any
      (G := G) (W := W) small S
      (List.replicate n true) w
      (ShiTMUnaryLogCost.work (n + 1))
      (some (ShiTMUnaryLog.cfg (.scan false) false none true
        (List.replicate (n + 1) true) [] []))
  have hlift := ShiTMSubroutine.run_iter_lift
    framed
    (referenceMachine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
    loader (by intro l; rfl)
    (ShiTMUnaryLogCost.work (n + 1))
    (some (ShiTMScaledLogControllerFrame.cfg
      S (List.replicate n true) w
      (ShiTMUnaryLog.cfg (.scan false) false none true
        (List.replicate (n + 1) true) [] [])))
  simp only [Option.map_some] at hframe
  change (ShiTMSubroutine.run small)^[ShiTMUnaryLogCost.work (n + 1)]
      (some (ShiTMUnaryLog.cfg (.scan false) false none true
        (List.replicate (n + 1) true) [] [])) = _ at hsmall
  rw [hframe, hsmall] at hlift
  simpa only [Option.map_some, List.append_nil] using hlift

end ShiTMConstructiveIntegrated
