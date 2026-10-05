import «AMPUNI-scaled-log-controller-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMScaledLogControllerFrame

variable {K W : Type} [DecidableEq K] {G : K → Type}

/-- A loader on the controller's auxiliary stacks preserves all source
stacks and the original unary length header. It reaches its active finish
label with the logarithmic part of the counter on the controller counter
stack; a final fixed-offset step can then enter the first verifier call. -/
theorem loader_to_done (p : Polynomial ℕ) (n : Nat)
    (S : ∀ j, List (G j)) (w : W) :
    ∃ direction parity : Bool,
      (ShiTMSubroutine.run
        (machine (G := G) (W := W)
          p.natDegree (ShiTMScaledLog.scheduleOffset p)))^[
          ShiTMUnaryLogCost.work (n + 1)]
        (some (cfg S (List.replicate n true) w
          (ShiTMUnaryLog.cfg (.scan false) false none true
            (List.replicate (n + 1) true) [] []))) =
      some (cfg S (List.replicate n true) w
        (ShiTMUnaryLog.cfg .done direction none parity [] []
          (List.replicate
            (p.natDegree * Nat.log 2 (n + 1)) true))) := by
  obtain ⟨direction, parity, hr⟩ :=
    ShiTMScaledLog.full_run p.natDegree
      (ShiTMScaledLog.scheduleOffset p) (n + 1)
      false none []
  refine ⟨direction, parity, ?_⟩
  have hf := run_iter_frame (G := G) (W := W)
    p.natDegree (ShiTMScaledLog.scheduleOffset p)
    S (List.replicate n true) w
    (ShiTMUnaryLogCost.work (n + 1))
    (some (ShiTMUnaryLog.cfg (.scan false) false none true
      (List.replicate (n + 1) true) [] []))
  simpa only [Option.map_some, List.append_nil, hr] using hf

end ShiTMScaledLogControllerFrame
