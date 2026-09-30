import «AMPUNI-repeat-loop-step»
import «AMPUNI-repeat-loop-final»
import «AMPUNI-repeat-controller-body»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- A source run ending in a clean output handoff, followed by the controller's
nonfinal transition, gives the canonical input configuration for the next
source run. The source run and handoff share an exact auxiliary-bank invariant. -/
theorem body_then_next
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (hio : input ≠ output)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (hhalt : M terminal = .halt)
    (b : Bool) (n q t : Nat) (ys : List (G output))
    (c : Option (Cfg G L (Option Bool × W)))
    (d : Cfg G L (Option Bool × W))
    (hd : d.l = some terminal)
    (ho : d.stk output = ys)
    (hbase : ∀ j : K, j ≠ output → d.stk j = [])
    (hr : (ShiTMSubroutine.run M)^[t] c = some d) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[
          t + (1 + 2 * (ys.length + 1) + n + 2)]
        ((c.map (ShiTMStackFrame.cfg (bank b n (q + 1)))).map
          (ShiTMSubroutine.cfg (body b))) =
          some ⟨some (body (!b) entry), (none, d.var.2), S'⟩ ∧
      (∀ j : K,
        S' (.inl j) =
          Function.update (fun _ : K => []) input
            ((List.replicate n true ++ false :: ys.map decodeOutput).map
              encodeInput) j) ∧
      (∀ h : Aux, S' (.inr h) = bank (!b) n q h) := by
  let A := bank b n (q + 1)
  let S := (ShiTMStackFrame.cfg A d).stk
  have hb := run_body M entry terminal input output decodeOutput
    encodeInput hhalt b A t c d hd hr
  have hbo :
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[t]
        ((c.map (ShiTMStackFrame.cfg A)).map
          (ShiTMSubroutine.cfg (body b))) =
        some ⟨some (body b terminal), d.var, S⟩ := by
    simpa only [S, ShiTMSubroutine.cfg, ShiTMStackFrame.cfg, hd,
      Option.map_some] using hb
  have ho' : S (.inl output) = ys := by
    simpa [S, ShiTMStackFrame.cfg, ShiTMStackFrame.extendStacks] using ho
  have hbase' : ∀ j : K, j ≠ output → S (.inl j) = [] := by
    intro j hj
    simpa [S, ShiTMStackFrame.cfg, ShiTMStackFrame.extendStacks] using
      hbase j hj
  have haux : ∀ h : Aux, S (.inr h) = bank b n (q + 1) h := by
    intro h
    rfl
  obtain ⟨S', hn, hcanon, hbank⟩ := terminal_to_next M entry
    terminal input output hio decodeOutput encodeInput b n q ys S
      d.var.1 d.var.2 ho' hbase' haux
  refine ⟨S', ?_, hcanon, hbank⟩
  rw [show t + (1 + 2 * (ys.length + 1) + n + 2) =
      (1 + 2 * (ys.length + 1) + n + 2) + t by omega,
    Function.iterate_add_apply, hbo]
  exact hn

/-- The same source handoff with no counter tokens reaches a clean halt. -/
theorem body_then_final
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (hhalt : M terminal = .halt)
    (b : Bool) (n t : Nat)
    (c : Option (Cfg G L (Option Bool × W)))
    (d : Cfg G L (Option Bool × W))
    (hd : d.l = some terminal)
    (hr : (ShiTMSubroutine.run M)^[t] c = some d) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[
          t + (n + 2)]
        ((c.map (ShiTMStackFrame.cfg (bank b n 0))).map
          (ShiTMSubroutine.cfg (body b))) =
          some ⟨none, (none, d.var.2), S'⟩ ∧
      (∀ j : K, S' (.inl j) = d.stk j) ∧
      (∀ h : Aux, S' (.inr h) = []) := by
  let A := bank b n 0
  let S := (ShiTMStackFrame.cfg A d).stk
  have hb := run_body M entry terminal input output decodeOutput
    encodeInput hhalt b A t c d hd hr
  have hbo :
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[t]
        ((c.map (ShiTMStackFrame.cfg A)).map
          (ShiTMSubroutine.cfg (body b))) =
        some ⟨some (body b terminal), d.var, S⟩ := by
    simpa only [S, ShiTMSubroutine.cfg, ShiTMStackFrame.cfg, hd,
      Option.map_some] using hb
  have haux : ∀ h : Aux, S (.inr h) = bank b n 0 h := by
    intro h
    rfl
  obtain ⟨S', hf, hbase, hclear⟩ := terminal_to_clean_halt M entry
    terminal input output decodeOutput encodeInput b n S d.var.1
      d.var.2 haux
  refine ⟨S', ?_, ?_, hclear⟩
  · rw [show t + (n + 2) = (n + 2) + t by omega,
      Function.iterate_add_apply, hbo]
    exact hf
  · intro j
    rw [hbase]
    rfl

end ShiTMRepeatController
