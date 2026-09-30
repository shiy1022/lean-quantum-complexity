import «AMPUNI-stack-frame»
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatBodyEmbed

variable {K H L R V : Type} [DecidableEq K] [DecidableEq H] [DecidableEq L]
    {G : K → Type} {E : H → Type}

/-- Run a source program on its own stacks until an active terminal label,
then let a surrounding controller take over at the terminal. -/
def machine (M : L → Stmt G L V) (terminal : L) (handoff : R)
    (other : R → Stmt (ShiTMStackFrame.Gam G E) (L ⊕ R) V) :
    L ⊕ R → Stmt (ShiTMStackFrame.Gam G E) (L ⊕ R) V
  | .inl l =>
      if l = terminal then .goto (fun _ => .inr handoff)
      else ShiTMSubroutine.stmt Sum.inl (ShiTMStackFrame.stmt (M l))
  | .inr r => other r

theorem run_body (M : L → Stmt G L V) (terminal : L) (handoff : R)
    (other : R → Stmt (ShiTMStackFrame.Gam G E) (L ⊕ R) V)
    (hhalt : M terminal = .halt)
    (A : ∀ h, List (E h))
    (n : Nat) (c : Option (Cfg G L V)) (d : Cfg G L V)
    (hd : d.l = some terminal)
    (hr : (ShiTMSubroutine.run M)^[n] c = some d) :
    (ShiTMSubroutine.run (machine M terminal handoff other))^[n]
      ((c.map (ShiTMStackFrame.cfg A)).map (ShiTMSubroutine.cfg Sum.inl)) =
      some (ShiTMSubroutine.cfg Sum.inl (ShiTMStackFrame.cfg A d)) := by
  have hf := ShiTMStackFrame.run_iter_frame (E := E) M A n c
  change (ShiTMSubroutine.run (ShiTMStackFrame.machine M))^[n]
    (c.map (ShiTMStackFrame.cfg A)) =
      ((ShiTMSubroutine.run M)^[n] c).map (ShiTMStackFrame.cfg A) at hf
  rw [hr] at hf
  exact ShiTMSubroutine.run_to_terminal
    (ShiTMStackFrame.machine (E := E) M)
    (machine M terminal handoff other) Sum.inl terminal
    (by simp [ShiTMStackFrame.machine, ShiTMStackFrame.stmt, hhalt])
    (by
      intro l hl
      simp [machine, hl, ShiTMStackFrame.machine])
    n _ _ (by simpa [ShiTMStackFrame.cfg] using hd) hf

end ShiTMRepeatBodyEmbed
