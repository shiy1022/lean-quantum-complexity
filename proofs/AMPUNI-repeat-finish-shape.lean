import «AMPUNI-repeat-fueled-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatFueled

variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)
    (k : Nat)

theorem activeFinish_output (ys : List (tm.Γ tm.k₁)) :
    (activeFinish tm inputEquiv k ys).stk
      ((finiteMachine tm inputEquiv k).k₁) = ys := by
  simp [activeFinish, finiteMachine, ShiTMSubroutine.cfg,
    ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks,
    ShiTMRepeatClocked.activeFinish]

theorem activeFinish_other_empty (ys : List (tm.Γ tm.k₁))
    (j : (finiteMachine tm inputEquiv k).K)
    (hj : j ≠ (finiteMachine tm inputEquiv k).k₁) :
    (activeFinish tm inputEquiv k ys).stk j = [] := by
  cases j with
  | inl a =>
      simp [activeFinish, finiteMachine, ShiTMSubroutine.cfg,
        ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks]
  | inr a =>
      cases a with
      | inl a =>
          have ha : a ≠ tm.k₁ := by
            intro he
            subst a
            exact hj rfl
          simp [activeFinish, finiteMachine, ShiTMSubroutine.cfg,
            ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks,
            ShiTMRepeatClocked.activeFinish, ha]
      | inr a =>
          simp [activeFinish, finiteMachine, ShiTMSubroutine.cfg,
            ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks,
            ShiTMRepeatClocked.activeFinish]

theorem activeFinish_state (ys : List (tm.Γ tm.k₁)) :
    (activeFinish tm inputEquiv k ys).var =
      (finiteMachine tm inputEquiv k).initialState := by
  rfl

end ShiTMRepeatFueled
