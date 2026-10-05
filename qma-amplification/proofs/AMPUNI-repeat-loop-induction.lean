import «AMPUNI-repeat-loop-compose»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- A clean source entry: only its input stack contains the current code. -/
def sourceInput (input : K) (xs : List (G input)) :
    ∀ j : K, List (G j) :=
  Function.update (fun j : K => ([] : List (G j))) input xs

/-- The corresponding entry in the alternating-header loop controller. -/
def loopInput (entry : L) (input : K) (w : W)
    (xs : List (G input)) (b : Bool) (n q : Nat) :
    Cfg (Gam G) (Label L) (Option Bool × W) :=
  ⟨some (body b entry), (none, w),
    ShiTMStackFrame.extendStacks (sourceInput input xs) (bank b n q)⟩

/-- Exact budget used by the inductive controller run, measured from the
current body entry through the final cleanup. -/
def preloadedCost (n : Nat) (resultLen times : Nat → Nat)
    (r : Nat) : Nat → Nat
  | 0 => times r + n + 2
  | q + 1 => times r +
      (1 + 2 * (resultLen r + 1) + n + 2) +
        preloadedCost n resultLen times (r + 1) q

/-- With a preloaded unary round counter, a clean output handoff on every
source call entails a complete finite-controller run through all rounds.
The index `q` counts further calls after the current one. -/
theorem preloaded_loop_runs
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (hio : input ≠ output)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (hhalt : M terminal = .halt)
    (n : Nat) (w : W)
    (code : Nat → List (G input))
    (result : Nat → List (G output))
    (times : Nat → Nat)
    (finish : Nat → Cfg G L (Option Bool × W))
    (hcode : ∀ r, code (r + 1) =
      ((List.replicate n true ++ false :: (result r).map decodeOutput).map
        encodeInput))
    (hrun : ∀ r,
      (ShiTMSubroutine.run M)^[times r]
        (some ⟨some entry, (none, w), sourceInput input (code r)⟩) =
          some (finish r))
    (hlabel : ∀ r, (finish r).l = some terminal)
    (hstate : ∀ r, (finish r).var = (none, w))
    (houtput : ∀ r, (finish r).stk output = result r)
    (hclean : ∀ r j, j ≠ output → (finish r).stk j = []) :
    ∀ (r q : Nat) (b : Bool),
      ∃ t : Nat, ∃ S : ∀ j, List (Gam G j),
        (ShiTMSubroutine.run
          (machine M entry terminal input output decodeOutput encodeInput))^[t]
          (some (loopInput entry input w (code r) b n q)) =
            some ⟨none, (none, w), S⟩ ∧
        S (.inl output) = result (r + q) ∧
        (∀ j : K, j ≠ output → S (.inl j) = []) ∧
        (∀ h : Aux, S (.inr h) = []) ∧
        t ≤ preloadedCost n (fun i => (result i).length) times r q := by
  let P := machine M entry terminal input output decodeOutput encodeInput
  intro r q
  induction q generalizing r with
  | zero =>
      intro b
      have hh := body_then_final M entry terminal input output
        decodeOutput encodeInput hhalt b n (times r)
        (some ⟨some entry, (none, w), sourceInput input (code r)⟩)
        (finish r) (hlabel r) (hrun r)
      obtain ⟨S, hrun', hbase, haux⟩ := hh
      refine ⟨times r + (n + 2), S, ?_, ?_, ?_, haux, ?_⟩
      · simpa [loopInput, sourceInput, ShiTMSubroutine.cfg, ShiTMStackFrame.cfg,
          ShiTMStackFrame.extendStacks, hstate r] using hrun'
      · rw [hbase, houtput]
        rfl
      · intro j hj
        rw [hbase]
        exact hclean r j hj
      · simp only [preloadedCost]
        omega
  | succ q ih =>
      intro b
      have hh := body_then_next M entry terminal input output hio
        decodeOutput encodeInput hhalt b n q (times r) (result r)
        (some ⟨some entry, (none, w), sourceInput input (code r)⟩)
        (finish r) (hlabel r) (houtput r) (hclean r) (hrun r)
      obtain ⟨S₁, hrun', hcanon, hbank⟩ := hh
      have hs : S₁ = ShiTMStackFrame.extendStacks
          (sourceInput input (code (r + 1))) (bank (!b) n q) := by
        funext j
        cases j with
        | inl j =>
            rw [hcanon j, hcode r]
            rfl
        | inr j => exact hbank j
      have hstep :
          (ShiTMSubroutine.run P)^[times r +
              (1 + 2 * ((result r).length + 1) + n + 2)]
            (some (loopInput entry input w (code r) b n (q + 1))) =
              some (loopInput entry input w (code (r + 1)) (!b) n q) := by
        simpa [P, loopInput, sourceInput, ShiTMSubroutine.cfg,
          ShiTMStackFrame.cfg,
          ShiTMStackFrame.extendStacks, hstate r, hs] using hrun'
      obtain ⟨t₂, S₂, htail, hout, hother, haux, ht₂⟩ :=
        ih (r + 1) (!b)
      refine ⟨t₂ + (times r +
          (1 + 2 * ((result r).length + 1) + n + 2)), S₂, ?_, ?_,
        hother, haux, ?_⟩
      · rw [Function.iterate_add_apply, hstep]
        exact htail
      · have hidx : (r + 1) + q = r + (q + 1) := by omega
        simpa only [hidx] using hout
      · simp only [preloadedCost]
        omega

end ShiTMRepeatController
