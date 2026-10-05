import Space.PeakComposition

/-! # Fresh-import audit for the run algebra, frames and peak segments (S02) -/

open Turing Turing.TM2

-- The all-prefix principle in the form downstream tasks use.
example (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁))
    (h : TM2Outputs tm xs (some ys)) (s : ℕ)
    (hb : ∀ t ≤ h.steps, ∀ e,
      (ShiTMSubroutine.run tm.m)^[t] (some (initList tm xs)) = some e →
        ShiSpace.cfgSpace tm e ≤ s) :
    ShiSpace.SpaceBoundedOn tm xs s := ShiSpace.spaceBoundedOn_of_outputs h s hb

-- Iterated segments keep a common bound (scratch reuse; no factor of the iteration count).
example {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}
    (M : L → Stmt G L V) (c : ℕ → Cfg G L V) (n : ℕ → ℕ) (B N : ℕ)
    (h : ∀ i < N, ShiSpace.Seg M (c i) (n i) (c (i + 1)) B)
    (h0 : ShiTMStackGrowth.size (c 0).stk ≤ B) :
    ShiSpace.Seg M (c 0) (∑ i ∈ Finset.range N, n i) (c N) B :=
  ShiSpace.Seg.iter c n B N h h0

#print axioms ShiSpace.iterate_after_halt
#print axioms ShiSpace.iterate_prefix
#print axioms ShiSpace.halted_time_unique
#print axioms ShiSpace.halted_unique
#print axioms ShiSpace.forall_reachable_of_halts
#print axioms ShiSpace.spaceBoundedOn_of_outputs
#print axioms ShiSpace.le_steps_of_outputs
#print axioms ShiSpace.stepAux_stk_of_not_writes
#print axioms ShiSpace.iterate_stk_of_not_writes
#print axioms ShiSpace.size_iterate_of_frame
#print axioms ShiSpace.Seg.trans
#print axioms ShiSpace.Seg.iter
#print axioms ShiSpace.Seg.single
#print axioms ShiSpace.Seg.forall_of_halted
#print axioms ShiSpace.Seg.of_frame
#print axioms ShiSpace.not_terminal_before
#print axioms ShiSpace.iterate_lift_before_terminal
#print axioms ShiSpace.Seg.lift_terminal
