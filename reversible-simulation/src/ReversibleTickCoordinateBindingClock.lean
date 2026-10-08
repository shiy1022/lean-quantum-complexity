import ReversibleTickCoordinateBindingRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R L : Type} [DecidableEq R]

theorem tickCoordinateBindingSteps_polynomial (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (hv : r.Valid) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      tickCoordinateBindingSteps tm r coordinate cs ≤ clock.eval n := by
  cases coordinate with
  | inl z =>
    refine ⟨Polynomial.C 9 * bound + Polynomial.C (3 + tickCoordinateOffset tm (.inl z)), ?_⟩
    intro n cs hb
    have ht := hb r.target
    have hi := hb r.input
    simp only [tickCoordinateBindingSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  | inr z =>
    exact symbolicCellBindingSteps_polynomial z.1.2 r.input r.capacity r.position r.query r.target
      (tickCoordinateOffset tm (.inr z)) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm))) hv.input_query hv.capacity_query
      hv.input_target hv.capacity_target hv.query_target bound

theorem tickCoordinateBinding_source_frame (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (hv : r.Valid) (cs : R → Nat) :
    ∀ q ∈ [r.input, r.capacity, r.position, r.query, r.tmp],
      Function.update cs r.target (tickCoordinateAddress tm r coordinate cs) q = cs q := by
  intro q hq
  simp at hq
  rcases hq with h | h | h | h | h
  · subst q; simp [hv.input_target]
  · subst q; simp [hv.capacity_target]
  · subst q; simp [hv.position_target]
  · subst q; simp [hv.query_target]
  · subst q; simp [Ne.symm hv.target_tmp]

/-- One fixed coordinate binding program has finite control, exact address output and a polynomial clock. -/
theorem tickCoordinateBindingCode_certificate [Fintype L] (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (coordinate : TickSymbolicCoordinate tm)
    (caller : L → CounterInstr R L) (stop : L) (hv : r.Valid) (bound : Polynomial Nat) :
    ∃ _finite : Fintype (TickCoordinateBindingLabels tm r coordinate L), ∃ clock : Polynomial Nat,
      ∀ n (cs : R → Nat) (ys : List Bool), (∀ q, cs q ≤ bound.eval n) →
        cs r.query = 0 → cs r.tmp = 0 →
        ∃ steps, CounterRun (tickCoordinateBindingCode tm r coordinate caller stop)
          ⟨some (tickCoordinateBindingEntry tm r coordinate L), cs, ys⟩ steps
          ⟨some (tickCoordinateBindingExit tm r coordinate stop),
            Function.update cs r.target (tickCoordinateAddress tm r coordinate cs), ys⟩ ∧ steps ≤ clock.eval n := by
  obtain ⟨clock, hclock⟩ := tickCoordinateBindingSteps_polynomial tm r coordinate hv bound
  refine ⟨inferInstance, clock, ?_⟩
  intro n cs ys hb hq hx
  exact ⟨tickCoordinateBindingSteps tm r coordinate cs,
    tickCoordinateBindingCode_run tm r coordinate caller stop hv cs hq hx ys, hclock n cs hb⟩

end ShiReversibleGenerator
