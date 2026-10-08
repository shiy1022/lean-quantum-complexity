import ReversibleStridedTickCoordinateBindingRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R L : Type} [DecidableEq R]

theorem stridedTickCoordinateBindingSteps_polynomial (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (hv : r.Valid) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      stridedTickCoordinateBindingSteps tm r inputStride coordinate cs ≤ clock.eval n := by
  cases coordinate with
  | inl z =>
    refine ⟨Polynomial.C 9 * bound + Polynomial.C (3 + tickCoordinateOffset tm (.inl z) * inputStride), ?_⟩
    intro n cs hb
    have ht := hb r.target
    have hi := hb r.input
    simp only [stridedTickCoordinateBindingSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    omega
  | inr z =>
    exact symbolicCellBindingSteps_polynomial z.1.2 r.input r.capacity r.position r.query r.target
      (tickCoordinateOffset tm (.inr z) * inputStride) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) hv.input_query hv.capacity_query
      hv.input_target hv.capacity_target hv.query_target bound

theorem stridedTickCoordinateBinding_source_frame (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (hv : r.Valid) (cs : R → Nat) :
    ∀ q ∈ [r.input, r.capacity, r.position, r.query, r.tmp],
      Function.update cs r.target (stridedTickCoordinateAddress tm r inputStride coordinate cs) q = cs q := by
  intro q hq
  simp at hq
  rcases hq with h | h | h | h | h
  · subst q; simp [hv.input_target]
  · subst q; simp [hv.capacity_target]
  · subst q; simp [hv.position_target]
  · subst q; simp [hv.query_target]
  · subst q; simp [Ne.symm hv.target_tmp]

/-- One fixed coordinate binding program has finite control, exact address output and a polynomial clock. -/
theorem stridedTickCoordinateBindingCode_certificate [Fintype L] (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (inputStride : Nat) (coordinate : TickSymbolicCoordinate tm)
    (caller : L → CounterInstr R L) (stop : L) (hv : r.Valid) (bound : Polynomial Nat) :
    ∃ _finite : Fintype (StridedTickCoordinateBindingLabels tm r inputStride coordinate L), ∃ clock : Polynomial Nat,
      ∀ n (cs : R → Nat) (ys : List Bool), (∀ q, cs q ≤ bound.eval n) →
        cs r.query = 0 → cs r.tmp = 0 →
        ∃ steps, CounterRun (stridedTickCoordinateBindingCode tm r inputStride coordinate caller stop)
          ⟨some (stridedTickCoordinateBindingEntry tm r inputStride coordinate L), cs, ys⟩ steps
          ⟨some (stridedTickCoordinateBindingExit tm r inputStride coordinate stop),
            Function.update cs r.target (stridedTickCoordinateAddress tm r inputStride coordinate cs), ys⟩ ∧ steps ≤ clock.eval n := by
  obtain ⟨clock, hclock⟩ := stridedTickCoordinateBindingSteps_polynomial tm r inputStride coordinate hv bound
  refine ⟨inferInstance, clock, ?_⟩
  intro n cs ys hb hq hx
  exact ⟨stridedTickCoordinateBindingSteps tm r inputStride coordinate cs,
    stridedTickCoordinateBindingCode_run tm r inputStride coordinate caller stop hv cs hq hx ys, hclock n cs hb⟩

end ShiReversibleGenerator
