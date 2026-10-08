import ReversibleConstantInitializationBounds
import ReversibleLocatedBodyBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard symbolRank : Nat) (value backward : Bool)

abbrev LocatedConstantLabels (L : Type) :=
  CellCoordinateLabels header stackRank symbolCard symbolRank (ConstantInitializationLabels value backward L)

def locatedConstantEntry {L : Type} (stop : L) :
    LocatedConstantLabels header stackRank symbolCard symbolRank value backward L :=
  cleanupEntry [(Sum.inr 1 : InitializationRegister)]
    (operationEntry (cellCoordinateOperations header stackRank symbolCard symbolRank)
      (constantInitializationEntry value backward stop))

def locatedConstantExit {L : Type} (stop : L) :
    LocatedConstantLabels header stackRank symbolCard symbolRank value backward L :=
  cleanupExit [(Sum.inr 1 : InitializationRegister)]
    (operationExit (cellCoordinateOperations header stackRank symbolCard symbolRank)
      (constantInitializationExit value backward stop))

def locatedConstantCode {L : Type} (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    LocatedConstantLabels header stackRank symbolCard symbolRank value backward L →
      CounterInstr InitializationRegister (LocatedConstantLabels header stackRank symbolCard symbolRank value backward L) :=
  cellCoordinateCode header stackRank symbolCard symbolRank
    (constantInitializationCode value backward caller stop) (constantInitializationEntry value backward stop)

def locatedConstantCounters (cs : InitializationRegister → Nat) :=
  constantInitializationCounters value backward (cellCoordinateResult header stackRank symbolCard symbolRank cs)

def locatedConstantSteps (cs : InitializationRegister → Nat) :=
  (cleanupSteps [(Sum.inr 1 : InitializationRegister)] cs +
    operationSteps (cellCoordinateOperations header stackRank symbolCard symbolRank)
      (cleanupCounters [(Sum.inr 1 : InitializationRegister)] cs)) +
    constantInitializationSteps value backward (cellCoordinateResult header stackRank symbolCard symbolRank cs)

/-- Both fixed metadata coordinates and runtime non-input stack cells use this finite graph. -/
theorem locatedConstant_run {L : Type} (caller : L → CounterInstr InitializationRegister L)
    (stop : L) (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0)
    (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (locatedConstantCode header stackRank symbolCard symbolRank value backward caller stop)
      ⟨some (locatedConstantEntry header stackRank symbolCard symbolRank value backward stop), cs, ys⟩
      (locatedConstantSteps header stackRank symbolCard symbolRank value backward cs)
      ⟨some (locatedConstantExit header stackRank symbolCard symbolRank value backward stop),
        locatedConstantCounters header stackRank symbolCard symbolRank value backward cs,
        constantInitializationPayload value backward
          (cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank)) ++ ys⟩ := by
  let inner := constantInitializationCode value backward caller stop
  let code := locatedConstantCode header stackRank symbolCard symbolRank value backward caller stop
  let ops := cellCoordinateOperations header stackRank symbolCard symbolRank
  let prepared := cellCoordinateResult header stackRank symbolCard symbolRank cs
  have hc := cellCoordinate_run header stackRank symbolCard symbolRank inner
    (constantInitializationEntry value backward stop) cs hb ht ys
  have hp := constantInitialization_run value backward caller stop prepared
    (by simpa [prepared, cellCoordinateResult_eq] using hb)
    (by simpa [prepared, cellCoordinateResult_eq] using ht) ys
  have hp' := CounterRun.relabel inner code
    (fun l => cleanupExit [(Sum.inr 1 : InitializationRegister)] (operationExit ops l))
    (by
      intro l
      simp only [code, locatedConstantCode, cellCoordinateCode, ops, inner,
        cleanupCode_embed, operationCode_embed]
      exact CounterInstr.relabel_comp (operationExit ops)
        (cleanupExit [(Sum.inr 1 : InitializationRegister)]) (inner l)) hp
  dsimp only [CounterCfg.relabel, Option.map] at hp'
  set_option backward.isDefEq.respectTransparency false in
    simpa [locatedConstantSteps, locatedConstantCounters, locatedConstantEntry,
      locatedConstantExit, prepared, cellCoordinateResult_eq, code, ops] using CounterRun.trans code hc hp'

theorem locatedConstant_polynomial_bound (sizes : InitializationRegister → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      (∀ r, cs r ≤ (sizes r).eval n) →
      locatedConstantSteps header stackRank symbolCard symbolRank value backward cs ≤ clock.eval n := by
  let preparedSizes := cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes
  obtain ⟨clock, hc⟩ := constantInitialization_polynomial_bound value backward preparedSizes
  refine ⟨cellCoordinateClock header stackRank symbolCard symbolRank sizes + clock, ?_⟩
  intro n cs h
  have hprep : ∀ r, cellCoordinateResult header stackRank symbolCard symbolRank cs r ≤ (preparedSizes r).eval n := by
    intro r
    change cellCoordinateResult header stackRank symbolCard symbolRank cs r ≤
      (cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes r).eval n
    rw [congrFun (cellCoordinatePolynomials_eval header stackRank symbolCard symbolRank sizes n) r]
    exact operationResult_mono _ _ _ (cleanupCounters_mono _ cs _ h) r
  have ha := Nat.add_le_add (cleanupSteps_mono [(Sum.inr 1 : InitializationRegister)] cs _ h)
    (operationSteps_mono (cellCoordinateOperations header stackRank symbolCard symbolRank) _ _
      (cleanupCounters_mono [(Sum.inr 1 : InitializationRegister)] cs _ h))
  rw [Polynomial.eval_add, cellCoordinateClock_eval]
  exact Nat.add_le_add ha (hc n _ hprep)

theorem locatedConstant_preserves_metadata (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inl r) = cs (.inl r) := by
  rw [locatedConstantCounters, constantInitialization_preserves_metadata, cellCoordinateResult_eq]
  simp

theorem locatedConstant_preserves_index (cs : InitializationRegister → Nat) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 0) = cs (.inr 0) := by
  rw [locatedConstantCounters, constantInitialization_preserves_index, cellCoordinateResult_eq]
  simp

theorem locatedConstant_preserves_remaining (cs : InitializationRegister → Nat) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 11) = cs (.inr 11) := by
  rw [locatedConstantCounters, constantInitialization_preserves_remaining, cellCoordinateResult_eq]
  simp

theorem locatedConstantCode_embed {L : Type} (caller : L → CounterInstr InitializationRegister L)
    (stop l : L) :
    locatedConstantCode header stackRank symbolCard symbolRank value backward caller stop
      (locatedConstantExit header stackRank symbolCard symbolRank value backward l) =
      (caller l).relabel (locatedConstantExit header stackRank symbolCard symbolRank value backward) := by
  simp only [locatedConstantCode, cellCoordinateCode, locatedConstantExit,
    cleanupCode_embed, operationCode_embed, constantInitializationCode_embed]
  cases caller l <;> rfl

theorem locatedConstantExit_injective {L : Type} :
    Function.Injective (locatedConstantExit header stackRank symbolCard symbolRank value backward (L := L)) := by
  intro l k h
  exact fixedNodeExit_injective initializationNodeRegisters (constantInitializationTemplates value backward)
    (operationExit_injective initializationAddressOperations
      (cleanupExit_injective initializationAddressCleanup
        (operationExit_injective (cellCoordinateOperations header stackRank symbolCard symbolRank)
          (cleanupExit_injective [(Sum.inr 1 : InitializationRegister)] h))))

end ShiReversibleGenerator
