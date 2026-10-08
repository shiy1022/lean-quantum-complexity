import ReversibleSymbolicFormula
import ReversibleLayerCounting
import ReversibleFinalCleanup

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def nodeFieldOperations (x y z : SymbolicWire R) (p q r : R) : List (GeneratorOperation R) :=
  [.affine ⟨x.source, p, x.offset, 1⟩, .affine ⟨y.source, q, y.offset, 1⟩,
    .affine ⟨z.source, r, z.offset, 1⟩]

def nodeFieldResult (x y z : SymbolicWire R) (p q r : R) (cs : R → Nat) : R → Nat :=
  operationResult (nodeFieldOperations x y z p q r) (cleanupCounters [p, q, r] cs)

/-- Only the three field registers change; symbolic references read caller registers. -/
theorem nodeFieldResult_eval (x y z : SymbolicWire R) (p q r : R)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x.source ≠ p ∧ x.source ≠ q ∧ x.source ≠ r)
    (hy : y.source ≠ p ∧ y.source ≠ q ∧ y.source ≠ r)
    (hz : z.source ≠ p ∧ z.source ≠ q ∧ z.source ≠ r) (cs : R → Nat) :
    nodeFieldResult x y z p q r cs =
      Function.update (Function.update (Function.update cs p (x.eval cs)) q (y.eval cs)) r (z.eval cs) := by
  funext j
  by_cases hjp : j = p <;> by_cases hjq : j = q <;> by_cases hjr : j = r
  all_goals simp_all [nodeFieldResult, nodeFieldOperations, operationResult, GeneratorOperation.apply,
    AffineAtom.apply, cleanupCounters_apply, SymbolicWire.eval, ne_comm]

abbrev SymbolicNodeLabels (kind : AssignmentEmissionKind) (x y z : SymbolicWire R)
    (p q r count : R) (L : Type) :=
  CleanupLabels [p, q, r] (GeneratorOperationLabels (nodeFieldOperations x y z p q r)
    (GeneratorActionLabels (countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers) L))

def symbolicNodeCode (kind : AssignmentEmissionKind) (x y z : SymbolicWire R)
    (p q r count buf tmp : R) (caller : L → CounterInstr R L) (stop : L) :
    SymbolicNodeLabels kind x y z p q r count L →
      CounterInstr R (SymbolicNodeLabels kind x y z p q r count L) :=
  let actions := countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers
  let emit := actionCode actions caller buf tmp stop
  let emitStart := actionEntry actions stop
  let fields := operationCode (nodeFieldOperations x y z p q r) emit buf tmp emitStart
  cleanupCode [p, q, r] fields (operationEntry (nodeFieldOperations x y z p q r) emitStart)

theorem symbolicNodeCode_run (kind : AssignmentEmissionKind) (x y z : SymbolicWire R)
    (p q r count buf tmp : R) (caller : L → CounterInstr R L) (stop : L)
    (hv : ∀ op ∈ nodeFieldOperations x y z p q r, op.Valid buf tmp)
    (hp : p ≠ buf ∧ p ≠ tmp) (hq : q ≠ buf ∧ q ≠ tmp) (hr : r ≠ buf ∧ r ≠ tmp)
    (hpc : p ≠ count) (hct : count ≠ tmp) (hcb : count ≠ buf) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    let regs := [p, q, r]
    let ops := nodeFieldOperations x y z p q r
    let actions := countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers
    CounterRun (symbolicNodeCode kind x y z p q r count buf tmp caller stop)
      ⟨some (cleanupEntry regs (operationEntry ops (actionEntry actions stop))), cs, ys⟩
      ((cleanupSteps regs cs + operationSteps ops (cleanupCounters regs cs)) +
        actionSteps actions (nodeFieldResult x y z p q r cs))
      ⟨some (cleanupExit regs (operationExit ops (actionExit actions stop))),
        Function.update (nodeFieldResult x y z p q r cs) count
          (nodeFieldResult x y z p q r cs count + kind.layers),
        emissionBytes (assignmentAtoms kind p q r) (nodeFieldResult x y z p q r cs) ++ ys⟩ := by
  let regs := [p, q, r]
  let ops := nodeFieldOperations x y z p q r
  let actions := countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers
  let emit := actionCode actions caller buf tmp stop
  let emitStart := actionEntry actions stop
  let fields := operationCode ops emit buf tmp emitStart
  let fieldStart := operationEntry ops emitStart
  let code := symbolicNodeCode kind x y z p q r count buf tmp caller stop
  have hc := cleanupCode_run regs fields fieldStart cs ys
  have ht₀ : cleanupCounters regs cs tmp = 0 := by
    simp [regs, cleanupCounters_apply, Ne.symm hp.2, Ne.symm hq.2, Ne.symm hr.2, ht]
  have hf := operationCode_run ops emit buf tmp emitStart hv hbt (cleanupCounters regs cs)
    (by simp [regs, cleanupCounters_apply, Ne.symm hp.1, Ne.symm hq.1, Ne.symm hr.1, hb]) ht₀ ys
  have hf' := CounterRun.relabel fields code (cleanupExit regs)
    (cleanupCode_embed regs fields fieldStart) hf
  have hfield (s : R) (hs : s = buf ∨ s = tmp) : nodeFieldResult x y z p q r cs s = cs s := by
    rcases hs with rfl | rfl
    all_goals
      unfold nodeFieldResult
      simp only [nodeFieldOperations, operationResult]
      simp only [GeneratorOperation.apply]
      simp [AffineAtom.apply, Ne.symm hp.1, Ne.symm hq.1, Ne.symm hr.1,
        Ne.symm hp.2, Ne.symm hq.2, Ne.symm hr.2, cleanupCounters_apply]
  have he := countedEmission_run (assignmentAtoms kind p q r) p count buf tmp kind.layers caller stop
    (assignmentAtoms_valid kind p q r buf tmp hp hq hr) hpc hp.2 hct hcb hbt
    (nodeFieldResult x y z p q r cs) (by rw [hfield buf (Or.inl rfl)]; exact hb)
    (by rw [hfield tmp (Or.inr rfl)]; exact ht) ys
  have he' := CounterRun.relabel emit fields (operationExit ops)
    (operationCode_embed ops emit buf tmp emitStart) he
  have he'' := CounterRun.relabel fields code (cleanupExit regs)
    (cleanupCode_embed regs fields fieldStart) he'
  change CounterRun code
    ⟨some (cleanupExit regs fieldStart), cleanupCounters regs cs, ys⟩
    (operationSteps ops (cleanupCounters regs cs))
    ⟨some (cleanupExit regs (operationExit ops emitStart)), nodeFieldResult x y z p q r cs, ys⟩ at hf'
  change CounterRun code
    ⟨some (cleanupExit regs (operationExit ops emitStart)), nodeFieldResult x y z p q r cs, ys⟩
    (actionSteps actions (nodeFieldResult x y z p q r cs))
    ⟨some (cleanupExit regs (operationExit ops (actionExit actions stop))),
      Function.update (nodeFieldResult x y z p q r cs) count
        (nodeFieldResult x y z p q r cs count + kind.layers),
      emissionBytes (assignmentAtoms kind p q r) (nodeFieldResult x y z p q r cs) ++ ys⟩ at he''
  exact CounterRun.trans code (CounterRun.trans code hc hf') he''

noncomputable def operationResultPolynomial (ops : List (GeneratorOperation R))
    (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  match ops with
  | [] => sizes
  | op :: ops => operationResultPolynomial ops (op.applyPolynomial sizes)

theorem operationResultPolynomial_eval (ops : List (GeneratorOperation R))
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fun r => (operationResultPolynomial ops sizes r).eval n) =
      operationResult ops (fun r => (sizes r).eval n) := by
  induction ops generalizing sizes with
  | nil => rfl
  | cons op ops ih =>
      simp only [operationResultPolynomial, ih, GeneratorOperation.applyPolynomial_eval, operationResult]

theorem symbolicNode_clock (kind : AssignmentEmissionKind) (x y z : SymbolicWire R)
    (p q r count : R) (sizes : R → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n,
      ((cleanupSteps [p, q, r] (fun s => (sizes s).eval n) +
        operationSteps (nodeFieldOperations x y z p q r)
          (cleanupCounters [p, q, r] (fun s => (sizes s).eval n))) +
        actionSteps (countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers)
          (nodeFieldResult x y z p q r (fun s => (sizes s).eval n))) = clock.eval n := by
  let regs := [p, q, r]
  let cleared : R → Polynomial Nat := fun s => if s ∈ regs then 0 else sizes s
  let ops := nodeFieldOperations x y z p q r
  let fieldSizes := operationResultPolynomial ops cleared
  let actions := countedEmissionActions (assignmentAtoms kind p q r) p count kind.layers
  refine ⟨(cleanupClock regs sizes + operationClock ops cleared) + actionClock actions fieldSizes, ?_⟩
  intro n
  have hc : (fun s => (cleared s).eval n) = cleanupCounters regs (fun s => (sizes s).eval n) := by
    funext s
    by_cases hs : s ∈ regs <;> simp [cleared, cleanupCounters_apply, hs]
  simp only [Polynomial.eval_add, cleanupClock_eval, operationClock_eval, actionClock_eval]
  rw [show (fun s => (fieldSizes s).eval n) = nodeFieldResult x y z p q r (fun s => (sizes s).eval n) by
    simp only [fieldSizes, operationResultPolynomial_eval, hc]; rfl]
  rw [hc]

end ShiReversibleGenerator
