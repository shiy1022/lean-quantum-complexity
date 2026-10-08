import ReversibleSymbolicNodeEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

structure NodePrinterRegisters (R : Type) where
  p : R
  q : R
  r : R
  count : R
  buf : R
  tmp : R

def NodePrinterRegisters.Valid (r : NodePrinterRegisters R) : Prop :=
  r.p ≠ r.buf ∧ r.p ≠ r.tmp ∧ r.q ≠ r.buf ∧ r.q ≠ r.tmp ∧
  r.r ≠ r.buf ∧ r.r ≠ r.tmp ∧ r.p ≠ r.count ∧ r.count ≠ r.tmp ∧
  r.count ≠ r.buf ∧ r.buf ≠ r.tmp

structure FixedNodeTemplate (R : Type) where
  kind : AssignmentEmissionKind
  x : SymbolicWire R
  y : SymbolicWire R
  z : SymbolicWire R

def FixedNodeTemplate.ops (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) :=
  nodeFieldOperations t.x t.y t.z r.p r.q r.r

def FixedNodeTemplate.actions (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) :=
  countedEmissionActions (assignmentAtoms t.kind r.p r.q r.r) r.p r.count t.kind.layers

abbrev FixedNodeTemplate.Label (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (L : Type) :=
  SymbolicNodeLabels t.kind t.x t.y t.z r.p r.q r.r r.count L

def FixedNodeTemplate.entry (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (stop : L) : t.Label r L :=
  cleanupEntry [r.p, r.q, r.r] (operationEntry (t.ops r) (actionEntry (t.actions r) stop))

def FixedNodeTemplate.embed (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (l : L) : t.Label r L :=
  cleanupExit [r.p, r.q, r.r] (operationExit (t.ops r) (actionExit (t.actions r) l))

def FixedNodeTemplate.code (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) : t.Label r L → CounterInstr R (t.Label r L) :=
  symbolicNodeCode t.kind t.x t.y t.z r.p r.q r.r r.count r.buf r.tmp caller stop

def FixedNodeTemplate.fields (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (cs : R → Nat) : R → Nat :=
  nodeFieldResult t.x t.y t.z r.p r.q r.r cs

def FixedNodeTemplate.counters (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (cs : R → Nat) : R → Nat :=
  Function.update (t.fields r cs) r.count (t.fields r cs r.count + t.kind.layers)

def FixedNodeTemplate.bytes (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (cs : R → Nat) : List Bool :=
  emissionBytes (assignmentAtoms t.kind r.p r.q r.r) (t.fields r cs)

def FixedNodeTemplate.steps (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) (cs : R → Nat) : Nat :=
  (cleanupSteps [r.p, r.q, r.r] cs + operationSteps (t.ops r) (cleanupCounters [r.p, r.q, r.r] cs)) +
    actionSteps (t.actions r) (t.fields r cs)

theorem FixedNodeTemplate.code_embed (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop l : L) :
    t.code r caller stop (t.embed r l) = (caller l).relabel (t.embed r) := by
  simp only [code, symbolicNodeCode, embed, ops, actions, cleanupCode_embed, operationCode_embed, actionCode_embed]
  cases caller l <;> rfl

theorem FixedNodeTemplate.run (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hv : ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (cs : R → Nat) (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    CounterRun (t.code r caller stop) ⟨some (t.entry r stop), cs, ys⟩ (t.steps r cs)
      ⟨some (t.embed r stop), t.counters r cs, t.bytes r cs ++ ys⟩ := by
  rcases hr with ⟨hpb, hpt, hqb, hqt, hrb, hrt, hpc, hct, hcb, hbt⟩
  exact symbolicNodeCode_run t.kind t.x t.y t.z r.p r.q r.r r.count r.buf r.tmp caller stop hv
    ⟨hpb, hpt⟩ ⟨hqb, hqt⟩ ⟨hrb, hrt⟩ hpc hct hcb hbt cs hb ht ys

theorem nodeFieldResult_other (x y z : SymbolicWire R) (p q r s : R)
    (hp : s ≠ p) (hq : s ≠ q) (hr : s ≠ r) (cs : R → Nat) :
    nodeFieldResult x y z p q r cs s = cs s := by
  simp [nodeFieldResult, nodeFieldOperations, operationResult, GeneratorOperation.apply,
    AffineAtom.apply, cleanupCounters_apply, hp, hq, hr]

theorem FixedNodeTemplate.counters_buffer (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hr : r.Valid) (cs : R → Nat) : t.counters r cs r.buf = cs r.buf := by
  rcases hr with ⟨hpb, hpt, hqb, hqt, hrb, hrt, hpc, hct, hcb, hbt⟩
  simp [counters, fields, Ne.symm hcb, nodeFieldResult_other, Ne.symm hpb, Ne.symm hqb, Ne.symm hrb]

theorem FixedNodeTemplate.counters_scratch (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hr : r.Valid) (cs : R → Nat) : t.counters r cs r.tmp = cs r.tmp := by
  rcases hr with ⟨hpb, hpt, hqb, hqt, hrb, hrt, hpc, hct, hcb, hbt⟩
  simp [counters, fields, Ne.symm hct, nodeFieldResult_other, Ne.symm hpt, Ne.symm hqt, Ne.symm hrt]

def FixedNodeLabels (r : NodePrinterRegisters R) : List (FixedNodeTemplate R) → Type → Type
  | [], L => L
  | t :: ts, L => t.Label r (FixedNodeLabels r ts L)

def fixedNodeEntry (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (stop : L) : FixedNodeLabels r ts L :=
  match ts with
  | [] => stop
  | t :: ts => t.entry r (fixedNodeEntry r ts stop)

def fixedNodeExit (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (l : L) : FixedNodeLabels r ts L :=
  match ts with
  | [] => l
  | t :: ts => t.embed r (fixedNodeExit r ts l)

def fixedNodeCode (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop : L) : FixedNodeLabels r ts L → CounterInstr R (FixedNodeLabels r ts L) :=
  match ts with
  | [] => caller
  | t :: ts => t.code r (fixedNodeCode r ts caller stop) (fixedNodeEntry r ts stop)

def fixedNodeCounters (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (cs : R → Nat) : R → Nat :=
  match ts with
  | [] => cs
  | t :: ts => fixedNodeCounters r ts (t.counters r cs)

def fixedNodeBytes (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (cs : R → Nat) : List Bool :=
  match ts with
  | [] => []
  | t :: ts => fixedNodeBytes r ts (t.counters r cs) ++ t.bytes r cs

def fixedNodeSteps (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (cs : R → Nat) : Nat :=
  match ts with
  | [] => 0
  | t :: ts => t.steps r cs + fixedNodeSteps r ts (t.counters r cs)

/-- A fixed whole formula printing template is one finite instruction graph. -/
theorem fixedNodeCode_run (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hv : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (cs : R → Nat) (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    CounterRun (fixedNodeCode r ts caller stop) ⟨some (fixedNodeEntry r ts stop), cs, ys⟩
      (fixedNodeSteps r ts cs) ⟨some (fixedNodeExit r ts stop), fixedNodeCounters r ts cs,
        fixedNodeBytes r ts cs ++ ys⟩ := by
  induction ts generalizing cs ys with
  | nil => exact CounterRun.refl _
  | cons t ts ih =>
      let inner := fixedNodeCode r ts caller stop
      let code := fixedNodeCode r (t :: ts) caller stop
      have h₁ := t.run r inner (fixedNodeEntry r ts stop) hr (hv t (by simp)) cs hb ht ys
      have h₂ := ih (fun u hu => hv u (by simp [hu])) (t.counters r cs)
        (by rw [t.counters_buffer r hr]; exact hb) (by rw [t.counters_scratch r hr]; exact ht)
        (t.bytes r cs ++ ys)
      have h₃ := CounterRun.relabel inner code (t.embed r)
        (t.code_embed r inner (fixedNodeEntry r ts stop)) h₂
      change CounterRun code ⟨some (t.embed r (fixedNodeEntry r ts stop)), t.counters r cs, t.bytes r cs ++ ys⟩
        (fixedNodeSteps r ts (t.counters r cs))
        ⟨some (t.embed r (fixedNodeExit r ts stop)), fixedNodeCounters r ts (t.counters r cs),
          fixedNodeBytes r ts (t.counters r cs) ++ (t.bytes r cs ++ ys)⟩ at h₃
      have h := CounterRun.trans code h₁ h₃
      convert h using 1 <;> (try simp [code, fixedNodeEntry, fixedNodeExit, fixedNodeSteps,
        fixedNodeCounters, fixedNodeBytes, List.append_assoc]) <;> rfl

noncomputable instance fixedNodeLabelsFintype (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) [Fintype L] : Fintype (FixedNodeLabels r ts L) := by
  induction ts with
  | nil => exact inferInstanceAs (Fintype L)
  | cons t ts ih =>
      letI := ih
      exact inferInstanceAs (Fintype (t.Label r (FixedNodeLabels r ts L)))

noncomputable def FixedNodeTemplate.fieldsPolynomial (t : FixedNodeTemplate R)
    (r : NodePrinterRegisters R) (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  operationResultPolynomial (t.ops r) (fun s => if s ∈ [r.p, r.q, r.r] then 0 else sizes s)

theorem FixedNodeTemplate.fieldsPolynomial_eval (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fun s => (t.fieldsPolynomial r sizes s).eval n) = t.fields r (fun s => (sizes s).eval n) := by
  simp only [fieldsPolynomial, operationResultPolynomial_eval]
  congr 1
  funext s
  by_cases hs : s ∈ [r.p, r.q, r.r] <;> simp [fields, nodeFieldResult, ops, cleanupCounters_apply, hs]

noncomputable def FixedNodeTemplate.countersPolynomial (t : FixedNodeTemplate R)
    (r : NodePrinterRegisters R) (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  Function.update (t.fieldsPolynomial r sizes) r.count
    (t.fieldsPolynomial r sizes r.count + Polynomial.C t.kind.layers)

theorem FixedNodeTemplate.countersPolynomial_eval (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fun s => (t.countersPolynomial r sizes s).eval n) = t.counters r (fun s => (sizes s).eval n) := by
  have hf := t.fieldsPolynomial_eval r sizes n
  funext s
  by_cases hs : s = r.count
  · subst s
    simp [countersPolynomial, counters, ← congrFun hf r.count]
  · simp [countersPolynomial, counters, hs, ← congrFun hf s]

noncomputable def FixedNodeTemplate.clock (t : FixedNodeTemplate R)
    (r : NodePrinterRegisters R) (sizes : R → Polynomial Nat) : Polynomial Nat :=
  Classical.choose (symbolicNode_clock t.kind t.x t.y t.z r.p r.q r.r r.count sizes)

theorem FixedNodeTemplate.clock_eval (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    (t.clock r sizes).eval n = t.steps r (fun s => (sizes s).eval n) :=
  (Classical.choose_spec (symbolicNode_clock t.kind t.x t.y t.z r.p r.q r.r r.count sizes) n).symm

noncomputable def fixedNodeClock (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match ts with
  | [] => 0
  | t :: ts => t.clock r sizes + fixedNodeClock r ts (t.countersPolynomial r sizes)

theorem fixedNodeClock_eval (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fixedNodeClock r ts sizes).eval n = fixedNodeSteps r ts (fun s => (sizes s).eval n) := by
  induction ts generalizing sizes with
  | nil => simp [fixedNodeClock, fixedNodeSteps]
  | cons t ts ih =>
      simp only [fixedNodeClock, Polynomial.eval_add, FixedNodeTemplate.clock_eval, ih,
        FixedNodeTemplate.countersPolynomial_eval, fixedNodeSteps]

end ShiReversibleGenerator
