import ReversibleLeafPaddedFormulaClean
import ReversibleIndexGuardCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem indexGuardCode_embed (g : TickIndexGuard) (caller : L → CounterInstr R L)
    (capacity position left right tmp : R) (le gt l : L) :
    indexGuardCode g caller capacity position left right tmp le gt (indexGuardExit g l) =
      (caller l).relabel (indexGuardExit g) := by
  rw [indexGuardCode, indexGuardExit, indexExpressionCode_embed, indexExpressionCode_embed]
  change (((caller l).relabel Sum.inr).relabel (indexExpressionExit g.right)).relabel
    (indexExpressionExit g.left) = _
  cases caller l <;> rfl

/-- Finite counter instruction templates, with explicit continuation interfaces and run data. -/
structure CounterProgramTemplate (R : Type) where
  Labels : Type → Type
  finite : ∀ (L : Type), Fintype L → Fintype (Labels L)
  code : {L : Type} → (L → CounterInstr R L) → L → Labels L → CounterInstr R (Labels L)
  entry : {L : Type} → L → Labels L
  exit : {L : Type} → L → Labels L
  ready : (R → Nat) → Prop
  steps : (R → Nat) → Nat
  counters : (R → Nat) → R → Nat
  bytes : (R → Nat) → List Bool

def CounterProgramTemplate.Embeds (p : CounterProgramTemplate R) : Prop :=
  ∀ (L : Type) (caller : L → CounterInstr R L) (stop l : L),
    p.code caller stop (p.exit l) = (caller l).relabel p.exit

def CounterProgramTemplate.Runs (p : CounterProgramTemplate R) : Prop :=
  ∀ (L : Type) (caller : L → CounterInstr R L) (stop : L) (cs : R → Nat) (ys : List Bool),
    p.ready cs → CounterRun (p.code caller stop) ⟨some (p.entry stop), cs, ys⟩ (p.steps cs)
      ⟨some (p.exit stop), p.counters cs, p.bytes cs ++ ys⟩

structure GuardProgramRegisters (R : Type) where
  capacity : R
  position : R
  left : R
  right : R
  tmp : R

structure GuardProgramRegisters.Valid (r : GuardProgramRegisters R) : Prop where
  capacity_left : r.capacity ≠ r.left
  position_left : r.position ≠ r.left
  capacity_right : r.capacity ≠ r.right
  position_right : r.position ≠ r.right
  capacity_tmp : r.capacity ≠ r.tmp
  position_tmp : r.position ≠ r.tmp
  left_tmp : r.left ≠ r.tmp
  right_tmp : r.right ≠ r.tmp
  left_right : r.left ≠ r.right

/-- Both branch graphs are fixed. The checked clean guard selects which graph actually runs. -/
noncomputable def guardedProgramTemplate (r : GuardProgramRegisters R) (g : TickIndexGuard)
    (y n : CounterProgramTemplate R) : CounterProgramTemplate R where
  Labels := fun L => IndexGuardLabels g (y.Labels (n.Labels L))
  finite := fun L f => by
    letI := f
    letI := n.finite L f
    letI := y.finite (n.Labels L) inferInstance
    infer_instance
  code := fun caller stop => indexGuardCode g (y.code (n.code caller stop) (n.exit stop))
    r.capacity r.position r.left r.right r.tmp (y.entry (n.exit stop)) (y.exit (n.entry stop))
  entry := fun _ => .inl 0
  exit := fun stop => indexGuardExit g (y.exit (n.exit stop))
  ready := fun cs => cs r.left = 0 ∧ cs r.right = 0 ∧ cs r.tmp = 0 ∧ y.ready cs ∧ n.ready cs
  steps := fun cs => indexGuardSteps g r.capacity r.position r.left r.right cs +
    if g.eval (cs r.capacity) (cs r.position) then y.steps cs else n.steps cs
  counters := fun cs => if g.eval (cs r.capacity) (cs r.position) then y.counters cs else n.counters cs
  bytes := fun cs => if g.eval (cs r.capacity) (cs r.position) then y.bytes cs else n.bytes cs

end ShiReversibleGenerator
