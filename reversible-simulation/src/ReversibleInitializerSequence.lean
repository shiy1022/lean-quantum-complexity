import ReversiblePreparedComponentFrames
import ReversibleCounterChain

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A fixed finite instruction graph, with its actual counted run and preserved source registers. -/
structure InitializationComponent where
  Labels : Type
  finiteLabels : Fintype Labels
  decideLabels : DecidableEq Labels
  code : Labels → CounterInstr InitializationRegister Labels
  entry : Labels
  exit : Labels
  exit_halt : code exit = .halt
  steps : Nat → (InitializationRegister → Nat) → List Bool → Nat
  counters : Nat → (InitializationRegister → Nat) → List Bool → InitializationRegister → Nat
  output : Nat → (InitializationRegister → Nat) → List Bool → List Bool
  metadata : ∀ n cs ys r, counters n cs ys (.inl r) = cs (.inl r)
  run : ∀ n cs ys, cs (.inl 0) = n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
    CounterRun code ⟨some entry, cs, ys⟩ (steps n cs ys)
      ⟨some exit, counters n cs ys, output n cs ys⟩

attribute [instance] InitializationComponent.finiteLabels InitializationComponent.decideLabels

def initializerSequenceLabels : List InitializationComponent → Type
  | [] => Unit
  | c :: cs => c.Labels ⊕ initializerSequenceLabels cs

noncomputable instance initializerSequenceFintype (cs : List InitializationComponent) :
    Fintype (initializerSequenceLabels cs) := by
  induction cs with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons c cs ih =>
      letI := ih
      exact inferInstanceAs (Fintype (c.Labels ⊕ initializerSequenceLabels cs))

noncomputable instance initializerSequenceDecidableEq (cs : List InitializationComponent) :
    DecidableEq (initializerSequenceLabels cs) := Classical.decEq _

def initializerSequenceEntry : (cs : List InitializationComponent) → initializerSequenceLabels cs
  | [] => ()
  | c :: _ => .inl c.entry

def initializerSequenceExit : (cs : List InitializationComponent) → initializerSequenceLabels cs
  | [] => ()
  | _ :: cs => .inr (initializerSequenceExit cs)

noncomputable def initializerSequenceCode : (cs : List InitializationComponent) →
    initializerSequenceLabels cs → CounterInstr InitializationRegister (initializerSequenceLabels cs)
  | [] => fun _ => .halt
  | c :: cs => chainedCounterCode c.code (initializerSequenceCode cs) c.exit
      (initializerSequenceEntry cs) (.inl 0)

def initializerSequenceCounters : List InitializationComponent → Nat →
    (InitializationRegister → Nat) → List Bool → InitializationRegister → Nat
  | [], _, cs, _ => cs
  | c :: rest, n, cs, ys => initializerSequenceCounters rest n (c.counters n cs ys) (c.output n cs ys)

def initializerSequenceOutput : List InitializationComponent → Nat →
    (InitializationRegister → Nat) → List Bool → List Bool
  | [], _, _, ys => ys
  | c :: rest, n, cs, ys => initializerSequenceOutput rest n (c.counters n cs ys) (c.output n cs ys)

def initializerSequenceSteps : List InitializationComponent → Nat →
    (InitializationRegister → Nat) → List Bool → Nat
  | [], _, _, _ => 0
  | c :: rest, n, cs, ys => c.steps n cs ys + 1 +
      initializerSequenceSteps rest n (c.counters n cs ys) (c.output n cs ys)

theorem initializerSequence_exit (components : List InitializationComponent) :
    initializerSequenceCode components (initializerSequenceExit components) = .halt := by
  induction components with
  | nil => rfl
  | cons c cs ih =>
      simp only [initializerSequenceCode, initializerSequenceExit, chainedCounterCode_right, ih,
        CounterInstr.relabel]
      rfl

theorem initializerSequence_metadata (components : List InitializationComponent) (n : Nat)
    (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    initializerSequenceCounters components n cs ys (.inl r) = cs (.inl r) := by
  induction components generalizing cs ys with
  | nil => rfl
  | cons c rest ih =>
      rw [initializerSequenceCounters, ih, c.metadata]

set_option backward.isDefEq.respectTransparency false in
/-- Each connecting branch is counted; source frames justify every subsequent actual run. -/
theorem initializerSequence_run (components : List InitializationComponent) (n : Nat)
    (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) :
    CounterRun (initializerSequenceCode components)
      ⟨some (initializerSequenceEntry components), cs, ys⟩
      (initializerSequenceSteps components n cs ys)
      ⟨some (initializerSequenceExit components), initializerSequenceCounters components n cs ys,
        initializerSequenceOutput components n cs ys⟩ := by
  induction components generalizing cs ys with
  | nil => exact CounterRun.refl _
  | cons c rest ih =>
      have hfirst := c.run n cs ys hn hb ht
      have hsecond := ih (c.counters n cs ys) (c.output n cs ys)
        (by simpa only [c.metadata] using hn)
        (by simpa only [c.metadata] using hb)
        (by simpa only [c.metadata] using ht)
      have h := chainedCounterCode_run c.code (initializerSequenceCode rest) c.exit
        (initializerSequenceEntry rest) (.inl 0) c.exit_halt
        ⟨some c.entry, cs, ys⟩ (c.counters n cs ys) (c.output n cs ys)
        ⟨some (initializerSequenceExit rest), initializerSequenceCounters rest n (c.counters n cs ys) (c.output n cs ys),
          initializerSequenceOutput rest n (c.counters n cs ys) (c.output n cs ys)⟩
        (c.steps n cs ys) (initializerSequenceSteps rest n (c.counters n cs ys) (c.output n cs ys)) hfirst hsecond
      simpa only [initializerSequenceCode, initializerSequenceEntry, initializerSequenceExit,
        initializerSequenceSteps, initializerSequenceCounters, initializerSequenceOutput, CounterCfg.relabel,
        Option.map] using h

end ShiReversibleGenerator
