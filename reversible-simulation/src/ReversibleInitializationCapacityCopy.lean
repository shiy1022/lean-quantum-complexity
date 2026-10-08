import ReversibleConstantInitializationStart

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Copy the runtime capacity into a fresh loop counter without consuming its source. -/
theorem initializationCapacity_copy_run {L : Type} (target : InitializationRegister)
    (caller : L → CounterInstr InitializationRegister L) (stop : L)
    (cs : InitializationRegister → Nat) (hz : cs target = 0) (ht : cs (.inl 5) = 0)
    (hv : (⟨.inl 2, target, 0, 1⟩ : AffineAtom InitializationRegister).Valid (.inl 5))
    (ys : List Bool) :
    CounterRun (affineCode caller 0 1 (.inl 2) target (.inl 5) stop)
      ⟨some (affineStart 0 1 stop), cs, ys⟩ (7 * cs (.inl 2) + 2)
      ⟨some (.inr (.inr stop)), Function.update cs target (cs (.inl 2)), ys⟩ := by
  have h := AffineAtom.run (⟨.inl 2, target, 0, 1⟩ : AffineAtom InitializationRegister)
    caller (.inl 5) stop hv cs ht ys
  simpa only [AffineAtom.apply, AffineAtom.steps, hz, Nat.one_mul, Nat.zero_add, Nat.add_zero] using h

/-- Freshness of private counters is the only prelude-specific fact needed by the capacity copy. -/
theorem initializationCapacity_copy_metadata (cs : InitializationRegister → Nat)
    (target : Fin 16) (r : WorkspaceRegister) :
    Function.update cs (.inr target) (cs (.inl 2)) (.inl r) = cs (.inl r) := by
  simp

end ShiReversibleGenerator
