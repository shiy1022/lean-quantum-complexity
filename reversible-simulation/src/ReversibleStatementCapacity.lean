import ReversibleMachineEncoding

set_option autoImplicit false

namespace ShiReversibleTM

local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Room for every push on either branch of a statement, including its interior. -/
def StackRoom (capacity : Nat) (q : Turing.TM2.Stmt Γ Λ σ)
    (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (S k).length + pushBound q ≤ capacity

theorem StackRoom.push {capacity : Nat} {k : K} {f : σ → Γ k}
    {q : Turing.TM2.Stmt Γ Λ σ} {S : ∀ k, List (Γ k)}
    (h : StackRoom capacity (.push k f q) S) (v : σ) :
    StackRoom capacity q (Function.update S k (f v :: S k)) := by
  intro i
  have hi := h i
  by_cases hik : i = k
  · subst i
    simpa [Function.update_self, pushBound, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hi
  · simp only [Function.update_of_ne hik]
    simp only [pushBound] at hi
    omega

theorem StackRoom.pop {capacity : Nat} {k : K} {f : σ → Option (Γ k) → σ}
    {q : Turing.TM2.Stmt Γ Λ σ} {S : ∀ k, List (Γ k)}
    (h : StackRoom capacity (.pop k f q) S) :
    StackRoom capacity q (Function.update S k (S k).tail) := by
  intro i
  have hi := h i
  by_cases hik : i = k
  · subst i
    simp only [Function.update_self, List.length_tail]
    simp only [pushBound] at hi
    omega
  · simpa [Function.update_of_ne hik, pushBound] using hi

theorem StackRoom.branch_left {capacity : Nat} {f : σ → Bool}
    {q r : Turing.TM2.Stmt Γ Λ σ} {S : ∀ k, List (Γ k)}
    (h : StackRoom capacity (.branch f q r) S) : StackRoom capacity q S := by
  intro k
  exact (Nat.add_le_add_left (le_max_left _ _) _).trans (h k)

theorem StackRoom.branch_right {capacity : Nat} {f : σ → Bool}
    {q r : Turing.TM2.Stmt Γ Λ σ} {S : ∀ k, List (Γ k)}
    (h : StackRoom capacity (.branch f q r) S) : StackRoom capacity r S := by
  intro k
  exact (Nat.add_le_add_left (le_max_right _ _) _).trans (h k)

/-- Statement execution stays within the fixed representation; no truncation premise is hidden. -/
noncomputable def BoundedCfg.execute {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : pushSymbols q ⊆ machineSymbols tm)
    (hroom : StackRoom capacity q c.cfg.stk) : BoundedCfg tm capacity where
  cfg := Turing.TM2.stepAux q c.cfg.var c.cfg.stk
  length_bound k := (stepAux_stack_length q c.cfg.var c.cfg.stk k).trans (hroom k)
  alphabet := stepAux_alphabet q (machineSymbols tm) hq c.cfg.var c.cfg.stk c.alphabet

@[simp] theorem BoundedCfg.execute_cfg {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : pushSymbols q ⊆ machineSymbols tm)
    (hroom : StackRoom capacity q c.cfg.stk) :
    (c.execute q hq hroom).cfg = Turing.TM2.stepAux q c.cfg.var c.cfg.stk := rfl

end ShiReversibleTM
