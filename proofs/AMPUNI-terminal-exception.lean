import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false

namespace ShiTMTerminalException

/-- Two deterministic transitions have the same first `n` steps when they
agree away from a terminal state and the reference run reaches that state
for the first time at step `n`. -/
theorem iterate_agree_until_terminal {A : Type}
    (f g : A → A) (terminal : A → Prop)
    (hagrees : ∀ x, ¬ terminal x → f x = g x)
    (hnever : ∀ x, terminal x → ∀ k : Nat, 0 < k →
      ¬ terminal (g^[k] x))
    (n : Nat) (x : A) (hfinal : terminal (g^[n] x)) :
    f^[n] x = g^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hx : ¬ terminal x := by
        intro hp
        exact (hnever x hp (n + 1) (by omega)) hfinal
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, hagrees x hx]
      exact ih (g x) hfinal

/-- A closed set of configurations reached immediately after a terminal
state supplies the non-return condition used above. -/
theorem no_return_of_closed {A : Type}
    (g : A → A) (terminal closed : A → Prop)
    (hstep : ∀ x, terminal x → closed (g x))
    (hclosed : ∀ x, closed x → closed (g x))
    (hdisjoint : ∀ x, closed x → ¬ terminal x)
    (x : A) (hx : terminal x) (k : Nat) (hk : 0 < k) :
    ¬ terminal (g^[k] x) := by
  have hstay (m : Nat) (y : A) (hy : closed y) :
      closed (g^[m] y) := by
    induction m generalizing y with
    | zero => simpa using hy
    | succ m ih =>
        rw [Function.iterate_succ_apply]
        exact ih (g y) (hclosed y hy)
  cases k with
  | zero => omega
  | succ k =>
      rw [Function.iterate_succ_apply]
      exact hdisjoint _ (hstay k (g x) (hstep x hx))

end ShiTMTerminalException
