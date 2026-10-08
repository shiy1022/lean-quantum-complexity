import ReversibleCore

set_option autoImplicit false

namespace ShiReversible

def Gate.normalized {n : Nat} : Gate n → Prop
  | .ccx a b _ _ _ => a ≠ b
  | _ => True

/-- Repeated Toffoli controls reduce to CNOT, avoiding a three-distinct-wire premise. -/
def Gate.normalize {n : Nat} : Gate n → Gate n
  | .ccx a b t ha hb => if h : a = b then .cx a t ha else .ccx a b t ha hb
  | g => g

theorem Gate.normalize_valid {n : Nat} (g : Gate n) : g.normalize.normalized := by
  cases g with
  | x => trivial
  | cx => trivial
  | ccx a b t ha hb =>
    by_cases h : a = b <;> simp [Gate.normalize, h, Gate.normalized]

theorem Gate.normalize_correct {n : Nat} (g : Gate n) : g.normalize.eval = g.eval := by
  cases g with
  | x => rfl
  | cx => rfl
  | ccx a b t ha hb =>
    by_cases h : a = b
    · subst b
      funext s i
      simp [Gate.normalize, Gate.eval]
    · simp [Gate.normalize, h]

theorem normalizeCircuit_correct {n : Nat} (c : List (Gate n)) (s : Bits n) :
    run (c.map Gate.normalize) s = run c s := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    simp only [List.map_cons, run_cons, Gate.normalize_correct]
    exact ih _

end ShiReversible
