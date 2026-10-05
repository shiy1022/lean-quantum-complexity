-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_circuit_amplitude_is_a_path_sum_over_hadamard_branches`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

namespace ShiShallow

theorem circuit_amplitude_is_a_path_sum_over_hadamard_branches :
    ∃ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (A : ∀ m : ℕ, (Instr m → Bits m → ℂ) → (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → ℂ)
      (P : ∀ m : ℕ, (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → Bits m),
      -- `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0)
    ∧ (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1)
    ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs)
      -- `A` and `P` are explicit recursions over the gate list
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (y : Bits m) (bits : List Bool), A m coef perm [] y bits = 1)
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (y : Bits m) (bits : List Bool),
          P m perm [] y bits = y)
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          A m coef perm (Instr.h i :: gs) y bits
            = A m coef perm gs y bits.tail
                * hMat (P m perm gs y bits.tail i) (bits.headD false))
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          P m perm (Instr.h i :: gs) y bits
            = Function.update (P m perm gs y bits.tail) i (bits.headD false))
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          A m coef perm (g :: gs) y bits
            = A m coef perm gs y bits * coef g (P m perm gs y bits))
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          P m perm (g :: gs) y bits = perm g (P m perm gs y bits))
      -- the path decomposition for a flat gate list
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) →
          ∀ (gs : List (Instr m)) (ψ : QState m) (y : Bits m),
            (gs.foldl (fun st g => Instr.apply g st) ψ) y
              = ∑ b : Fin (N m gs) → Bool,
                  A m coef perm gs y (List.ofFn b) * ψ (P m perm gs y (List.ofFn b)))
      -- the same for a one-gate-per-layer `runLayered` circuit
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) →
          ∀ (gs : List (Instr m)) (ψ : QState m) (y : Bits m),
            runLayered (gs.map (fun g => [g])) ψ y
              = ∑ b : Fin (N m gs) → Bool,
                  A m coef perm gs y (List.ofFn b) * ψ (P m perm gs y (List.ofFn b)))
      -- every branch amplitude is `(√2)⁻¹ ^ h` times a power of `ω = exp (iπ/4)`
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ x : Bits m,
              ∃ k : ℕ, coef g x = Complex.exp (Complex.I * Real.pi / 4) ^ k) →
          ∀ (gs : List (Instr m)) (y : Bits m),
            ∃ e : (Fin (N m gs) → Bool) → ℕ, ∀ b : Fin (N m gs) → Bool,
              A m coef perm gs y (List.ofFn b)
                = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (N m gs)
                    * Complex.exp (Complex.I * Real.pi / 4) ^ (e b))
      -- non-vacuity: two Hadamards and one non-Hadamard gate on two wires, four branches,
      -- the fold and the path sum computed independently
    ∧ N 2 [Instr.h 0, Instr.x 1, Instr.h 0] = 2
    ∧ (([Instr.h 0, Instr.x 1, Instr.h 0] : List (Instr 2)).foldl
          (fun st g => Instr.apply g st)
          (fun x => (if x 0 then (2 : ℂ) else 1) * (if x 1 then 3 else 5)))
          (fun _ => false) = 3
    ∧ (∑ b : Fin 2 → Bool,
          A 2 (fun _ _ => 1) (fun _ x => Function.update x 1 (!(x 1)))
              [Instr.h 0, Instr.x 1, Instr.h 0] (fun _ => false) (List.ofFn b)
            * (fun x : Bits 2 => (if x 0 then (2 : ℂ) else 1) * (if x 1 then 3 else 5))
                (P 2 (fun _ x => Function.update x 1 (!(x 1)))
                  [Instr.h 0, Instr.x 1, Instr.h 0] (fun _ => false) (List.ofFn b))) = 3
    ∧ (∀ (ψ : QState 2) (x : Bits 2),
          Instr.apply (Instr.x 1) ψ x = 1 * ψ (Function.update x 1 (!(x 1))))
      -- BRANCH-1's per-gate existential supplies the `coef`/`perm` data used above
    ∧ (∀ m : ℕ,
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) →
              ∃ coef : Bits m → ℂ, ∃ perm : Bits m → Bits m,
                ∀ ψ : QState m, Instr.apply g ψ = fun x => coef x * ψ (perm x)) →
          ∃ (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            ∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) := by
  sorry

end ShiShallow
