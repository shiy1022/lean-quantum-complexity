-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.explicit_embedded_fanout_circuit`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_explicit_embedded_fanout_circuit`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

namespace ShiShallow

theorem explicit_embedded_fanout_circuit :
    (∀ (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g),
      ∃ (c : Layered N) (u : Bits N → Bits N),
        c = [(List.finRange n).map (fun j : Fin n =>
              Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j))
                (fun h => by
                  have hj : (j : ℕ) < n := j.isLt
                  have hv : (j : ℕ) = n + (j : ℕ) := congrArg Fin.val (hg h)
                  omega))]
        ∧ u = (fun (x : Bits N) (k : Fin N) =>
              if h : ∃ j : Fin n, g (Fin.natAdd n j) = k
                then xor (x k) (x (g (Fin.castAdd n h.choose))) else x k)
        ∧ (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
              = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
        ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1)
    ∧ (∃ (c : Layered 6) (u : Bits 6 → Bits 6),
        c = [[Instr.cnot (⟨1, by omega⟩ : Fin 6) ⟨3, by omega⟩ (by decide),
              Instr.cnot (⟨2, by omega⟩ : Fin 6) ⟨4, by omega⟩ (by decide)]]
        ∧ (∀ Φ : QState 6, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨3, by omega⟩ = true
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨4, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨0, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨5, by omega⟩ = true) := by
  sorry

end ShiShallow
