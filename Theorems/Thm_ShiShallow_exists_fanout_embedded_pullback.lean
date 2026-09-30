-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_fanout_embedded_pullback`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem exists_fanout_embedded_pullback (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g) :
    ∃ (c : Layered N) (u : Bits N → Bits N),
      (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
      ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
            = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
      ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 1 := by
  sorry

end ShiShallow
