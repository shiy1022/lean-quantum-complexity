-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_polyTimeComputable_bridge_for_generic_pairing_decoders`. The real proof is on prove2.me.
import Definitions.Def_PvsNP
import Theorems.Thm_ShiTM_polyTimeComputable_of_machine_polybound

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem polyTimeComputable_bridge_for_generic_pairing_decoders :
    -- (1) THE BRIDGE, ∀-QUANTIFIED IN THE DECODERS and in the output constant `K`.  The ONLY
    -- property of the decoders it uses is the global budget on EVERY string; they are not
    -- required to invert anything.  This is the conjunct `COMPMACHe` (15) should have been.
    (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (K c : ℕ),
      (∀ w : List Bool, (unL w).length + (unR w).length ≤ w.length) →
      (∀ s x : List Bool, (gc s x).length ≤ K * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (2) the same at `COMPILE-STRd` (7)'s output constant 56
    ∧ (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (c : ℕ),
      (∀ w : List Bool, (unL w).length + (unR w).length ≤ w.length) →
      (∀ s x : List Bool, (gc s x).length ≤ 56 * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (3) THE BRIDGE FROM THE DEFINING EQUATIONS OF THE LENGTH-2 TAGGED DECODERS ALONE: the
    -- global budget is DERIVED, not assumed, so a consumer holding concrete decoders discharges
    -- eight `rfl`s and needs no hypothesis about well-formed inputs.
    ∧ (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (c : ℕ),
      unL [] = [] → (∀ b : Bool, unL [b] = []) →
      (∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t) →
      (∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = []) →
      unR [] = [] → (∀ b : Bool, unR [b] = []) →
      (∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t) →
      (∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t) →
      (∀ s x : List Bool, (gc s x).length ≤ 56 * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (4) the degree-one polynomials the bridge uses, named
    ∧ (∀ c : ℕ, ∃ p : Polynomial ℕ, ∀ n : ℕ, p.eval n = 57 * c * n + 57 * c)
    ∧ (∀ K c : ℕ, ∃ p : Polynomial ℕ,
        ∀ n : ℕ, p.eval n = (K + 1) * c * n + (K + 1) * c)
    -- (5) NON-VACUITY: decoders satisfying (3)'s eight equations exist, and the equations
    -- specify them on EVERY string -- including one outside the image of the pairing, where
    -- `COMPMACHe`'s existentially bound decoders are unconstrained.
    ∧ (∃ unL unR : List Bool → List Bool,
        (unL [] = []
          ∧ (∀ b : Bool, unL [b] = [])
          ∧ (∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t)
          ∧ (∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = []))
      ∧ (unR [] = []
          ∧ (∀ b : Bool, unR [b] = [])
          ∧ (∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t)
          ∧ (∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t))
      ∧ unL [false, true, true, false, false, true] = [true]
      ∧ unR [false, true, true, false, false, true] = [false]) := by
  sorry

end ShiBQP
