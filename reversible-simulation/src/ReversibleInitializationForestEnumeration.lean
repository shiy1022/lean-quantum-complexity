import ReversibleConfigurationEnumeration
import ReversibleConfigurationHeaderPayload
import ReversiblePaddedForestPayloadEnumeration

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Byte blocks of the established initializer, indexed by its actual configuration codec. -/
noncomputable def initializationForestBlocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) : List (List Bool) :=
  List.ofFn (fun i : Fin (configurationWidth tm capacity) =>
    initializationFormulaPayload ((initialFormulas tm e capacity n).bitFormula i)
      backward (n + 18 * i.val))

/-- Both emission directions use the same coordinate blocks; reverse emission also reverses their order. -/
theorem initializationForest_payload_blocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    ((if backward then (paddedForestCompile (fun i : Fin n => i.val) n 17
        (initialForest tm e capacity n)).reverse
      else paddedForestCompile (fun i : Fin n => i.val) n 17
        (initialForest tm e capacity n)).map (rawAssignmentPayload backward)).flatten =
      (if backward then (initializationForestBlocks tm e capacity n backward).reverse
       else initializationForestBlocks tm e capacity n backward).flatten := by
  have h := paddedForestPayload_ofFn (initialFormulas tm e capacity n).bitFormula
    (fun i : Fin n => i.val) n 17 backward (rawAssignmentPayload backward)
  cases backward <;>
    simpa [initialForest, initializationForestBlocks, initializationFormulaPayload,
      Nat.mul_comm] using h

end ShiReversibleGenerator
