import «AMPUNI-total-clocked-bounds»
import «AMPUNI-total-function»
import «AMPUNI-normalized-boolean-quadratic»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
noncomputable section
namespace ShiTMNormalizedEntry
open ShiTMRetainedPayload
local instance transducerEntryLabelEq : DecidableEq Label := entryLabelEq

/-- One total polynomial-time function transforms every retained valid
verifier encoding into its exact amplified encoding. Malformed inputs also
terminate; no claim about their output content is required. -/
theorem retained_encoding_transducer :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (F : ShiClassQMA.QMAFamily) (n : Nat),
        g (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n) =
          ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n := by
  obtain ⟨k, hk⟩ := boolean_valid_input_quadratic
  let ein : Bool ≃ booleanMachine.Γ booleanMachine.k₀ := Equiv.refl Bool
  let full := ShiTMTotalClocked.finiteMachine booleanMachine ein k
  obtain ⟨C, hC⟩ := ShiTMTotalClocked.total_quadratic booleanMachine ein k
  have hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (Turing.TM2OutputsInTime full (xs.map (Equiv.refl Bool).symm)
        (some (ys.map (Equiv.refl Bool).symm)) (C*(xs.length+1)^2)) := by
    intro xs
    obtain ⟨ys, hy⟩ := hC xs
    have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
    have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
    have heq := congrArg₂ (fun (a b : List Bool) =>
      Nonempty (Turing.TM2OutputsInTime full a (some b) (C*(xs.length+1)^2))) hin hout
    exact ⟨ys, heq.mpr hy⟩
  obtain ⟨g, hg, hunique⟩ := ShiTMTotalFunction.function_of_total full
    (Equiv.refl Bool) (Equiv.refl Bool) C hall
  obtain ⟨D, hD⟩ := ShiTMTotalClocked.valid_quadratic booleanMachine ein k
  refine ⟨g, hg, ?_⟩
  intro F n
  let xs := ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n
  let ys := ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n
  have hv : Nonempty (Turing.TM2OutputsInTime booleanMachine (xs.map ein) (some ys)
      (k*(xs.length+1)^2)) := by
    have hin : xs.map ein = xs := List.map_id xs
    have heq := congrArg (fun a : List Bool =>
      Nonempty (Turing.TM2OutputsInTime booleanMachine a (some ys) (k*(xs.length+1)^2))) hin
    exact heq.mpr (hk F n)
  have hf := hD xs ys hv
  apply hunique xs ys (D*(xs.length+1)^2)
  have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
  have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
  have heq := congrArg₂ (fun (a b : List Bool) =>
    Nonempty (Turing.TM2OutputsInTime full a (some b) (D*(xs.length+1)^2))) hin hout
  exact heq.mpr hf

/-- The concrete transformer discharges the retained-encoding premise of
the one-round uniform QMA amplification theorem. -/
theorem retained_htrans : ∀ F : ShiClassQMA.QMAFamily,
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧ ∀ n : Nat,
      g (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n) =
        ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n := by
  obtain ⟨g, hg, hmap⟩ := retained_encoding_transducer
  intro F
  exact ⟨g, hg, hmap F⟩

end ShiTMNormalizedEntry
