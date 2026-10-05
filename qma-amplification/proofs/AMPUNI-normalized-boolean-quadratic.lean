import «AMPUNI-normalized-entry-charged»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMStackGrowth ShiTMRetainedPayload
open ShiTMPayloadSuffix (reserve)

-- Reuse the exact computable equality instance captured by booleanMachine.
local instance quadraticEntryLabelEq : DecidableEq Label := entryLabelEq

/-- One fixed Boolean machine computes every valid amplified encoding within
one uniform quadratic bound, including loading, output, and canonical cleanup.
This does not yet assert totality on malformed inputs. -/
theorem boolean_valid_input_quadratic :
    ∃ K : Nat, ∀ (F : ShiClassQMA.QMAFamily) (n : Nat),
      Nonempty (Turing.TM2OutputsInTime booleanMachine
        (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
        (some (ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n))
        (K*(inputLength F n+1)^2)) := by
  obtain ⟨kb, body⟩ := init_to_amplified_encoding_charged
  obtain ⟨growth, hg⟩ := finite_growth machine
  refine ⟨(2*growth+1)*kb+32, ?_⟩
  intro F n
  obtain ⟨S, v, steps, hr, ho, hb⟩ := body F n
  rw [typed_initial_eq] at hr
  obtain ⟨⟨execution, ht⟩⟩ := ShiTMBooleanWrapper.valid_input_outputs_bound
    machine copyLabel finished rfl growth hg
    (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
    (ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n)
    steps v S hr ho
  have hs : steps ≤ kb*reserve F n := by omega
  have hm := Nat.mul_le_mul_left (2*growth+1) hs
  have hL : inputLength F n ≤ reserve F n := by dsimp [reserve]; nlinarith
  have h1 : 1 ≤ reserve F n := by dsimp [reserve]; nlinarith
  refine ⟨⟨execution, ht.trans ?_⟩⟩
  change (2*growth+1)*steps+4*inputLength F n+28 ≤ _
  change _ ≤ ((2*growth+1)*kb+32)*reserve F n
  nlinarith

end ShiTMNormalizedEntry
