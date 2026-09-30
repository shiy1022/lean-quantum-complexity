import «AMPUNI-normalized-entry-valid-run»
import «AMPUNI-boolean-controller-valid-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop

-- Name equality instances at the component boundaries so synthesis does not
-- have to expand the entire nested controller label in one search.
local instance layoutLabelEq : DecidableEq ShiTMLayoutMachine.Label := inferInstance
local instance outerLabelEq : DecidableEq ShiTMOuterLift.OuterLabel := inferInstance
local instance topLabelEq : DecidableEq ShiTMRetainedTop.TopLabel := inferInstance
local instance pieceEntryLabelEq : DecidableEq ShiTMPieceEntry.EntryLabel := inferInstance
local instance payloadLabelEq : DecidableEq ShiTMRetainedPayload.Label := inferInstance
local instance copyStageLabelEq : DecidableEq ShiTMPayloadCopyStage.Label := inferInstance
local instance readoutCopyLabelEq : DecidableEq ShiTMReadoutCopy.Label := inferInstance
local instance readoutScratchLabelEq : DecidableEq ShiTMReadoutScratch.Label := inferInstance
local instance preparedLabelEq : DecidableEq ShiTMPreparedReadout.Label := inferInstance
local instance suffixLabelEq : DecidableEq ShiTMPayloadSuffix.Label := inferInstance
local instance firstLabelEq : DecidableEq ShiTMFirstPayload.Label := inferInstance
local instance prefixLabelEq : DecidableEq ShiTMGlobalFanoutPrefix.Label := inferInstance
local instance circuitLabelEq : DecidableEq ShiTMNormalizedCircuit.Label := inferInstance
local instance entryLabelEq : DecidableEq Label := inferInstance

noncomputable def booleanMachine : Turing.FinTM2 :=
  ShiTMBooleanWrapper.finiteMachine machine copyLabel finished

/-- The typed initial configuration agrees with the Boolean loader's result. -/
theorem typed_initial_eq (xs : List Bool) :
    (Turing.initList finiteMachine (xs.map bit) : Cfg TopGam Label Sig) =
      ⟨some copyLabel, none, ShiTMBooleanWrapper.initialTop xs⟩ := by
  dsimp only [Turing.initList, finiteMachine]
  congr 1
  funext k
  by_cases hk : k = source
  · subst k
    simp [ShiTMBooleanWrapper.initialTop, ShiTMBooleanWrapper.cellSource, source]
  · have hk' : k ≠ ShiTMBooleanWrapper.cellSource := hk
    simp [ShiTMBooleanWrapper.initialTop, hk, hk']

/-- On every valid verifier encoding, one fixed Boolean machine starts from
`initList`, emits the exact amplified encoding, and reaches canonical
`haltList`, with all work stacks drained. No polynomial runtime is claimed. -/
theorem boolean_valid_input_run (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ steps : Nat,
      (ShiTMBooleanWrapper.run machine copyLabel finished)^[steps]
        (some (Turing.initList booleanMachine
          (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n))) =
            some (Turing.haltList booleanMachine
              (ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n)) := by
  obtain ⟨S, v, bodySteps, hr, ho⟩ := init_to_amplified_encoding F n
  rw [typed_initial_eq] at hr
  obtain ⟨steps, _, hrun⟩ := ShiTMBooleanWrapper.valid_input_run
    machine copyLabel finished rfl
    (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
    (ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n)
    bodySteps v S hr ho
  exact ⟨steps, hrun⟩

/-- The same valid-input result in mathlib's actual timed-output interface.
The existential time has not yet been bounded by an input-length polynomial. -/
theorem boolean_valid_input_outputs (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ steps : Nat, Nonempty (Turing.TM2OutputsInTime booleanMachine
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
      (some (ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n)) steps) := by
  obtain ⟨steps, hr⟩ := boolean_valid_input_run F n
  exact ⟨steps, ⟨⟨⟨steps, hr⟩, Nat.le_refl _⟩⟩⟩

end ShiTMNormalizedEntry
