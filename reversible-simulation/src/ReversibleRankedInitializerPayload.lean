import ReversibleRankedStackPayload
import ReversibleInitializerSequencePayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin

noncomputable def rankedInitializerSchedule (tm : Turing.FinTM2) (backward : Bool) : List (Option tm.K) :=
  let stackItems := (initializationStackSchedule tm backward).map some
  if backward then none :: stackItems else stackItems ++ [none]

noncomputable def rankedInitializerComponent (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) :
    Option tm.K → InitializationComponent
  | none => packagedConfigurationHeader tm backward
  | some k => packagedInitializationStack tm e backward k

noncomputable def rankedInitializerPayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity n : Nat) : List Bool :=
  (rankedInitializerSchedule tm backward).reverse.flatMap (fun item => match item with
    | none => configurationHeaderPayload tm backward n
    | some k => rankedStackPayload tm e backward capacity n k)

theorem rankedInitializerComponents_map (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) :
    rankedInitializerComponents tm e backward =
      (rankedInitializerSchedule tm backward).map (rankedInitializerComponent tm e backward) := by
  cases backward <;>
    simp [rankedInitializerComponents, rankedInitializerSchedule, rankedInitializerComponent, List.map_map]

/-- Exact complete payload of the actual all-stack/header program, in both directions. -/
theorem rankedInitializer_output (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (capacity n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceOutput (rankedInitializerComponents tm e backward) n cs ys =
      rankedInitializerPayload tm e backward capacity n ++ ys := by
  rw [rankedInitializerComponents_map]
  apply initializerSequence_map_payload _ _ _ n capacity _ cs ys hn hcap
  intro item hi cs' ys' hn' hcap'
  cases item with
  | none => exact packagedConfigurationHeader_output tm backward n cs' ys' hn'
  | some k => exact packagedInitializationStack_output tm e backward capacity n k cs' ys' hcap'

end ShiReversibleGenerator
