import ReversibleInitializationForestLayers
import ReversibleInitializerSequenceExactLayers
import ReversibleRankedInitializerPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin

noncomputable def rankedInitializerItemLayerCount (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : Option tm.K → Nat
  | none => initializationHeaderLayerCount tm
  | some k => initializationStackLayerCount tm e capacity n k

set_option backward.isDefEq.respectTransparency false in
theorem rankedInitializerComponent_exact_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) (item : Option tm.K)
    (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    (rankedInitializerComponent tm e backward item).counters n cs ys (.inr 10) =
      cs (.inr 10) + rankedInitializerItemLayerCount tm e capacity n item := by
  cases item with
  | none =>
    change constantSequenceCounters 0 0 0 backward (initializationHeaderSchedule tm backward) cs (.inr 10) =
      cs (.inr 10) + initializationHeaderLayerCount tm
    exact configurationHeader_exact_layers tm backward cs
  | some k => exact packagedInitializationStack_exact_layers tm e capacity n k backward cs ys hn hcap

/-- Exact total elementary-layer count of the actual finite initializer in either direction. -/
theorem rankedInitializer_exact_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs ys (.inr 10) =
      cs (.inr 10) + initializationForestLayerCount tm e capacity n := by
  have hsum : ((rankedInitializerSchedule tm backward).map
      (rankedInitializerItemLayerCount tm e capacity n)).sum =
      initializationForestLayerCount tm e capacity n := by
    rw [initializationForestLayerCount_coordinates]
    cases backward <;>
      simp [rankedInitializerSchedule, initializationStackSchedule,
        rankedInitializerItemLayerCount, List.map_ofFn, Function.comp_def, Nat.add_comm]
  have h := initializerSequence_map_layers (rankedInitializerSchedule tm backward)
    (rankedInitializerComponent tm e backward) (rankedInitializerItemLayerCount tm e capacity n)
    n capacity (fun item _ cs' ys' hn' hcap' =>
      rankedInitializerComponent_exact_layers tm e capacity n backward item cs' ys' hn' hcap')
    cs ys hn hcap
  rw [hsum] at h
  simpa only [rankedInitializerComponents_map] using h

/-- The concrete prelude starts the layer counter at zero, so the final count is exactly the forest count. -/
theorem rankedInitializer_prelude_exact_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (time : Polynomial Nat) (backward : Bool) (n : Nat) (ys : List Bool) :
    initializerSequenceCounters (rankedInitializerComponents tm e backward) n
      (initializationPreludeCounters tm time n) ys (.inr 10) =
      initializationForestLayerCount tm e ((initializationCapacityPolynomial tm time).eval n) n := by
  have h := rankedInitializer_exact_layers tm e ((initializationCapacityPolynomial tm time).eval n) n
    backward (initializationPreludeCounters tm time n) ys
    (by simp [initializationPreludeCounters, resourceResult_raw])
    (by simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity])
  simpa [initializationPreludeCounters] using h

end ShiReversibleGenerator
