import ReversibleInitializerComponentPackages
import ReversibleConstantStackSchema
import ReversibleInitializationSymbolOrder

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

set_option backward.isDefEq.respectTransparency false in
/-- The configuration header is the checked fixed finite sequence, with a designated halt. -/
noncomputable def packagedConfigurationHeader (tm : Turing.FinTM2) (backward : Bool) : InitializationComponent := by
  classical
  let ars := initializationHeaderSchedule tm backward
  refine {
    Labels := ConstantSequenceLabels 0 0 0 backward ars (Fin 1)
    finiteLabels := inferInstance
    decideLabels := inferInstance
    code := configurationHeaderCode tm backward (fun _ : Fin 1 => .halt) 0
    entry := constantSequenceEntry 0 0 0 backward ars (0 : Fin 1)
    exit := constantSequenceExit 0 0 0 backward ars (0 : Fin 1)
    exit_halt := ?_
    steps := fun _ cs _ => constantSequenceSteps 0 0 0 backward ars cs
    counters := fun _ cs _ => constantSequenceCounters 0 0 0 backward ars cs
    output := fun _ cs ys => configurationHeaderPayload tm backward (cs (.inl 0)) ++ ys
    metadata := fun _ cs _ r => constantSequenceCounters_metadata 0 0 0 backward ars cs r
    run := ?_ }
  · change constantSequenceCode 0 0 0 backward ars (fun _ : Fin 1 => .halt) 0
      (constantSequenceExit 0 0 0 backward ars (0 : Fin 1)) = .halt
    rw [constantSequenceCode_embed]
    rfl
  · intro n cs ys hn hb ht
    exact configurationHeader_run tm backward (fun _ : Fin 1 => .halt) 0 cs hb ht ys

/-- Each fixed machine stack selects the actual input or constant program, in the required cell direction. -/
noncomputable def packagedInitializationStack (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (k : tm.K) : InitializationComponent := by
  classical
  let header := Fintype.card (Option tm.Λ) + Fintype.card tm.σ
  let rank := ((Fintype.equivFin tm.K) k).val
  let card := Fintype.card (Option (MachineSymbol tm))
  exact if k = tm.k₀ then
    if backward then packagedAscendingInputComponent header rank card tm e backward (initializationSymbolSchedule tm backward)
    else packagedInputComponent header rank card tm e backward (initializationSymbolSchedule tm backward)
  else
    if backward then packagedAscendingConstantComponent header rank card backward (initializationConstantSchedule tm backward)
    else packagedConstantComponent header rank card backward (initializationConstantSchedule tm backward)

/-- The schedule is fixed by the finite machine, independently of runtime input length and capacity. -/
noncomputable def initializationStackSchedule (tm : Turing.FinTM2) (backward : Bool) : List tm.K :=
  let ranks := List.ofFn (fun j : Fin (Fintype.card tm.K) => (Fintype.equivFin tm.K).symm j)
  if backward then ranks else ranks.reverse

/-- Forward emission executes decreasing stack ranks before the header; reverse emission reverses that order. -/
noncomputable def rankedInitializerComponents (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) : List InitializationComponent :=
  let stackComponents := (initializationStackSchedule tm backward).map (packagedInitializationStack tm e backward)
  if backward then packagedConfigurationHeader tm backward :: stackComponents
  else stackComponents ++ [packagedConfigurationHeader tm backward]

noncomputable def rankedInitializerCode (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) :=
  initializerSequenceCode (rankedInitializerComponents tm e backward)

/-- Actual all-stack instruction execution with every connecting branch in its count. -/
theorem rankedInitializer_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) :
    CounterRun (rankedInitializerCode tm e backward)
      ⟨some (initializerSequenceEntry (rankedInitializerComponents tm e backward)), cs, ys⟩
      (initializerSequenceSteps (rankedInitializerComponents tm e backward) n cs ys)
      ⟨some (initializerSequenceExit (rankedInitializerComponents tm e backward)),
        initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs ys,
        initializerSequenceOutput (rankedInitializerComponents tm e backward) n cs ys⟩ :=
  initializerSequence_run (rankedInitializerComponents tm e backward) n cs ys hn hb ht

theorem rankedInitializer_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs ys (.inl r) = cs (.inl r) :=
  initializerSequence_metadata (rankedInitializerComponents tm e backward) n cs ys r

theorem rankedInitializer_exit (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) :
    rankedInitializerCode tm e backward (initializerSequenceExit (rankedInitializerComponents tm e backward)) = .halt :=
  initializerSequence_exit (rankedInitializerComponents tm e backward)

end ShiReversibleGenerator
