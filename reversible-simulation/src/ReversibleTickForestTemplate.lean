import ReversibleTickStackListPayload
import ReversibleTickStackListLayerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Header coordinates follow the existing label, then memory codec order. -/
noncomputable def tickHeaderKinds (tm : Turing.FinTM2) : List (TickTreeKind tm) :=
  List.ofFn (fun i : Fin (Fintype.card (Option tm.Λ)) => .inl (.inl ((Fintype.equivFin (Option tm.Λ)).symm i))) ++
  List.ofFn (fun i : Fin (Fintype.card tm.σ) => .inl (.inr ((Fintype.equivFin tm.σ).symm i)))

noncomputable def tickStackOrder (tm : Turing.FinTM2) : List tm.K :=
  List.ofFn (Fintype.equivFin tm.K).symm

/-- Header emission explicitly clears the unused position counter before dispatch. -/
noncomputable def tickHeaderTemplate (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :=
  sequenceProgramTemplate (cleanupProgramTemplate [.inl 2])
    (tickCoordinateListTemplate tm (if backward then tickHeaderKinds tm else (tickHeaderKinds tm).reverse)
      inputStride strideBound backward)

/-- A finite complete tick-forest program, with execution order accounting for prepended output. -/
noncomputable def tickForestTemplate (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :=
  let header := tickHeaderTemplate tm inputStride strideBound backward
  let cells := tickStackListTemplate tm (if backward then tickStackOrder tm else (tickStackOrder tm).reverse)
    inputStride strideBound backward
  if backward then sequenceProgramTemplate header cells else sequenceProgramTemplate cells header

theorem tickHeaderTemplate_embeds (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :
    (tickHeaderTemplate tm inputStride strideBound backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds _)
    (tickCoordinateListTemplate_embeds tm _ inputStride strideBound backward)

theorem tickHeaderTemplate_run (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :
    (tickHeaderTemplate tm inputStride strideBound backward).Runs :=
  sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds _) (cleanupProgramTemplate_run _)
    (tickCoordinateListTemplate_run tm _ inputStride strideBound backward)

theorem tickForestTemplate_embeds (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :
    (tickForestTemplate tm inputStride strideBound backward).Embeds := by
  unfold tickForestTemplate
  split <;> apply sequenceProgramTemplate_embeds
  all_goals first
    | exact tickHeaderTemplate_embeds tm inputStride strideBound backward
    | exact tickStackListTemplate_embeds tm _ inputStride strideBound backward

theorem tickForestTemplate_run (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool) :
    (tickForestTemplate tm inputStride strideBound backward).Runs := by
  unfold tickForestTemplate
  split <;> apply sequenceProgramTemplate_run
  all_goals first
    | exact tickHeaderTemplate_embeds tm inputStride strideBound backward
    | exact tickHeaderTemplate_run tm inputStride strideBound backward
    | exact tickStackListTemplate_embeds tm _ inputStride strideBound backward
    | exact tickStackListTemplate_run tm _ inputStride strideBound backward

end ShiReversibleGenerator
