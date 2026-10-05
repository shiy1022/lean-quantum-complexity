import Definitions.Def_PvsNP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiTM_polyTimeComputable_of_machine_polybound

namespace BQPReferenceValidation.Source40
-- BRIDGE-1: from a machine-level step bound to the `PvsNP.PolyTimeComputable` certificate.
--
-- Interface note.  The alphabet identifications are taken as `Equiv`s
-- (`ea : tm.Γ tm.k₀ ≃ Bool`, `eb : tm.Γ tm.k₁ ≃ Bool`) rather than as type equalities
-- `tm.Γ tm.k₀ = Bool`.  Reason: `Turing.TM2ComputableAux` stores *exactly* these two
-- `Equiv`s, and the `outputsFun` field of `Turing.TM2ComputableInPolyTime` mentions
-- `inputAlphabet.invFun` / `outputAlphabet.invFun`.  With `Equiv` parameters the run
-- hypothesis is literally the field, so no transport is needed anywhere and the user
-- of the bridge may supply `Equiv.cast h0` when all they have is an equality `h0`
-- (see `shiBr2_ofEq` below).  Stating the hypothesis with equalities instead would
-- force `h0 ▸ ·` casts inside the list arguments of `TM2OutputsInTime`, which is a
-- type-valued dependent argument, and the resulting goals are not `rfl`-closable.

set_option autoImplicit false

open Turing

/-- **Bridge.**  If a bundled multi-stack machine `tm` has input and output stack alphabets
identified with `Bool`, and on every input string `s` it halts with output `f s` within
`p.eval s.length` steps, then `f` is polynomial-time computable in the sense of
`PvsNP.PolyTimeComputable` (Cook, Definition 3). -/
theorem _root_.BQPReferenceValidation.candidate40 (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (f : PvsNP.Str → PvsNP.Str) (p : Polynomial ℕ)
    (hrun : ∀ s : PvsNP.Str, Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun s) (Option.some (List.map eb.invFun (f s)))
      (p.eval s.length))) :
    PvsNP.PolyTimeComputable f :=
  ⟨{ tm := tm
     inputAlphabet := ea
     outputAlphabet := eb
     time := p
     outputsFun := fun a => (hrun a).some }⟩

/-- The equality-hypothesis form, derived from `BQPReferenceValidation.candidate40` by `Equiv.cast`.  Kept `private`
(it does not occur in the type of `BQPReferenceValidation.candidate40`). -/
private theorem shiBr2_ofEq (tm : Turing.FinTM2) (h0 : tm.Γ tm.k₀ = Bool)
    (h1 : tm.Γ tm.k₁ = Bool) (f : PvsNP.Str → PvsNP.Str) (p : Polynomial ℕ)
    (hrun : ∀ s : PvsNP.Str, Nonempty (Turing.TM2OutputsInTime tm
      (List.map (Equiv.cast h0).invFun s)
      (Option.some (List.map (Equiv.cast h1).invFun (f s)))
      (p.eval s.length))) :
    PvsNP.PolyTimeComputable f :=
  BQPReferenceValidation.candidate40 tm (Equiv.cast h0) (Equiv.cast h1) f p hrun

/-- **Satisfiability check (rule 3).**  Instantiating the bridge at Mathlib's
`Turing.idComputer Bool` (whose stack alphabets *are* `Bool`, so both identifications are
`Equiv.cast rfl`), with `f := id` and `p := 1`, reproduces `PolyTimeComputable id`.
The run hypothesis is supplied by the `outputsFun` field of Mathlib's own
`Turing.idComputableInPolyTime`, wrapped in `Nonempty` (rule 1: `TM2OutputsInTime` is
type-valued). -/
private theorem shiBr2_idCheck : PvsNP.PolyTimeComputable (id : PvsNP.Str → PvsNP.Str) :=
  BQPReferenceValidation.candidate40 (Turing.idComputer Bool) (Equiv.cast rfl) (Equiv.cast rfl) id 1
    (fun s => ⟨(Turing.idComputableInPolyTime (id : PvsNP.Str → List Bool)).outputsFun s⟩)

end BQPReferenceValidation.Source40

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate40
    let target ← getConstInfo ``ShiTM.polyTimeComputable_of_machine_polybound
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.polyTimeComputable_of_machine_polybound"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.polyTimeComputable_of_machine_polybound"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.polyTimeComputable_of_machine_polybound"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate40
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.polyTimeComputable_of_machine_polybound; axioms {axioms}"
