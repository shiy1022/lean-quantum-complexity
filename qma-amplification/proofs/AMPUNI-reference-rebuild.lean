import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
Rebuild proof dependencies under fresh names, replacing reference stubs by
separately checked candidates. Every new declaration goes through `Lean.addDecl`
and the kernel. Original declarations and imported environments are unchanged.
The caller must audit the resulting theorem's axioms and original statement.
-/

namespace QMAReferenceRebuild
open Lean

structure State where
  replacements : Std.HashMap Name Name := {}
  rebuilt : Std.HashMap Name Name := {}
  visiting : Std.HashSet Name := {}
  count : Nat := 0

abbrev M := StateRefT State CoreM

private def rewriteConstants (e : Expr) (mapping : Std.HashMap Name Name) : Expr :=
  e.replace fun sub => match sub with
    | .const name levels => (mapping[name]?).map (fun name' => mkConst name' levels)
    | _ => none

partial def rebuild (name : Name) : M Name := do
  if let some result := (← get).rebuilt[name]? then return result
  if name == ``sorryAx then throwError "Unresolved reference placeholder"
  let axioms ← collectAxioms name
  if !axioms.contains ``sorryAx then return name
  if (← get).visiting.contains name then
    throwError "Cycle in reference reconstruction at {name}"
  modify fun s => { s with visiting := s.visiting.insert name }
  if let some replacement := (← get).replacements[name]? then
    let source ← getConstInfo name
    let target ← getConstInfo replacement
    unless source.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch replacing {name} by {replacement}"
    let result ← rebuild replacement
    modify fun s => { s with
      rebuilt := s.rebuilt.insert name result
      visiting := s.visiting.erase name }
    return result
  let env := (← getEnv).setExporting false
  let some info := env.find? name | throwError "Missing declaration {name}"
  let some value := info.value? (allowOpaque := true) |
    throwError "Unsupported axiom-bearing declaration {name}"
  for dep in info.type.getUsedConstants ++ value.getUsedConstants do
    discard <| rebuild dep
  let mapping := (← get).rebuilt
  let newName := Name.str `QMAReferenceRebuilt name.toString
  let newType := rewriteConstants info.type mapping
  let newValue := rewriteConstants value mapping
  let decl ← match info with
    | .thmInfo v => pure <| Declaration.thmDecl { v with name := newName, type := newType, value := newValue, all := [newName] }
    | .defnInfo v => pure <| Declaration.defnDecl { v with name := newName, type := newType, value := newValue, all := [newName] }
    | .opaqueInfo v => pure <| Declaration.opaqueDecl { v with name := newName, type := newType, value := newValue, all := [newName] }
    | _ => throwError "Unsupported declaration kind at {name}"
  addDecl decl
  modify fun s => { s with
    rebuilt := s.rebuilt.insert name newName
    visiting := s.visiting.erase name
    count := s.count + 1 }
  logInfo m!"REFERENCE_REBUILT {name}"
  return newName

/-- Recheck a dependency chain and expose its original theorem statement.
The final check accepts only Lean's three usual logical axioms. -/
def closeTheorem (original result : Name) (replacements : Array (Name × Name)) : CoreM Unit := do
  let info ← getConstInfo original
  let initial : State := { replacements := Std.HashMap.ofList replacements.toList }
  let (closed, state) ← (rebuild original).run initial
  addDecl <| .thmDecl {
    name := result
    levelParams := info.levelParams
    type := info.type
    value := mkConst closed (info.levelParams.map Level.param)
  }
  let axioms ← collectAxioms result
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected axiom in reconstructed theorem: {axiomName}"
  logInfo m!"REFERENCE_CLOSURE_CHECKED {result}; rebuilt {state.count} declarations; axioms {axioms}"

end QMAReferenceRebuild
