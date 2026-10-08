import ReversibleConditionalPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem cleanupExit_injective (rs : List R) : Function.Injective (cleanupExit rs (L := L)) := by
  induction rs with
  | nil => exact fun _ _ h => h
  | cons r rs ih => exact fun _ _ h => ih (Sum.inr.inj h)

theorem GeneratorOperation.embed_injective (op : GeneratorOperation R) :
    Function.Injective (op.embed (L := L)) := by
  cases op <;> exact fun _ _ h => Sum.inr.inj (Sum.inr.inj h)

theorem operationExit_injective (ops : List (GeneratorOperation R)) :
    Function.Injective (operationExit ops (L := L)) := by
  induction ops with
  | nil => exact fun _ _ h => h
  | cons op ops ih => exact fun _ _ h => ih (op.embed_injective h)

theorem EmissionAtom.embed_injective (atom : EmissionAtom R) :
    Function.Injective (atom.embed (L := L)) := by
  cases atom with
  | literal bits => exact fun _ _ h => Sum.inr.inj h
  | natural r => exact fun _ _ h => Sum.inr.inj (Sum.inr.inj h)

theorem GeneratorAction.embed_injective (a : GeneratorAction R) :
    Function.Injective (a.embed (L := L)) := by
  cases a with
  | arithmetic op => exact op.embed_injective
  | emit atom => exact atom.embed_injective

theorem actionExit_injective (actions : List (GeneratorAction R)) :
    Function.Injective (actionExit actions (L := L)) := by
  induction actions with
  | nil => exact fun _ _ h => h
  | cons a actions ih => exact fun _ _ h => ih (a.embed_injective h)

theorem FixedNodeTemplate.embed_injective (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) :
    Function.Injective (t.embed r (L := L)) := by
  exact (cleanupExit_injective [r.p, r.q, r.r]).comp
    ((operationExit_injective (t.ops r)).comp (actionExit_injective (t.actions r)))

theorem fixedNodeExit_injective (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) :
    Function.Injective (fixedNodeExit r ts (L := L)) := by
  induction ts with
  | nil => exact fun _ _ h => h
  | cons t ts ih => exact fun _ _ h => ih (t.embed_injective r h)

theorem choicePrinterExit_injective (r : NodePrinterRegisters R)
    (yes no : List (FixedNodeTemplate R)) :
    Function.Injective (choicePrinterExit r yes no (L := L)) := by
  exact (fixedNodeExit_injective r yes).comp (fixedNodeExit_injective r no)

end ShiReversibleGenerator
