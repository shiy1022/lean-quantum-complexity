import ReversibleFormulaInputEnumeration

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

theorem Formula.intern_rawCompile (p : Formula ι) (inputs : ι → Nat) (base : Nat) :
    p.intern.rawCompile (fun i => inputs p.inputList[i.val]) base = p.rawCompile inputs base := by
  simpa only [Formula.rename_rawCompile] using
    congrArg (fun q => q.rawCompile inputs base) p.intern_rename

end ShiReversibleFormula

namespace ShiReversibleGenerator
open ShiReversibleFormula

theorem symbolicFormulaCompile_intern {R ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) :
    symbolicFormulaCompile (fun i => inputs p.inputList[i.val]) base offset p.intern =
      symbolicFormulaCompile inputs base offset p := by
  simpa only [symbolicFormulaCompile_rename] using
    congrArg (fun q => symbolicFormulaCompile inputs base offset q) p.intern_rename

end ShiReversibleGenerator
