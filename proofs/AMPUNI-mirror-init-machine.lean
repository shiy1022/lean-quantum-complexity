import «AMPUNI-piece-full-program»
import «AMPUNI-retained-finite»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Copy a completed width/base table to its reverse mirror, then restore the
source table from scratch. Stack 10 is temporary scratch; 8 and 9 receive the
mirror copies with `mirrorEnd` sentinels. -/
inductive Phase where
  | startWidth | copyWidth | restoreWidth
  | startBase | copyBase | restoreBase | done
deriving DecidableEq

instance : Fintype Phase :=
  Fintype.ofList
    [.startWidth, .copyWidth, .restoreWidth,
     .startBase, .copyBase, .restoreBase, .done]
    (by intro x; cases x <;> simp)

def machine : Phase → Stmt TopGam Phase Sig
  | .startWidth =>
      .push (.inl (.inl (8 : Fin 14))) (cst .mirrorEnd)
        (.goto (fun _ => .copyWidth))
  | .copyWidth =>
      .pop (.inl (.inl (1 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (8 : Fin 14))) get
            (.push (.inl (.inl (10 : Fin 14))) get
              (.goto (fun _ => .copyWidth))))
          (.goto (fun _ => .restoreWidth)))
  | .restoreWidth =>
      .pop (.inl (.inl (10 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (1 : Fin 14))) get
            (.goto (fun _ => .restoreWidth)))
          (.goto (fun _ => .startBase)))
  | .startBase =>
      .push (.inl (.inl (9 : Fin 14))) (cst .mirrorEnd)
        (.goto (fun _ => .copyBase))
  | .copyBase =>
      .pop (.inl (.inl (2 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (9 : Fin 14))) get
            (.push (.inl (.inl (10 : Fin 14))) get
              (.goto (fun _ => .copyBase))))
          (.goto (fun _ => .restoreBase)))
  | .restoreBase =>
      .pop (.inl (.inl (10 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (2 : Fin 14))) get
            (.goto (fun _ => .restoreBase)))
          (.goto (fun _ => .done)))
  | .done => .halt

def run : Option (Cfg TopGam Phase Sig) → Option (Cfg TopGam Phase Sig) :=
  fun cf => cf.bind (step machine)

end ShiTMMirrorInit
