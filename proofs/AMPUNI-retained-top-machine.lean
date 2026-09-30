import «AMPUNI-nested-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMRetainedTop

open ShiTMLayoutMachine ShiTMOuterLift

/-- Four new stacks retain the input length and the three verifier header fields. -/
abbrev TopK := OuterK ⊕ Fin 4
abbrev TopGam : TopK → Type
  | .inl k => OuterGam k
  | .inr _ => Cell

inductive Header where
  | inputLength | witnessCount | ancillaCount | outputIndex
deriving DecidableEq

abbrev TopLabel := OuterLabel ⊕ Header

def headerStack : Header → Fin 4
  | .inputLength => 0
  | .witnessCount => 1
  | .ancillaCount => 2
  | .outputIndex => 3

def nextHeader : Header → TopLabel
  | .inputLength => .inr .witnessCount
  | .witnessCount => .inr .ancillaCount
  | .ancillaCount => .inr .outputIndex
  | .outputIndex => .inl (.inr .circuitHeader)

def topStacks (S : ∀ k, List (OuterGam k)) (H : Fin 4 → List Cell) :
    ∀ k, List (TopGam k)
  | .inl k => S k
  | .inr k => H k

def liftNestedStmt : Stmt OuterGam OuterLabel Sig → Stmt TopGam TopLabel Sig
  | .push k f q => .push (.inl k) f (liftNestedStmt q)
  | .peek k f q => .peek (.inl k) f (liftNestedStmt q)
  | .pop k f q => .pop (.inl k) f (liftNestedStmt q)
  | .load f q => .load f (liftNestedStmt q)
  | .branch f q₁ q₂ => .branch f (liftNestedStmt q₁) (liftNestedStmt q₂)
  | .goto f => .goto (fun v => .inl (f v))
  | .halt => .halt

/-- Read a terminated unary header, retaining one mark per true bit. A truncated field
halts immediately. The circuit bytes remain on the original input stack. -/
def scanRetainedHeader (h : Header) : Stmt TopGam TopLabel Sig :=
  .pop (.inl (.inl (11 : Fin 14))) pop
    (.branch isSome
      (.branch isMark
        (.push (.inr (headerStack h)) (cst .mark)
          (.goto (fun _ => .inr h)))
        (.goto (fun _ => nextHeader h)))
      .halt)

/-- A concrete retained-input entry phase followed by the existing nested circuit machine.
The later copy-reload and output-assembly phases will be attached at nested exit. -/
def topMachine : TopLabel → Stmt TopGam TopLabel Sig
  | .inl l => liftNestedStmt (nestedMachine l)
  | .inr h => scanRetainedHeader h

def topRun : Option (Cfg TopGam TopLabel Sig) → Option (Cfg TopGam TopLabel Sig) :=
  fun cf => cf.bind (step topMachine)

/-- One unary `true` bit transfers from the input stack to its retained field stack. -/
theorem header_mark_step (h : Header) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S (.inl (.inl (11 : Fin 14))) = .mark :: tail) :
    topRun^[1]
      (some { l := some (.inr h), var := v, stk := S }) =
        some { l := some (.inr h), var := some Cell.mark, stk := (Function.update (Function.update S (.inl (.inl (11 : Fin 14))) tail) (.inr (headerStack h)) (.mark :: S (.inr (headerStack h)))) } := by
  simp [topRun, topMachine, scanRetainedHeader, step, stepAux,
    hsrc, pop, isSome, isMark, cst]

/-- A unary terminator advances to the next field without changing any retained stack. -/
theorem header_delim_step (h : Header) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S (.inl (.inl (11 : Fin 14))) = .delim :: tail) :
    topRun^[1]
      (some { l := some (.inr h), var := v, stk := S }) =
        some { l := some (nextHeader h), var := some Cell.delim, stk :=
          Function.update S (.inl (.inl (11 : Fin 14))) tail } := by
  simp [topRun, topMachine, scanRetainedHeader, step, stepAux,
    hsrc, pop, isSome, isMark]

/-- A missing unary terminator halts rather than entering a header loop. -/
theorem header_empty_halts (h : Header) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inl (.inl (11 : Fin 14))) = []) :
    topRun^[1]
      (some { l := some (.inr h), var := v, stk := S }) =
        some { l := none, var := none, stk := S } := by
  simp [topRun, topMachine, scanRetainedHeader, step, stepAux,
    hsrc, pop, isSome]

end ShiTMRetainedTop
