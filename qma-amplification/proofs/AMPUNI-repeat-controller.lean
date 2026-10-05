import «AMPUNI-repeat-header-copy»
import «AMPUNI-stack-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

inductive Phase where
  | toScratch | toInput | separator | copyHeader | clearHeader
  deriving DecidableEq

instance : Fintype Phase := Fintype.ofList
  [.toScratch, .toInput, .separator, .copyHeader, .clearHeader]
  (by intro p; cases p <;> simp)

abbrev Aux := Fin 4
abbrev Gam (G : K → Type) :=
  ShiTMStackFrame.Gam G (fun _ : Aux => Bool)
abbrev Label (L : Type) := Bool × (L ⊕ Phase)

def scratch : Aux := 0
def counter : Aux := 3
def header : Bool → Aux
  | false => 1
  | true => 2

def body (b : Bool) (l : L) : Label L := (b, .inl l)
def phase (b : Bool) (p : Phase) : Label L := (b, .inr p)

/-- The loop body has two alternating header banks. A Boolean-coded counter
is preloaded with one token for each round after the first. The source
machine's terminal program must be `.halt`; this controller replaces it by
the decision whether to run another round. -/
def machine (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input) :
    Label L → Stmt (Gam G) (Label L) (Option Bool × W)
  | (b, .inl l) =>
      if l = terminal then
        .pop (.inr counter) (fun v x => (x, v.2))
          (.branch (fun v => v.1.isSome)
            (.goto (fun _ => phase b .toScratch))
            (.goto (fun _ => phase b .clearHeader)))
      else
        ShiTMSubroutine.stmt (body b) (ShiTMStackFrame.stmt (M l))
  | (b, .inr .toScratch) =>
      ShiTMRepeatTransfer.move (.inl output) (.inr scratch)
        decodeOutput id (phase b .toScratch) (phase b .toInput)
  | (b, .inr .toInput) =>
      ShiTMRepeatTransfer.move (.inr scratch) (.inl input)
        id encodeInput (phase b .toInput) (phase b .separator)
  | (b, .inr .separator) =>
      .push (.inl input) (fun _ => encodeInput false)
        (.goto (fun _ => phase b .copyHeader))
  | (b, .inr .copyHeader) =>
      ShiTMRepeatTransfer.duplicate (.inr (header b)) (.inl input)
        (.inr (header (!b))) id encodeInput id
        (phase b .copyHeader) (body (!b) entry)
  | (b, .inr .clearHeader) =>
      .pop (.inr (header b)) (fun v x => (x, v.2))
        (.branch (fun v => v.1.isSome)
          (.goto (fun _ => phase b .clearHeader))
          .halt)

end ShiTMRepeatController
