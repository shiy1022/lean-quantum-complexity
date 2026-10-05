import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch

namespace BQPReferenceValidation.Source28
/-
MACH-A5.  THE DESIGN-R HOST MACHINE: ONE CONCRETE `Turing.FinTM2` WHOSE PHASE ORDER IS THE
COMPILED WORD'S ORDER, WITH **TWO** GATE-RENDERING LOOPS -- A MIRRORED FORWARD ONE EMITTING
STRAIGHT TO THE OPCODE PORT AND A NORMAL ADJOINT ONE EMITTING INTO THE HOLD AND THEN
TRANSFERRED -- AND A SINGLE GLOBAL REVERSAL AT THE END.

WHY THE PREDECESSOR COULD NOT WORK.  `MACH-A3c` had ONE rendering loop and a group-wise
reversal (`GREV`) that reverses unary FIELDS, not records, so the adjoint slot of the target
word was never rendered; and it emitted the two input sweeps ADJACENTLY with the output-wire
marker in the wrong phase, which no instantiation of the uninterpreted sweep functions can
move.  Both faults are structural, and the target word cannot be restated to match: the
head-safety analyser rejects any reversed block, so the phase order of the compiled program
is not a free choice.

THE FACT THAT FIXES IT.  Every emitter PREPENDS to the opcode port and the nibble expander
carries the port's LIST ORDER forward to the output wire.  So the output word is the REVERSE
of the emission sequence.  Emitting in word order and reversing the whole port ONCE at the
end therefore makes time order equal word order, and the two accepted stack-order
conventions -- the emitters' "block forward at the head" and the sweeps' "reversed" -- become
the SAME convention rather than contradictory ones.

THE FORCED ASYMMETRY.  A loop that prepends per record contributes `Y(r_n) ++ ... ++ Y(r_1)`
to the port; a loop that buffers per record and is then transferred by ONE reversing copy
contributes `Z(r_1).reverse ++ ... ++ Z(r_n).reverse`.  The target needs
`blk(r_1) ++ ... ++ blk(r_n)` at one place and `blkA(r_n) ++ ... ++ blkA(r_1)` at another, and
on the reversed port those read as `blk(r_n).rev ++ ... ++ blk(r_1).rev` and
`blkA(r_1).rev ++ ... ++ blkA(r_n).rev`.  Matching admits EXACTLY ONE assignment: the FORWARD
slot is the prepending loop with MIRRORED symbols (its per-record stack shape is
`blk(r).reverse`), and the ADJOINT slot is the buffered loop with NORMAL symbols (its
per-record stack shape is `blkA(r)`).  The asymmetry is not a stylistic choice.

THREE THINGS THAT COST NOTHING BECAUSE THE BLOCKS ARE ALL FORALL-QUANTIFIED.
(i)  MIRRORED ONE-INDEX BLOCKS: the one-index emitter is instantiated with its two wrapper
     nibbles swapped -- the index loop pushes the `1` nibble and the scratch drain the `0`
     nibble -- so its stack shape is the reverse of the forward block.  Not one line of the
     block theorem changes.
(ii) MIRRORED CNOT: the reverse of an `i < j` block has exactly the `j < i` block's shape with
     the two tag nibbles exchanged, and vice versa.  So the forward loop routes the `i < j`
     exit through the orientation bit the ADJOINT loop uses for `j < i`, exchanges the two tag
     nibbles, and -- a step this machine's design brief omitted -- ALSO exchanges the two
     wrapper nibbles, exactly as in (i).  Without that last exchange the mirrored CNOT block
     would carry `1`s where the reversed block carries `0`s.  The diagonal guard preserves the
     orientation bit, so routing the other bit through it is sound.
(iii) THE OPCODE AND REPEAT REGISTERS ARE SOURCED FROM THE WIRING, WITH NO `Stmt` CHANGE.  The
     predecessor pushed the TAG as the opcode and never initialised the repeat field, so its
     one-index emitter could only ever emit ONE nibble and never the right one.  Here only the
     REGISTER FUNCTIONS change: the opcode push reads the tag through the opcode table
     (`0,1,2,3 -> 2,4,3,5`), and the tag reader's terminator pop LOADS the repeat field from
     the tag.  THE COUNT IS THE NUMBER OF COPIES, NOT THE NUMBER OF EXTRA COPIES: the
     one-index emitter's hypothesis is `cnt v = r + 1` and it emits `r + 1` nibbles, so the
     register must hold `rp t + 1`.  That is ONE at every tag for the forward loop and
     `1,3,7,1` at tags `0,1,2,3` for the adjoint loop, which is what turns the adjoint `T`
     gate into seven `3`s and the adjoint `S` gate into three `4`s.  The predecessor stored
     `rp t` itself -- `0` forward and `0,2,6,0` adjoint -- and `r + 1 = 0` has NO BQPReferenceValidation.candidate28, so
     the forward emitter could never be entered at all and the adjoint one was short by a
     copy at every repeating tag.  No label, no `Stmt` and no block re-proof.

FOUR FURTHER REPAIRS CARRIED HERE.
* `lV0`, a scratch-port drain between the tokeniser and the duplicator.  The tokeniser's
  rollback trail is NOT emptied on the accepting path -- it carries one mark per copied symbol
  plus one boundary per record -- and every gate-loop hypothesis needs that port empty.  The
  tokeniser's exit is a BOUND PARAMETER of its block theorem, so re-pointing it costs no
  re-proof.  Pairing the drain into the tokeniser's own last label would be UNSOUND: the trail
  is longer than the hold by exactly the record count.
* THE TWO ZERO RUNS ARE HOSTED.  The target has two `0`-runs of the padded length and the
  predecessor emitted neither.  The header parser prepares only TWO padded copies and FOUR are
  needed, so the generic duplicator is instantiated THREE times: once on the token stream (for
  the two gate loops) and twice on the padded input -- each of those yielding both a sweep tape
  and a zero-run counter.
* ONE sweep instantiation, not two, and NO dead labels.  The accepted sweep block states the
  `L` sweep and the `E` sweep over a SINGLE tape stack, so hosting them on two different tape
  stacks forced the predecessor to carry a second, unreachable copy of each group -- nine dead
  labels that inflate every `decide`.  Here BOTH sweeps read the SAME tape port, which the late
  duplicator reloads between them, so one instantiation serves and the nine labels are gone.
* `GREV` IS DISCARDED, labels and all.
Fourteen stacks exactly: a fifteenth would break the drain's `Nodup`, its index bijection, its
`i < 13` bound and the composed step count.

TWO REPAIRS CARRIED BY THIS REVISION (`MACH-A5d`), BOTH IN THE `lSD` SHAPE.
* `lFD`, A FUEL DRAIN, spliced as `lSD -> lFD -> lV1`.  `kfu` was NEVER emptied on the
  ROLLBACK path: the tokeniser's accepting exit (`lU` at an exhausted `kfu`) leaves the port
  empty, but the rollback exit (`lTg`/`lJ1`/`lJ2` -> `lCl` -> `lFin`) leaves
  `ng - |recs| - 1` units on it, and `lZa`/`lZb` push one `0` onto the opcode port per unit
  popped, so the leading zero run was too long by exactly that leftover whenever it was
  positive.  The drain costs ONE step on the accepting path, where `kfu` is already empty.
  The drain's shape is the accepted single-stack drain's, generic in the stack AND in both
  labels, so no run theorem changes.
* `lSKT`/`lSKTz`, A TAG SKIP ARM per gate loop, reached by a THREE-WAY dispatch.  The tag
  accumulator saturates at seven and never wraps, so `= 4` holds exactly at the true tag
  four and `5 <= .` is exactly "four or more, and not four".  Records at those tags render
  as the EMPTY block, and the one-index emitter cannot express an empty block: it emits
  `1^i` then the opcode then `0^i`, of length `2i+1`, and its copy count is `r+1 >= 1`.  So
  such a record must not reach the emitter at all; the skip arm consumes its one index
  field and pushes nothing, exactly as the existing diagonal guard `lP4 -> lSK` does for the
  two-index record at equal indices.  The `= 4` arm is untouched, so the diagonal case still
  routes `lP2 -> lP4 -> lSK -> lGT` without touching the opcode port.
  CONSEQUENCE, STATED AS A CONJUNCT IN (10) AND (12): the dispatch is now TOTAL into three
  arms, so no well-formedness side condition on the tag is needed by any caller.

WHAT THIS SLICE DOES **NOT** CLAIM.  It is the machine datum, the per-block agreement lemmas
and the seam pack only.  No run theorem for any phase is claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

/-! ### 1.  The fourteen stacks and the two alphabets -/

private inductive Stk : Type
  | kin | ksrc | kxin | khld | kpd1 | kpd2 | kqc | kfu | ktok | kidx | kopc | kbit
  | kscA | kscB
  deriving DecidableEq

private instance : Fintype Stk where
  elems := ⟨[Stk.kin, Stk.ksrc, Stk.kxin, Stk.khld, Stk.kpd1, Stk.kpd2, Stk.kqc,
    Stk.kfu, Stk.ktok, Stk.kidx, Stk.kopc, Stk.kbit, Stk.kscA, Stk.kscB], by decide⟩
  complete := fun x => by cases x <;> decide

@[reducible] private def Gam : Stk → Type
  | Stk.khld => Fin 16
  | Stk.kopc => Fin 16
  | _ => Bool

private instance : Fintype (Gam Stk.kin) := (inferInstance : Fintype Bool)

/-! ### 2.  The register and every register function the blocks name -/

private abbrev Reg : Type := Option Bool × Option (Fin 16) × Fin 8 × Fin 8 × Bool × Bool

private abbrev r0 : Reg := (Option.none, Option.none, 0, 0, false, false)

private def obt (o : Option Bool) : Option (Fin 16) := o.map (fun b => if b then 1 else 0)

private def capI (c : Fin 8) : Fin 8 := if h : c.val < 5 then ⟨c.val + 1, by omega⟩ else c

private def capT (c : Fin 8) : Fin 8 := if h : c.val < 7 then ⟨c.val + 1, by omega⟩ else c

private def decf (c : Fin 8) : Fin 8 := ⟨c.val - 1, by omega⟩

-- THE OPCODE TABLE and THE TWO REPEAT TABLES.  These three functions are the whole of
-- repair (iii): the tag is no longer pushed as the opcode, and the repeat field is no
-- longer left at its initial zero by accident -- it is LOADED from the tag.  The two
-- repeat tables hold the COPY COUNT, i.e. the renderer's `rp t` PLUS ONE, because the
-- emitter's hypothesis is `cnt v = r + 1` and it emits `r + 1` copies.
private def ocF (t : Fin 8) : Fin 16 :=
  if t = 0 then 2 else if t = 1 then 4 else if t = 2 then 3 else if t = 3 then 5 else 0

private def rpF (_ : Fin 8) : Fin 8 := 1

private def rpA (t : Fin 8) : Fin 8 := if t = 1 then 3 else if t = 2 then 7 else 1

-- pops
private def pb (v : Reg) (o : Option Bool) : Reg := (o, v.2)
private def pp (v : Reg) (o : Option Bool) : Reg := (o, obt v.1, v.2.2)
private def pt (v : Reg) (o : Option (Fin 16)) : Reg := (v.1, o, v.2.2)
private def pfu (v : Reg) (o : Option Bool) : Reg := (o, v.2.1, 0, v.2.2.2)
private def ptg (v : Reg) (o : Option Bool) : Reg :=
  (o, v.2.1, (if o = Option.some true then capI v.2.2.1 else v.2.2.1), v.2.2.2)

-- the gate loops' tag readers: the accumulator saturates exactly as before, and the
-- TERMINATOR pop additionally loads the repeat field from the tag it just finished reading.
private def tgN (v : Reg) (o : Option Bool) : Fin 8 :=
  if o = Option.some true then capT v.2.2.1 else v.2.2.1

private def pgF (v : Reg) (o : Option Bool) : Reg :=
  (o, v.2.1, tgN v o,
    (if o = Option.some false then rpF (tgN v o) else v.2.2.2.1), v.2.2.2.2)

private def pgA (v : Reg) (o : Option Bool) : Reg :=
  (o, v.2.1, tgN v o,
    (if o = Option.some false then rpA (tgN v o) else v.2.2.2.1), v.2.2.2.2)

-- guards
private def gS (v : Reg) : Bool := v.1.isSome
private def gB (v : Reg) : Bool := v.1.getD false
private def gN (v : Reg) : Bool := v.2.1.isSome
private def gO (v : Reg) : Bool := decide (v.2.1 = Option.some (1 : Fin 16))
private def gC (v : Reg) : Bool := decide (v.2.2.1 = (4 : Fin 8))
private def gRep (v : Reg) : Bool := decide (0 < (v.2.2.2.1 : ℕ))
private def gDir (v : Reg) : Bool := v.2.2.2.2.1

-- pushes
private def qT (_ : Reg) : Bool := true
private def qF (_ : Reg) : Bool := false
private def qb (v : Reg) : Bool := v.1.getD false
private def qo (v : Reg) : Bool := decide (v.2.1 = Option.some (1 : Fin 16))
private def n0 (_ : Reg) : Fin 16 := 0
private def n1 (_ : Reg) : Fin 16 := 1
private def n5 (_ : Reg) : Fin 16 := 5
private def n6 (_ : Reg) : Fin 16 := 6
private def n7 (_ : Reg) : Fin 16 := 7
private def n8 (_ : Reg) : Fin 16 := 8
private def nb (v : Reg) : Fin 16 := if v.1.getD false then 1 else 0
private def nt (v : Reg) : Fin 16 := v.2.1.getD 0
private def ntg (v : Reg) : Fin 16 := ocF v.2.2.1

-- loads
private def dcr (v : Reg) : Reg := (v.1, v.2.1, v.2.2.1, decf v.2.2.2.1, v.2.2.2.2)
private def sdF (v : Reg) : Reg := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, false, v.2.2.2.2.2)
private def sdT (v : Reg) : Reg := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, true, v.2.2.2.2.2)
private def rtg (v : Reg) : Reg := (v.1, v.2.1, 0, v.2.2.2)

-- the nibble expander's four bit selectors
private def q0F (y : Fin 16) : Fin 16 := if y.val % 2 = 1 then 1 else 0
private def q1F (y : Fin 16) : Fin 16 := if (y.val / 2) % 2 = 1 then 1 else 0
private def q2F (y : Fin 16) : Fin 16 := if (y.val / 4) % 2 = 1 then 1 else 0
private def q3F (y : Fin 16) : Fin 16 := if (y.val / 8) % 2 = 1 then 1 else 0
private def eF (y : Fin 16) : List (Fin 16) := [q0F y, q1F y, q2F y, q3F y]
private def jF (y : Fin 16) : Bool := decide (y = (1 : Fin 16))
private def p0F (v : Reg) : Fin 16 := (v.2.1.map q0F).getD 0
private def p1F (v : Reg) : Fin 16 := (v.2.1.map q1F).getD 0
private def p2F (v : Reg) : Fin 16 := (v.2.1.map q2F).getD 0
private def p3F (v : Reg) : Fin 16 := (v.2.1.map q3F).getD 0
private def qjF (v : Reg) : Bool := (v.2.1.map jF).getD false

-- the opcode table read at the STATEMENT level: the four one-index opcodes as nibbles
private def ocN : ℕ → Fin 16
  | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 5 | (_ + 4) => 0

private def rpN : ℕ → ℕ
  | 0 => 0 | 1 => 2 | 2 => 6 | 3 => 0 | (_ + 4) => 0

/-! ### 3.  The one hundred and twenty-six labels -/

private inductive Lbl : Type
  | lS | lT | lDL | lDR
  | lF1 | lF2 | lF3 | lFA | lFC
  | lU | lTg | lJ1 | lJ2 | lCl | lFin
  | lV0 | lSD | lFD | lV1 | lV2 | lVp | lVq
  | lL | lL5 | lL1 | lZa
  | lGT | lTz
  | lN1 | lN2 | lN3
  | lA | lB | lC | lD | lE | lFa | lGa | lHa | lKa | lXA | lFb | lGb | lHb | lKb | lXB
  | lP1 | lP2 | lP3 | lP4 | lSK | lSKT
  | lQ1 | lQ7 | lQ2 | lQ6 | lR2 | lR1
  | lQX | lPa | lPm | lPb
  | lGTz | lTzz
  | lN1z | lN2z | lN3z
  | lAz | lBz | lCz | lDz | lEz | lFaz | lGaz | lHaz | lKaz | lXAz
  | lFbz | lGbz | lHbz | lKbz | lXBz
  | lP1z | lP2z | lP3z | lP4z | lSKz | lSKTz
  | lQ1z | lQ7z | lQ2z | lQ6z | lR2z | lR1z
  | lTR | lVr | lVs
  | lW | lW8 | lW1 | lWa | lWb | lWc | lZb
  | lGR
  | lY | lY0 | lY1 | lY2 | lY3 | lYD
  | lZ0 | lZ1 | lZ2 | lZ3 | lZ4 | lZ5 | lZ6 | lZ7 | lZ8 | lZ9 | lZ10 | lZ11 | lZ12 | lZR
  | lH
  deriving DecidableEq

private instance : Fintype Lbl where
  elems := ⟨[Lbl.lS, Lbl.lT, Lbl.lDL, Lbl.lDR,
    Lbl.lF1, Lbl.lF2, Lbl.lF3, Lbl.lFA, Lbl.lFC,
    Lbl.lU, Lbl.lTg, Lbl.lJ1, Lbl.lJ2, Lbl.lCl, Lbl.lFin,
    Lbl.lV0, Lbl.lSD, Lbl.lFD, Lbl.lV1, Lbl.lV2, Lbl.lVp, Lbl.lVq,
    Lbl.lL, Lbl.lL5, Lbl.lL1, Lbl.lZa,
    Lbl.lGT, Lbl.lTz,
    Lbl.lN1, Lbl.lN2, Lbl.lN3,
    Lbl.lA, Lbl.lB, Lbl.lC, Lbl.lD, Lbl.lE, Lbl.lFa, Lbl.lGa, Lbl.lHa, Lbl.lKa,
    Lbl.lXA, Lbl.lFb, Lbl.lGb, Lbl.lHb, Lbl.lKb, Lbl.lXB,
    Lbl.lP1, Lbl.lP2, Lbl.lP3, Lbl.lP4, Lbl.lSK, Lbl.lSKT,
    Lbl.lQ1, Lbl.lQ7, Lbl.lQ2, Lbl.lQ6, Lbl.lR2, Lbl.lR1,
    Lbl.lQX, Lbl.lPa, Lbl.lPm, Lbl.lPb,
    Lbl.lGTz, Lbl.lTzz,
    Lbl.lN1z, Lbl.lN2z, Lbl.lN3z,
    Lbl.lAz, Lbl.lBz, Lbl.lCz, Lbl.lDz, Lbl.lEz, Lbl.lFaz, Lbl.lGaz, Lbl.lHaz,
    Lbl.lKaz, Lbl.lXAz, Lbl.lFbz, Lbl.lGbz, Lbl.lHbz, Lbl.lKbz, Lbl.lXBz,
    Lbl.lP1z, Lbl.lP2z, Lbl.lP3z, Lbl.lP4z, Lbl.lSKz, Lbl.lSKTz,
    Lbl.lQ1z, Lbl.lQ7z, Lbl.lQ2z, Lbl.lQ6z, Lbl.lR2z, Lbl.lR1z,
    Lbl.lTR, Lbl.lVr, Lbl.lVs,
    Lbl.lW, Lbl.lW8, Lbl.lW1, Lbl.lWa, Lbl.lWb, Lbl.lWc, Lbl.lZb,
    Lbl.lGR,
    Lbl.lY, Lbl.lY0, Lbl.lY1, Lbl.lY2, Lbl.lY3, Lbl.lYD,
    Lbl.lZ0, Lbl.lZ1, Lbl.lZ2, Lbl.lZ3, Lbl.lZ4, Lbl.lZ5, Lbl.lZ6, Lbl.lZ7, Lbl.lZ8,
    Lbl.lZ9, Lbl.lZ10, Lbl.lZ11, Lbl.lZ12, Lbl.lZR,
    Lbl.lH], by decide⟩
  complete := fun x => by cases x <;> decide

-- the register-computed label dispatches: two loop dispatches and the two sweep dispatches
private def dspF (v : Reg) : Lbl := if v.2.2.1 = (4 : Fin 8) then Lbl.lA
  else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKT else Lbl.lN1
private def dspA (v : Reg) : Lbl := if v.2.2.1 = (4 : Fin 8) then Lbl.lAz
  else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKTz else Lbl.lN1z
private def dLF (v : Reg) : Lbl := if v.1.getD false then Lbl.lL5 else Lbl.lL1
private def dEF (v : Reg) : Lbl := if v.1.getD false then Lbl.lW8 else Lbl.lWa

/-! ### 4.  The drain order, indexed by `ℕ` -/

private def ksF : ℕ → Stk
  | 0 => Stk.kin | 1 => Stk.ksrc | 2 => Stk.kxin | 3 => Stk.khld | 4 => Stk.kpd1
  | 5 => Stk.kpd2 | 6 => Stk.kqc | 7 => Stk.kfu | 8 => Stk.ktok | 9 => Stk.kidx
  | 10 => Stk.kopc | 11 => Stk.kscA | 12 => Stk.kscB | (_ + 13) => Stk.kbit

private def ksN : Stk → ℕ
  | Stk.kin => 0 | Stk.ksrc => 1 | Stk.kxin => 2 | Stk.khld => 3 | Stk.kpd1 => 4
  | Stk.kpd2 => 5 | Stk.kqc => 6 | Stk.kfu => 7 | Stk.ktok => 8 | Stk.kidx => 9
  | Stk.kopc => 10 | Stk.kscA => 11 | Stk.kscB => 12 | Stk.kbit => 13

private def lsF : ℕ → Lbl
  | 0 => Lbl.lZ0 | 1 => Lbl.lZ1 | 2 => Lbl.lZ2 | 3 => Lbl.lZ3 | 4 => Lbl.lZ4
  | 5 => Lbl.lZ5 | 6 => Lbl.lZ6 | 7 => Lbl.lZ7 | 8 => Lbl.lZ8 | 9 => Lbl.lZ9
  | 10 => Lbl.lZ10 | 11 => Lbl.lZ11 | 12 => Lbl.lZ12 | (_ + 13) => Lbl.lZR

private def fpF : ∀ i : ℕ, Reg → Option (Gam (ksF i)) → Reg
  | 0 => pb | 1 => pb | 2 => pb | 3 => pt | 4 => pb | 5 => pb | 6 => pb | 7 => pb
  | 8 => pb | 9 => pb | 10 => pt | 11 => pb | 12 => pb | (_ + 13) => pb

private def gtF : ℕ → Reg → Bool
  | 0 => gS | 1 => gS | 2 => gS | 3 => gN | 4 => gS | 5 => gS | 6 => gS | 7 => gS
  | 8 => gS | 9 => gS | 10 => gN | 11 => gS | 12 => gS | (_ + 13) => gS

/-! ### 5.  The program, in PHASE ORDER = WORD ORDER -/

private def Mw : Lbl → Stmt Gam Lbl Reg
  -- SPLIT
  | Lbl.lS => Stmt.pop Stk.kin pb (Stmt.branch gS
      (Stmt.pop Stk.kin pp (Stmt.branch gS
        (Stmt.branch gO (Stmt.push Stk.kscB qb (Stmt.goto (fun _ => Lbl.lT)))
          (Stmt.push Stk.kscA qb (Stmt.goto (fun _ => Lbl.lS))))
        (Stmt.goto (fun _ => Lbl.lDL))))
      (Stmt.goto (fun _ => Lbl.lDL)))
  | Lbl.lT => Stmt.pop Stk.kin pb (Stmt.branch gS
      (Stmt.pop Stk.kin pp (Stmt.branch gS
        (Stmt.branch gO (Stmt.push Stk.kscB qb (Stmt.goto (fun _ => Lbl.lT)))
          (Stmt.goto (fun _ => Lbl.lT)))
        (Stmt.goto (fun _ => Lbl.lDL))))
      (Stmt.goto (fun _ => Lbl.lDL)))
  | Lbl.lDL => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.ksrc qb (Stmt.goto (fun _ => Lbl.lDL)))
      (Stmt.goto (fun _ => Lbl.lDR)))
  | Lbl.lDR => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kxin qb (Stmt.goto (fun _ => Lbl.lDR)))
      (Stmt.goto (fun _ => Lbl.lF1)))
  -- FIELDS
  | Lbl.lF1 => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.branch gB
        (Stmt.push Stk.kpd1 qF (Stmt.push Stk.kpd2 qF (Stmt.goto (fun _ => Lbl.lF1))))
        (Stmt.push Stk.kpd1 qF (Stmt.push Stk.kpd2 qF (Stmt.goto (fun _ => Lbl.lF2)))))
      (Stmt.goto (fun _ => lsF 0)))
  | Lbl.lF2 => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.branch gB (Stmt.push Stk.kqc qT (Stmt.goto (fun _ => Lbl.lF2)))
        (Stmt.goto (fun _ => Lbl.lF3)))
      (Stmt.goto (fun _ => lsF 0)))
  | Lbl.lF3 => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.branch gB (Stmt.push Stk.kfu qT (Stmt.goto (fun _ => Lbl.lF3)))
        (Stmt.goto (fun _ => Lbl.lFA)))
      (Stmt.goto (fun _ => lsF 0)))
  | Lbl.lFA => Stmt.pop Stk.kxin pb (Stmt.branch gS
      (Stmt.push Stk.khld nb (Stmt.goto (fun _ => Lbl.lFA)))
      (Stmt.goto (fun _ => Lbl.lFC)))
  | Lbl.lFC => Stmt.pop Stk.khld pt (Stmt.branch gN
      (Stmt.push Stk.kpd1 qo (Stmt.push Stk.kpd2 qo (Stmt.goto (fun _ => Lbl.lFC))))
      (Stmt.goto (fun _ => Lbl.lU)))
  -- TOKENISE.  Its exit is the block theorem's BOUND parameter, so re-pointing it at the
  -- new scratch drain costs no re-proof.
  | Lbl.lU => Stmt.pop Stk.kfu pfu (Stmt.branch gS
      (Stmt.push Stk.kscA qT (Stmt.goto (fun _ => Lbl.lTg)))
      (Stmt.goto (fun _ => Lbl.lFin)))
  | Lbl.lTg => Stmt.pop Stk.ksrc ptg (Stmt.branch gS
      (Stmt.push Stk.khld nb (Stmt.push Stk.kscA qF (Stmt.branch gB
        (Stmt.goto (fun _ => Lbl.lTg)) (Stmt.goto (fun _ => Lbl.lJ1)))))
      (Stmt.goto (fun _ => Lbl.lCl)))
  | Lbl.lJ1 => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.push Stk.khld nb (Stmt.push Stk.kscA qF (Stmt.branch gB
        (Stmt.goto (fun _ => Lbl.lJ1))
        (Stmt.goto (fun z => cond (gC z) Lbl.lJ2 Lbl.lU)))))
      (Stmt.goto (fun _ => Lbl.lCl)))
  | Lbl.lJ2 => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.push Stk.khld nb (Stmt.push Stk.kscA qF (Stmt.branch gB
        (Stmt.goto (fun _ => Lbl.lJ2)) (Stmt.goto (fun _ => Lbl.lU)))))
      (Stmt.goto (fun _ => Lbl.lCl)))
  | Lbl.lCl => Stmt.pop Stk.kscA pb (Stmt.branch gB
      (Stmt.goto (fun _ => Lbl.lFin))
      (Stmt.pop Stk.khld pt (Stmt.goto (fun _ => Lbl.lCl))))
  | Lbl.lFin => Stmt.pop Stk.khld pt (Stmt.branch gN
      (Stmt.push Stk.ktok qo (Stmt.goto (fun _ => Lbl.lFin)))
      (Stmt.goto (fun _ => Lbl.lV0)))
  -- THE SCRATCH-TRAIL DRAIN.  One label, one pop, no push.
  | Lbl.lV0 => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lV0)) (Stmt.goto (fun _ => Lbl.lSD)))
  | Lbl.lSD => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lSD)) (Stmt.goto (fun _ => Lbl.lFD)))
  -- THE FUEL DRAIN.  Same one-pop no-push shape, on the fuel port.
  | Lbl.lFD => Stmt.pop Stk.kfu pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lFD)) (Stmt.goto (fun _ => Lbl.lV1)))
  -- DUPLICATOR 1: the token stream, for the two gate loops.
  | Lbl.lV1 => Stmt.pop Stk.ktok pb (Stmt.branch gS
      (Stmt.push Stk.khld nb (Stmt.goto (fun _ => Lbl.lV1)))
      (Stmt.goto (fun _ => Lbl.lV2)))
  | Lbl.lV2 => Stmt.pop Stk.khld pt (Stmt.branch gN
      (Stmt.push Stk.ktok qo (Stmt.push Stk.kxin qo (Stmt.goto (fun _ => Lbl.lV2))))
      (Stmt.goto (fun _ => Lbl.lVp)))
  -- DUPLICATOR 2: the first padded copy -> the sweep tape and the FIRST zero-run counter.
  | Lbl.lVp => Stmt.pop Stk.kpd1 pb (Stmt.branch gS
      (Stmt.push Stk.kin qb (Stmt.goto (fun _ => Lbl.lVp)))
      (Stmt.goto (fun _ => Lbl.lVq)))
  | Lbl.lVq => Stmt.pop Stk.kin pb (Stmt.branch gS
      (Stmt.push Stk.kpd1 qb (Stmt.push Stk.kfu qb (Stmt.goto (fun _ => Lbl.lVq))))
      (Stmt.goto (fun _ => Lbl.lL)))
  -- THE `L` SWEEP, first in the word.
  | Lbl.lL => Stmt.pop Stk.kpd1 pb (Stmt.branch gS
      (Stmt.goto dLF) (Stmt.goto (fun _ => Lbl.lZa)))
  | Lbl.lL5 => Stmt.push Stk.kopc n5 (Stmt.goto (fun _ => Lbl.lL1))
  | Lbl.lL1 => Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lL))
  -- THE FIRST ZERO RUN.
  | Lbl.lZa => Stmt.pop Stk.kfu pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lZa)))
      (Stmt.goto (fun _ => Lbl.lGT)))
  -- THE FORWARD GATE LOOP: MIRRORED symbols, emitting STRAIGHT to the opcode port.
  | Lbl.lGT => Stmt.load rtg (Stmt.goto (fun _ => Lbl.lTz))
  | Lbl.lTz => Stmt.pop Stk.ktok pgF (Stmt.branch gS
      (Stmt.branch gB (Stmt.goto (fun _ => Lbl.lTz)) (Stmt.goto dspF))
      (Stmt.goto (fun _ => Lbl.lQX)))
  | Lbl.lN1 => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lN1))))
      (Stmt.goto (fun _ => Lbl.lN2)))
  | Lbl.lN2 => Stmt.push Stk.kopc ntg (Stmt.load dcr (Stmt.branch gRep
      (Stmt.goto (fun _ => Lbl.lN2)) (Stmt.goto (fun _ => Lbl.lN3))))
  | Lbl.lN3 => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lN3)))
      (Stmt.goto (fun _ => Lbl.lGT)))
  | Lbl.lA => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.goto (fun _ => Lbl.lA)))
      (Stmt.goto (fun _ => Lbl.lB)))
  | Lbl.lB => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.push Stk.kscB qT (Stmt.goto (fun _ => Lbl.lB)))
      (Stmt.goto (fun _ => Lbl.lC)))
  | Lbl.lC => Stmt.push Stk.ktok qF (Stmt.goto (fun _ => Lbl.lD))
  | Lbl.lD => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lE)) (Stmt.goto (fun _ => Lbl.lFa)))
  | Lbl.lE => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.ktok qT (Stmt.goto (fun _ => Lbl.lD)))
      (Stmt.goto (fun _ => Lbl.lFb)))
  | Lbl.lFa => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lGa))
  | Lbl.lGa => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lGa)))
      (Stmt.goto (fun _ => Lbl.lHa)))
  | Lbl.lHa => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lKa))
  | Lbl.lKa => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lKa)))
      (Stmt.goto (fun _ => Lbl.lXA)))
  -- MIRRORED CNOT: the `i < j` exit takes the orientation bit the adjoint loop uses for
  -- `j < i`, and vice versa.
  | Lbl.lXA => Stmt.load sdT (Stmt.goto (fun _ => Lbl.lP1))
  | Lbl.lFb => Stmt.push Stk.kscA qT (Stmt.push Stk.kidx qF
      (Stmt.goto (fun _ => Lbl.lGb)))
  | Lbl.lGb => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lGb)))
      (Stmt.goto (fun _ => Lbl.lHb)))
  | Lbl.lHb => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lKb))
  | Lbl.lKb => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lKb)))
      (Stmt.goto (fun _ => Lbl.lXB)))
  | Lbl.lXB => Stmt.load sdF (Stmt.goto (fun _ => Lbl.lQ1))
  | Lbl.lP1 => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.goto (fun _ => Lbl.lP1)))
      (Stmt.push Stk.kscA qF (Stmt.goto (fun _ => Lbl.lP2))))
  | Lbl.lP2 => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lP3)))
      (Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lP4))))
  | Lbl.lP3 => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qb (Stmt.goto (fun _ => Lbl.lP3)))
      (Stmt.goto (fun _ => Lbl.lQ1)))
  | Lbl.lP4 => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qb (Stmt.goto (fun _ => Lbl.lP4)))
      (Stmt.goto (fun _ => Lbl.lSK)))
  | Lbl.lSK => Stmt.pop Stk.kidx pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lSK)) (Stmt.goto (fun _ => Lbl.lGT)))
  -- THE TAG SKIP ARM: one index field consumed, nothing pushed.
  | Lbl.lSKT => Stmt.pop Stk.ktok pb (Stmt.branch gB
      (Stmt.goto (fun _ => Lbl.lSKT)) (Stmt.goto (fun _ => Lbl.lGT)))
  | Lbl.lQ1 => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lQ1))))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lQ7 Lbl.lQ2)))
  | Lbl.lQ7 => Stmt.push Stk.kopc n6 (Stmt.goto (fun w => cond (gDir w) Lbl.lQ2 Lbl.lR2))
  | Lbl.lQ2 => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscB qT (Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lQ2))))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lQ6 Lbl.lQ7)))
  | Lbl.lQ6 => Stmt.push Stk.kopc n7 (Stmt.goto (fun w => cond (gDir w) Lbl.lR2 Lbl.lR1))
  | Lbl.lR2 => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lR2)))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lR1 Lbl.lQ6)))
  | Lbl.lR1 => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lR1)))
      (Stmt.goto (fun _ => Lbl.lGT)))
  -- THE OUTPUT-WIRE MARKER, between the two block streams exactly as the target has it.
  | Lbl.lQX => Stmt.pop Stk.kqc pb (Stmt.branch gS
      (Stmt.push Stk.kscA qT (Stmt.push Stk.kscB qT (Stmt.goto (fun _ => Lbl.lQX))))
      (Stmt.goto (fun _ => Lbl.lPa)))
  | Lbl.lPa => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lPa)))
      (Stmt.goto (fun _ => Lbl.lPm)))
  | Lbl.lPm => Stmt.push Stk.kopc n8 (Stmt.goto (fun _ => Lbl.lPb))
  | Lbl.lPb => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lPb)))
      (Stmt.goto (fun _ => Lbl.lGTz)))
  -- THE ADJOINT GATE LOOP: NORMAL symbols, reading the DUPLICATED token copy and emitting
  -- into the hold, which one reversing transfer then moves onto the opcode port.
  | Lbl.lGTz => Stmt.load rtg (Stmt.goto (fun _ => Lbl.lTzz))
  | Lbl.lTzz => Stmt.pop Stk.kxin pgA (Stmt.branch gS
      (Stmt.branch gB (Stmt.goto (fun _ => Lbl.lTzz)) (Stmt.goto dspA))
      (Stmt.goto (fun _ => Lbl.lTR)))
  | Lbl.lN1z => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.push Stk.khld n0 (Stmt.goto (fun _ => Lbl.lN1z))))
      (Stmt.goto (fun _ => Lbl.lN2z)))
  | Lbl.lN2z => Stmt.push Stk.khld ntg (Stmt.load dcr (Stmt.branch gRep
      (Stmt.goto (fun _ => Lbl.lN2z)) (Stmt.goto (fun _ => Lbl.lN3z))))
  | Lbl.lN3z => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.khld n1 (Stmt.goto (fun _ => Lbl.lN3z)))
      (Stmt.goto (fun _ => Lbl.lGTz)))
  | Lbl.lAz => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.goto (fun _ => Lbl.lAz)))
      (Stmt.goto (fun _ => Lbl.lBz)))
  | Lbl.lBz => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.push Stk.kscB qT (Stmt.goto (fun _ => Lbl.lBz)))
      (Stmt.goto (fun _ => Lbl.lCz)))
  | Lbl.lCz => Stmt.push Stk.kxin qF (Stmt.goto (fun _ => Lbl.lDz))
  | Lbl.lDz => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lEz)) (Stmt.goto (fun _ => Lbl.lFaz)))
  | Lbl.lEz => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kxin qT (Stmt.goto (fun _ => Lbl.lDz)))
      (Stmt.goto (fun _ => Lbl.lFbz)))
  | Lbl.lFaz => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lGaz))
  | Lbl.lGaz => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lGaz)))
      (Stmt.goto (fun _ => Lbl.lHaz)))
  | Lbl.lHaz => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lKaz))
  | Lbl.lKaz => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lKaz)))
      (Stmt.goto (fun _ => Lbl.lXAz)))
  | Lbl.lXAz => Stmt.load sdF (Stmt.goto (fun _ => Lbl.lP1z))
  | Lbl.lFbz => Stmt.push Stk.kscA qT (Stmt.push Stk.kidx qF
      (Stmt.goto (fun _ => Lbl.lGbz)))
  | Lbl.lGbz => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lGbz)))
      (Stmt.goto (fun _ => Lbl.lHbz)))
  | Lbl.lHbz => Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lKbz))
  | Lbl.lKbz => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lKbz)))
      (Stmt.goto (fun _ => Lbl.lXBz)))
  | Lbl.lXBz => Stmt.load sdT (Stmt.goto (fun _ => Lbl.lQ1z))
  | Lbl.lP1z => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.goto (fun _ => Lbl.lP1z)))
      (Stmt.push Stk.kscA qF (Stmt.goto (fun _ => Lbl.lP2z))))
  | Lbl.lP2z => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kidx qT (Stmt.goto (fun _ => Lbl.lP3z)))
      (Stmt.push Stk.kidx qF (Stmt.goto (fun _ => Lbl.lP4z))))
  | Lbl.lP3z => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qb (Stmt.goto (fun _ => Lbl.lP3z)))
      (Stmt.goto (fun _ => Lbl.lQ1z)))
  | Lbl.lP4z => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.kidx qb (Stmt.goto (fun _ => Lbl.lP4z)))
      (Stmt.goto (fun _ => Lbl.lSKz)))
  | Lbl.lSKz => Stmt.pop Stk.kidx pb (Stmt.branch gS
      (Stmt.goto (fun _ => Lbl.lSKz)) (Stmt.goto (fun _ => Lbl.lGTz)))
  | Lbl.lSKTz => Stmt.pop Stk.kxin pb (Stmt.branch gB
      (Stmt.goto (fun _ => Lbl.lSKTz)) (Stmt.goto (fun _ => Lbl.lGTz)))
  | Lbl.lQ1z => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscA qT (Stmt.push Stk.khld n0 (Stmt.goto (fun _ => Lbl.lQ1z))))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lQ7z Lbl.lQ2z)))
  | Lbl.lQ7z => Stmt.push Stk.khld n7 (Stmt.goto (fun w => cond (gDir w) Lbl.lQ2z Lbl.lR2z))
  | Lbl.lQ2z => Stmt.pop Stk.kidx pb (Stmt.branch gB
      (Stmt.push Stk.kscB qT (Stmt.push Stk.khld n0 (Stmt.goto (fun _ => Lbl.lQ2z))))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lQ6z Lbl.lQ7z)))
  | Lbl.lQ6z => Stmt.push Stk.khld n6 (Stmt.goto (fun w => cond (gDir w) Lbl.lR2z Lbl.lR1z))
  | Lbl.lR2z => Stmt.pop Stk.kscB pb (Stmt.branch gS
      (Stmt.push Stk.khld n1 (Stmt.goto (fun _ => Lbl.lR2z)))
      (Stmt.goto (fun w => cond (gDir w) Lbl.lR1z Lbl.lQ6z)))
  | Lbl.lR1z => Stmt.pop Stk.kscA pb (Stmt.branch gS
      (Stmt.push Stk.khld n1 (Stmt.goto (fun _ => Lbl.lR1z)))
      (Stmt.goto (fun _ => Lbl.lGTz)))
  -- THE ADJOINT TRANSFER: one label, one reversing copy of the buffered adjoint stream.
  | Lbl.lTR => Stmt.pop Stk.khld pt (Stmt.branch gN
      (Stmt.push Stk.kopc nt (Stmt.goto (fun _ => Lbl.lTR)))
      (Stmt.goto (fun _ => Lbl.lVr)))
  -- DUPLICATOR 3: the second padded copy -> the sweep tape again and the SECOND zero-run
  -- counter.  This is what lets ONE sweep instantiation serve both sweeps.
  | Lbl.lVr => Stmt.pop Stk.kpd2 pb (Stmt.branch gS
      (Stmt.push Stk.ksrc qb (Stmt.goto (fun _ => Lbl.lVr)))
      (Stmt.goto (fun _ => Lbl.lVs)))
  | Lbl.lVs => Stmt.pop Stk.ksrc pb (Stmt.branch gS
      (Stmt.push Stk.kpd1 qb (Stmt.push Stk.kfu qb (Stmt.goto (fun _ => Lbl.lVs))))
      (Stmt.goto (fun _ => Lbl.lW)))
  -- THE `E` SWEEP, on the SAME tape port as the `L` sweep.
  | Lbl.lW => Stmt.pop Stk.kpd1 pb (Stmt.branch gS
      (Stmt.goto dEF) (Stmt.goto (fun _ => Lbl.lZb)))
  | Lbl.lW8 => Stmt.push Stk.kopc n8 (Stmt.goto (fun _ => Lbl.lW1))
  | Lbl.lW1 => Stmt.push Stk.kopc n1 (Stmt.goto (fun _ => Lbl.lW))
  | Lbl.lWa => Stmt.push Stk.kopc n5 (Stmt.goto (fun _ => Lbl.lWb))
  | Lbl.lWb => Stmt.push Stk.kopc n8 (Stmt.goto (fun _ => Lbl.lWc))
  | Lbl.lWc => Stmt.push Stk.kopc n5 (Stmt.goto (fun _ => Lbl.lW1))
  -- THE SECOND ZERO RUN.
  | Lbl.lZb => Stmt.pop Stk.kfu pb (Stmt.branch gS
      (Stmt.push Stk.kopc n0 (Stmt.goto (fun _ => Lbl.lZb)))
      (Stmt.goto (fun _ => Lbl.lGR)))
  -- THE ONE GLOBAL REVERSAL.  Emission order is word order; the port holds its reverse;
  -- this label turns it round once, onto the hold, which the expander then reads.
  | Lbl.lGR => Stmt.pop Stk.kopc pt (Stmt.branch gN
      (Stmt.push Stk.khld nt (Stmt.goto (fun _ => Lbl.lGR)))
      (Stmt.goto (fun _ => Lbl.lY)))
  -- EXPAND, with the two nibble ports in the roles the reversal leaves them in.
  | Lbl.lY => Stmt.pop Stk.khld pt (Stmt.branch gN
      (Stmt.goto (fun _ => Lbl.lY0)) (Stmt.goto (fun _ => Lbl.lYD)))
  | Lbl.lY0 => Stmt.push Stk.kopc p0F (Stmt.goto (fun _ => Lbl.lY1))
  | Lbl.lY1 => Stmt.push Stk.kopc p1F (Stmt.goto (fun _ => Lbl.lY2))
  | Lbl.lY2 => Stmt.push Stk.kopc p2F (Stmt.goto (fun _ => Lbl.lY3))
  | Lbl.lY3 => Stmt.push Stk.kopc p3F (Stmt.goto (fun _ => Lbl.lY))
  | Lbl.lYD => Stmt.pop Stk.kopc pt (Stmt.branch gN
      (Stmt.push Stk.kbit qjF (Stmt.goto (fun _ => Lbl.lYD)))
      (Stmt.goto (fun _ => lsF 0)))
  -- DRAIN
  | Lbl.lZ0 => Stmt.pop (ksF 0) (fpF 0) (Stmt.branch (gtF 0)
      (Stmt.goto (fun _ => lsF 0)) (Stmt.goto (fun _ => lsF 1)))
  | Lbl.lZ1 => Stmt.pop (ksF 1) (fpF 1) (Stmt.branch (gtF 1)
      (Stmt.goto (fun _ => lsF 1)) (Stmt.goto (fun _ => lsF 2)))
  | Lbl.lZ2 => Stmt.pop (ksF 2) (fpF 2) (Stmt.branch (gtF 2)
      (Stmt.goto (fun _ => lsF 2)) (Stmt.goto (fun _ => lsF 3)))
  | Lbl.lZ3 => Stmt.pop (ksF 3) (fpF 3) (Stmt.branch (gtF 3)
      (Stmt.goto (fun _ => lsF 3)) (Stmt.goto (fun _ => lsF 4)))
  | Lbl.lZ4 => Stmt.pop (ksF 4) (fpF 4) (Stmt.branch (gtF 4)
      (Stmt.goto (fun _ => lsF 4)) (Stmt.goto (fun _ => lsF 5)))
  | Lbl.lZ5 => Stmt.pop (ksF 5) (fpF 5) (Stmt.branch (gtF 5)
      (Stmt.goto (fun _ => lsF 5)) (Stmt.goto (fun _ => lsF 6)))
  | Lbl.lZ6 => Stmt.pop (ksF 6) (fpF 6) (Stmt.branch (gtF 6)
      (Stmt.goto (fun _ => lsF 6)) (Stmt.goto (fun _ => lsF 7)))
  | Lbl.lZ7 => Stmt.pop (ksF 7) (fpF 7) (Stmt.branch (gtF 7)
      (Stmt.goto (fun _ => lsF 7)) (Stmt.goto (fun _ => lsF 8)))
  | Lbl.lZ8 => Stmt.pop (ksF 8) (fpF 8) (Stmt.branch (gtF 8)
      (Stmt.goto (fun _ => lsF 8)) (Stmt.goto (fun _ => lsF 9)))
  | Lbl.lZ9 => Stmt.pop (ksF 9) (fpF 9) (Stmt.branch (gtF 9)
      (Stmt.goto (fun _ => lsF 9)) (Stmt.goto (fun _ => lsF 10)))
  | Lbl.lZ10 => Stmt.pop (ksF 10) (fpF 10) (Stmt.branch (gtF 10)
      (Stmt.goto (fun _ => lsF 10)) (Stmt.goto (fun _ => lsF 11)))
  | Lbl.lZ11 => Stmt.pop (ksF 11) (fpF 11) (Stmt.branch (gtF 11)
      (Stmt.goto (fun _ => lsF 11)) (Stmt.goto (fun _ => lsF 12)))
  | Lbl.lZ12 => Stmt.pop (ksF 12) (fpF 12) (Stmt.branch (gtF 12)
      (Stmt.goto (fun _ => lsF 12)) (Stmt.goto (fun _ => lsF 13)))
  | Lbl.lZR => Stmt.load (fun _ => r0) (Stmt.goto (fun _ => Lbl.lH))
  | Lbl.lH => Stmt.halt

private abbrev tmA : Turing.FinTM2 :=
  { K := Stk, k₀ := Stk.kin, k₁ := Stk.kbit, Γ := Gam, Λ := Lbl, main := Lbl.lS,
    σ := Reg, initialState := r0, m := Mw }

/-! ### 6.  The facts that are not `rfl` -/

private lemma ksNum : ∀ i : ℕ, i < 13 → ksN (ksF i) = i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | (n + 13), h => absurd h (by omega)

private lemma hinjA : ∀ i i' : ℕ, i < 13 → i' < 13 → i ≠ i' → ksF i ≠ ksF i' := by
  intro i i' hi hi' hne h
  exact hne (((ksNum i hi).symm.trans (congrArg ksN h)).trans (ksNum i' hi'))

private lemma hbitA : ∀ i : ℕ, i < 13 → ksF i ≠ Stk.kbit
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | (n + 13), h => absurd h (by omega)

private lemma hsurA : ∀ k : Stk, k ≠ Stk.kbit → ∃ i : ℕ, i < 13 ∧ ksF i = k := by
  intro k hk
  cases k
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨3, by omega, rfl⟩
  · exact ⟨4, by omega, rfl⟩
  · exact ⟨5, by omega, rfl⟩
  · exact ⟨6, by omega, rfl⟩
  · exact ⟨7, by omega, rfl⟩
  · exact ⟨8, by omega, rfl⟩
  · exact ⟨9, by omega, rfl⟩
  · exact ⟨10, by omega, rfl⟩
  · exact absurd rfl hk
  · exact ⟨11, by omega, rfl⟩
  · exact ⟨12, by omega, rfl⟩

private lemma capIter : ∀ n : ℕ, capI^[n] (0 : Fin 8) = ⟨min n 5, by omega⟩ := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases h : min k 5 < 5
      · have e1 : capI (⟨min k 5, by omega⟩ : Fin 8) = ⟨min k 5 + 1, by omega⟩ := dif_pos h
        have e2 : min (k + 1) 5 = min k 5 + 1 := by omega
        rw [e1]
        exact Fin.val_injective (by simpa using e2.symm)
      · have e1 : capI (⟨min k 5, by omega⟩ : Fin 8) = ⟨min k 5, by omega⟩ := dif_neg h
        have e2 : min (k + 1) 5 = min k 5 := by omega
        rw [e1]
        exact Fin.val_injective (by simpa using e2.symm)

private lemma hcnA : ∀ (v : Reg) (y : Bool) (n : ℕ),
    gC (ptg ((fun z => ptg z (Option.some true))^[n] (pfu v (Option.some y)))
      (Option.some false)) = decide (n = 4) := by
  intro v y n
  have hit : ∀ (m : ℕ) (w : Reg),
      ((fun z => ptg z (Option.some true))^[m] w).2.2.1 = capI^[m] w.2.2.1 := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
        rfl
  have h2 : (ptg ((fun z => ptg z (Option.some true))^[n] (pfu v (Option.some y)))
      (Option.some false)).2.2.1
      = ((fun z => ptg z (Option.some true))^[n] (pfu v (Option.some y))).2.2.1 := rfl
  have h1 : (pfu v (Option.some y)).2.2.1 = (0 : Fin 8) := rfl
  show decide ((ptg ((fun z => ptg z (Option.some true))^[n] (pfu v (Option.some y)))
      (Option.some false)).2.2.1 = (4 : Fin 8)) = decide (n = 4)
  rw [h2, hit n, h1, capIter n]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
  · have hv := congrArg Fin.val h
    simp only at hv
    omega
  · subst h; rfl

-- the opcode table and the two repeat tables, read at a tag value below four
private lemma hocA : ∀ (c : Fin 8) (t : ℕ), t < 4 → (c : ℕ) = t → ocF c = ocN t := by
  intro c t ht hc
  subst hc
  revert ht
  fin_cases c <;> decide

private lemma hrpAv : ∀ (c : Fin 8) (t : ℕ), t < 4 → (c : ℕ) = t →
    ((rpA c : Fin 8) : ℕ) = rpN t + 1 := by
  intro c t ht hc
  subst hc
  revert ht
  fin_cases c <;> decide

private lemma hgTA : ∀ (i : ℕ) (w : Reg) (y : Gam (ksF i)),
    gtF i (fpF i w (Option.some y)) = true := by
  intro i w y
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | (n + 13) => rfl

private lemma hgFA : ∀ (i : ℕ) (w : Reg), gtF i (fpF i w Option.none) = false := by
  intro i w
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | (n + 13) => rfl

private lemma hdrA : ∀ i : ℕ, i < 13 → tmA.m (lsF i) = Stmt.pop (ksF i) (fpF i)
    (Stmt.branch (gtF i) (Stmt.goto (fun _ => lsF i)) (Stmt.goto (fun _ => lsF (i + 1))))
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | (n + 13), h => absurd h (by omega)

/-! ### 7.  The statement -/
theorem _root_.BQPReferenceValidation.candidate28 :
    -- ONE concrete `Turing.FinTM2` -- fourteen stacks, ONE HUNDRED AND TWENTY-SIX all-nullary
    -- labels, a `Bool`/`Fin 16` two-alphabet stack family and a six-component register -- on
    -- which every accepted block program sits simultaneously and is wired end to end IN THE
    -- ORDER OF THE COMPILED WORD, with TWO gate-rendering loops (a mirrored forward one
    -- emitting straight to the opcode port, and a normal adjoint one emitting into the hold
    -- and then transferred by one reversing copy), the two padded zero-runs hosted, the
    -- output-wire marker BETWEEN the two block streams, and ONE global reversal at the end.
    -- Every alphabet seam is pinned by NAME in the outermost existential.  No run theorem for
    -- any phase is claimed here.
    ∃ (tm : Turing.FinTM2)
      (kin ksrc kxin khld kpd1 kpd2 kqc kfu ktok kidx kopc kbit kscA kscB : tm.K)
      (ks : ℕ → tm.K) (ls : ℕ → tm.Λ)
      (lS lT lDL lDR lF1 lF2 lF3 lFA lFC lU lTg lJ1 lJ2 lCl lFin
        lV0 lSD lFD lV1 lV2 lVp lVq lL lL5 lL1 lZa lGT lTz
        lN1 lN2 lN3 lA lB lC lD lE lFa lGa lHa lKa lXA lFb lGb lHb lKb lXB
        lP1 lP2 lP3 lP4 lSK lSKT lQ1 lQ7 lQ2 lQ6 lR2 lR1 lQX lPa lPm lPb
        lGTz lTzz lN1z lN2z lN3z lAz lBz lCz lDz lEz lFaz lGaz lHaz lKaz lXAz
        lFbz lGbz lHbz lKbz lXBz lP1z lP2z lP3z lP4z lSKz lSKTz
        lQ1z lQ7z lQ2z lQ6z lR2z lR1z lTR lVr lVs
        lW lW8 lW1 lWa lWb lWc lZb lGR lY lY0 lY1 lY2 lY3 lYD lH : tm.Λ)
      -- THE SEAM PACK.  Every alphabet symbol and encoder that more than one block touches is
      -- bound HERE, once, and used below by each of those blocks.  `uh`/`un` are the two
      -- nibble ports' shared symbol map: the adjoint loop emits `uh`-images on the hold and
      -- the transfer maps them back with `un`, so the buffered stream is the same word.
      (ec : Bool → tm.Γ kin) (dc : tm.Γ kin → Bool)
      (es : Bool → tm.Γ ksrc) (ex : Bool → tm.Γ kxin) (eh : Bool → tm.Γ khld)
      (eo : Bool → tm.Γ ktok) (ei : Bool → tm.Γ kidx) (ef : Bool → tm.Γ kfu)
      (o1 : Bool → tm.Γ kpd1) (o2 : Bool → tm.Γ kpd2)
      (mq : tm.Γ kqc) (mfu : tm.Γ kfu) (msA : tm.Γ kscA) (msB : tm.Γ kscB)
      (c0 c1 c2 c3 c4 c5 c8 t6 t7 : tm.Γ kopc) (oc : ℕ → tm.Γ kopc) (rp : ℕ → ℕ)
      (uh : tm.Γ kopc → tm.Γ khld) (un : tm.Γ khld → tm.Γ kopc),
    -- (1) THE PORTS, THE ENTRY POINT, AND THE FOURTEEN DISTINCT STACKS.  One `Nodup` replaces
    -- every directed disequality the blocks demand between them.
    tm.k₀ = kin ∧ tm.k₁ = kbit ∧ tm.main = lS
  ∧ ([kin, ksrc, kxin, khld, kpd1, kpd2, kqc, kfu, ktok, kidx, kopc, kbit, kscA,
      kscB] : List tm.K).Nodup
    -- (2) THE INPUT DEMULTIPLEXER (`SPLIT`), entry `lS`, exit into the header parser `lF1`.
  ∧ (∃ (fT fP : tm.σ → Option (tm.Γ kin) → tm.σ) (gT gP gTag : tm.σ → Bool)
        (pL : tm.σ → tm.Γ kscA) (pR : tm.σ → tm.Γ kscB)
        (fl : tm.σ → Option (tm.Γ kscA) → tm.σ) (gl : tm.σ → Bool)
        (ql : tm.σ → tm.Γ ksrc)
        (fr : tm.σ → Option (tm.Γ kscB) → tm.σ) (gr : tm.σ → Bool)
        (qr : tm.σ → tm.Γ kxin)
        (hL : Bool → tm.Γ kscA) (hR : Bool → tm.Γ kscB),
      tm.m lS = Stmt.pop kin fT (Stmt.branch gT
          (Stmt.pop kin fP (Stmt.branch gP
            (Stmt.branch gTag (Stmt.push kscB pR (Stmt.goto (fun _ => lT)))
              (Stmt.push kscA pL (Stmt.goto (fun _ => lS))))
            (Stmt.goto (fun _ => lDL))))
          (Stmt.goto (fun _ => lDL)))
    ∧ tm.m lT = Stmt.pop kin fT (Stmt.branch gT
          (Stmt.pop kin fP (Stmt.branch gP
            (Stmt.branch gTag (Stmt.push kscB pR (Stmt.goto (fun _ => lT)))
              (Stmt.goto (fun _ => lT)))
            (Stmt.goto (fun _ => lDL))))
          (Stmt.goto (fun _ => lDL)))
    ∧ tm.m lDL = Stmt.pop kscA fl (Stmt.branch gl
          (Stmt.push ksrc ql (Stmt.goto (fun _ => lDL))) (Stmt.goto (fun _ => lDR)))
    ∧ tm.m lDR = Stmt.pop kscB fr (Stmt.branch gr
          (Stmt.push kxin qr (Stmt.goto (fun _ => lDR))) (Stmt.goto (fun _ => lF1)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ kin), gT (fT v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gT (fT v Option.none) = false)
    ∧ (∀ (v : tm.σ) (y z : tm.Γ kin),
        gP (fP (fT v (Option.some y)) (Option.some z)) = true)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kin), gP (fP (fT v (Option.some y)) Option.none) = false)
    ∧ (∀ (v : tm.σ) (y z : tm.Γ kin),
        gTag (fP (fT v (Option.some y)) (Option.some z)) = dc y)
    ∧ (∀ (v : tm.σ) (y z : tm.Γ kin),
        pL (fP (fT v (Option.some y)) (Option.some z)) = hL (dc z))
    ∧ (∀ (v : tm.σ) (y z : tm.Γ kin),
        pR (fP (fT v (Option.some y)) (Option.some z)) = hR (dc z))
    ∧ (∀ b : Bool, dc (ec b) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kscA), gl (fl v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gl (fl v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), ql (fl v (Option.some (hL b))) = es b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kscB), gr (fr v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gr (fr v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qr (fr v (Option.some (hR b))) = ex b))
    -- (3) THE THREE-FIELD HEADER PARSER AND PADDED-INPUT BUILDER (`FIELDS`), entry `lF1`,
    -- REJECT ARM straight into the drain `ls 0`, exit into the tokeniser `lU`.
  ∧ (∃ (fs : tm.σ → Option (tm.Γ ksrc) → tm.σ) (gs gb : tm.σ → Bool)
        (qp1 : tm.σ → tm.Γ kpd1) (qp2 : tm.σ → tm.Γ kpd2) (qq : tm.σ → tm.Γ kqc)
        (qf : tm.σ → tm.Γ kfu) (fx : tm.σ → Option (tm.Γ kxin) → tm.σ)
        (gx : tm.σ → Bool) (qh : tm.σ → tm.Γ khld)
        (fh : tm.σ → Option (tm.Γ khld) → tm.σ) (gh : tm.σ → Bool)
        (rp1 : tm.σ → tm.Γ kpd1) (rp2 : tm.σ → tm.Γ kpd2),
      tm.m lF1 = Stmt.pop ksrc fs (Stmt.branch gs
        (Stmt.branch gb
          (Stmt.push kpd1 qp1 (Stmt.push kpd2 qp2 (Stmt.goto (fun _ => lF1))))
          (Stmt.push kpd1 qp1 (Stmt.push kpd2 qp2 (Stmt.goto (fun _ => lF2)))))
        (Stmt.goto (fun _ => ls 0)))
    ∧ tm.m lF2 = Stmt.pop ksrc fs (Stmt.branch gs
        (Stmt.branch gb (Stmt.push kqc qq (Stmt.goto (fun _ => lF2)))
          (Stmt.goto (fun _ => lF3)))
        (Stmt.goto (fun _ => ls 0)))
    ∧ tm.m lF3 = Stmt.pop ksrc fs (Stmt.branch gs
        (Stmt.branch gb (Stmt.push kfu qf (Stmt.goto (fun _ => lF3)))
          (Stmt.goto (fun _ => lFA)))
        (Stmt.goto (fun _ => ls 0)))
    ∧ tm.m lFA = Stmt.pop kxin fx (Stmt.branch gx
        (Stmt.push khld qh (Stmt.goto (fun _ => lFA)))
        (Stmt.goto (fun _ => lFC)))
    ∧ tm.m lFC = Stmt.pop khld fh (Stmt.branch gh
        (Stmt.push kpd1 rp1 (Stmt.push kpd2 rp2 (Stmt.goto (fun _ => lFC))))
        (Stmt.goto (fun _ => lU)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), gs (fs v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gs (fs v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), gb (fs v (Option.some (es b))) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), qp1 (fs v (Option.some y)) = o1 false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), qp2 (fs v (Option.some y)) = o2 false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), qq (fs v (Option.some y)) = mq)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), qf (fs v (Option.some y)) = mfu)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kxin), gx (fx v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gx (fx v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qh (fx v (Option.some (ex b))) = eh b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ khld), gh (fh v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gh (fh v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), rp1 (fh v (Option.some (eh b))) = o1 b)
    ∧ (∀ (v : tm.σ) (b : Bool), rp2 (fh v (Option.some (eh b))) = o2 b))
    -- (4) THE FUELLED GATE-RECORD PARSER (`TOKENISE`), entry `lU`.  ITS EXIT IS NOW `lV0`,
    -- the scratch-trail drain -- the one change this phase needed, and it is free because the
    -- exit is the block theorem's bound parameter.
  ∧ (∃ (FF : tm.σ → Option (tm.Γ kfu) → tm.σ) (GF : tm.σ → Bool) (QB : tm.σ → tm.Γ kscA)
        (ft fi : tm.σ → Option (tm.Γ ksrc) → tm.σ) (GT GBT GI GBI cn : tm.σ → Bool)
        (QHt QHi : tm.σ → tm.Γ khld) (QMt QMi : tm.σ → tm.Γ kscA)
        (FC : tm.σ → Option (tm.Γ kscA) → tm.σ) (GCB : tm.σ → Bool)
        (FH fo : tm.σ → Option (tm.Γ khld) → tm.σ) (GO : tm.σ → Bool)
        (QO : tm.σ → tm.Γ ktok) (mk bd : tm.Γ kscA),
      tm.m lU = Stmt.pop kfu FF (Stmt.branch GF
        (Stmt.push kscA QB (Stmt.goto (fun _ => lTg)))
        (Stmt.goto (fun _ => lFin)))
    ∧ tm.m lTg = Stmt.pop ksrc ft (Stmt.branch GT
        (Stmt.push khld QHt (Stmt.push kscA QMt (Stmt.branch GBT
          (Stmt.goto (fun _ => lTg)) (Stmt.goto (fun _ => lJ1)))))
        (Stmt.goto (fun _ => lCl)))
    ∧ tm.m lJ1 = Stmt.pop ksrc fi (Stmt.branch GI
        (Stmt.push khld QHi (Stmt.push kscA QMi (Stmt.branch GBI
          (Stmt.goto (fun _ => lJ1)) (Stmt.goto (fun z => cond (cn z) lJ2 lU)))))
        (Stmt.goto (fun _ => lCl)))
    ∧ tm.m lJ2 = Stmt.pop ksrc fi (Stmt.branch GI
        (Stmt.push khld QHi (Stmt.push kscA QMi (Stmt.branch GBI
          (Stmt.goto (fun _ => lJ2)) (Stmt.goto (fun _ => lU)))))
        (Stmt.goto (fun _ => lCl)))
    ∧ tm.m lCl = Stmt.pop kscA FC (Stmt.branch GCB (Stmt.goto (fun _ => lFin))
        (Stmt.pop khld FH (Stmt.goto (fun _ => lCl))))
    ∧ tm.m lFin = Stmt.pop khld fo (Stmt.branch GO
        (Stmt.push ktok QO (Stmt.goto (fun _ => lFin)))
        (Stmt.goto (fun _ => lV0)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ kfu), GF (FF v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, GF (FF v Option.none) = false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kfu), QB (FF v (Option.some y)) = bd)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), GT (ft v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, GT (ft v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), GBT (ft v (Option.some (es b))) = b)
    ∧ (∀ (v : tm.σ) (b : Bool), QHt (ft v (Option.some (es b))) = eh b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), QMt (ft v (Option.some y)) = mk)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), GI (fi v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, GI (fi v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), GBI (fi v (Option.some (es b))) = b)
    ∧ (∀ (v : tm.σ) (b : Bool), QHi (fi v (Option.some (es b))) = eh b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), QMi (fi v (Option.some y)) = mk)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), cn (fi v (Option.some y)) = cn v)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kfu) (n : ℕ),
        cn (ft ((fun z => ft z (Option.some (es true)))^[n] (FF v (Option.some y)))
          (Option.some (es false))) = decide (n = 4))
    ∧ (∀ v : tm.σ, GCB (FC v (Option.some bd)) = true)
    ∧ (∀ v : tm.σ, GCB (FC v (Option.some mk)) = false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ khld), GO (fo v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, GO (fo v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), QO (fo v (Option.some (eh b))) = eo b))
    -- (5) THE SCRATCH-TRAIL DRAIN `lV0`, one label in the accepted single-stack drain's
    -- shape.  On the ACCEPTING path the tokeniser's rollback trail is never emptied -- it
    -- carries one mark per copied symbol PLUS one boundary per record -- and every gate-loop
    -- precondition needs that port empty.  Pairing the pop into the tokeniser's own last
    -- label is UNSOUND (the trail is longer than the hold by the record count) and would in
    -- any case change an accepted `Stmt`.
  ∧ (∃ (fd : tm.σ → Option (tm.Γ kscA) → tm.σ) (gd : tm.σ → Bool)
        (fs : tm.σ → Option (tm.Γ ksrc) → tm.σ) (gs2 : tm.σ → Bool)
        (ff : tm.σ → Option (tm.Γ kfu) → tm.σ) (gf : tm.σ → Bool),
      tm.m lV0 = Stmt.pop kscA fd (Stmt.branch gd
        (Stmt.goto (fun _ => lV0)) (Stmt.goto (fun _ => lSD)))
    ∧ tm.m lSD = Stmt.pop ksrc fs (Stmt.branch gs2
        (Stmt.goto (fun _ => lSD)) (Stmt.goto (fun _ => lFD)))
    ∧ tm.m lFD = Stmt.pop kfu ff (Stmt.branch gf
        (Stmt.goto (fun _ => lFD)) (Stmt.goto (fun _ => lV1)))
    ∧ (∀ (w : tm.σ) (y : tm.Γ kscA), gd (fd w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gd (fd w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ ksrc), gs2 (fs w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gs2 (fs w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kfu), gf (ff w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gf (ff w Option.none) = false))
    -- (6) DUPLICATOR 1, on the TOKEN stream: the forward loop eats the restored copy and the
    -- adjoint loop eats the second one.  One `Stmt` pops the hold and pushes on BOTH ports,
    -- so both copies come out FORWARD.
  ∧ (∃ (fv : tm.σ → Option (tm.Γ ktok) → tm.σ) (gv : tm.σ → Bool) (qv : tm.σ → tm.Γ khld)
        (fw : tm.σ → Option (tm.Γ khld) → tm.σ) (gw : tm.σ → Bool)
        (qt : tm.σ → tm.Γ ktok) (qx : tm.σ → tm.Γ kxin),
      tm.m lV1 = Stmt.pop ktok fv (Stmt.branch gv
        (Stmt.push khld qv (Stmt.goto (fun _ => lV1)))
        (Stmt.goto (fun _ => lV2)))
    ∧ tm.m lV2 = Stmt.pop khld fw (Stmt.branch gw
        (Stmt.push ktok qt (Stmt.push kxin qx (Stmt.goto (fun _ => lV2))))
        (Stmt.goto (fun _ => lVp)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ ktok), gv (fv v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gv (fv v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qv (fv v (Option.some (eo b))) = eh b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ khld), gw (fw v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gw (fw v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qt (fw v (Option.some (eh b))) = eo b)
    ∧ (∀ (v : tm.σ) (b : Bool), qx (fw v (Option.some (eh b))) = ex b))
    -- (7) DUPLICATOR 2, on the FIRST padded copy: the sweep tape and the FIRST zero-run
    -- counter.  The header parser prepares TWO padded copies and the word needs FOUR.
  ∧ (∃ (fv : tm.σ → Option (tm.Γ kpd1) → tm.σ) (gv : tm.σ → Bool) (qv : tm.σ → tm.Γ kin)
        (fw : tm.σ → Option (tm.Γ kin) → tm.σ) (gw : tm.σ → Bool)
        (qt : tm.σ → tm.Γ kpd1) (qx : tm.σ → tm.Γ kfu),
      tm.m lVp = Stmt.pop kpd1 fv (Stmt.branch gv
        (Stmt.push kin qv (Stmt.goto (fun _ => lVp)))
        (Stmt.goto (fun _ => lVq)))
    ∧ tm.m lVq = Stmt.pop kin fw (Stmt.branch gw
        (Stmt.push kpd1 qt (Stmt.push kfu qx (Stmt.goto (fun _ => lVq))))
        (Stmt.goto (fun _ => lL)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ kpd1), gv (fv v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gv (fv v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qv (fv v (Option.some (o1 b))) = ec b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kin), gw (fw v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gw (fw v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qt (fw v (Option.some (ec b))) = o1 b)
    ∧ (∀ (v : tm.σ) (b : Bool), qx (fw v (Option.some (ec b))) = ef b))
    -- (8) DUPLICATOR 3, on the SECOND padded copy: it RELOADS the sweep tape for the `E`
    -- sweep and lays the SECOND zero-run counter.  This is what lets ONE sweep instantiation
    -- serve both sweeps -- the predecessor needed two, and so carried nine unreachable
    -- labels purely to satisfy the unused half of each.
  ∧ (∃ (fv : tm.σ → Option (tm.Γ kpd2) → tm.σ) (gv : tm.σ → Bool) (qv : tm.σ → tm.Γ ksrc)
        (fw : tm.σ → Option (tm.Γ ksrc) → tm.σ) (gw : tm.σ → Bool)
        (qt : tm.σ → tm.Γ kpd1) (qx : tm.σ → tm.Γ kfu),
      tm.m lVr = Stmt.pop kpd2 fv (Stmt.branch gv
        (Stmt.push ksrc qv (Stmt.goto (fun _ => lVr)))
        (Stmt.goto (fun _ => lVs)))
    ∧ tm.m lVs = Stmt.pop ksrc fw (Stmt.branch gw
        (Stmt.push kpd1 qt (Stmt.push kfu qx (Stmt.goto (fun _ => lVs))))
        (Stmt.goto (fun _ => lW)))
    ∧ (∀ (v : tm.σ) (y : tm.Γ kpd2), gv (fv v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gv (fv v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qv (fv v (Option.some (o2 b))) = es b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ksrc), gw (fw v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gw (fw v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), qt (fw v (Option.some (es b))) = o1 b)
    ∧ (∀ (v : tm.σ) (b : Bool), qx (fw v (Option.some (es b))) = ef b))
    -- (9) THE TWO INPUT SWEEPS, THE TWO ZERO RUNS AND THE OUTPUT-WIRE MARKER, all on ONE
    -- tape port and ONE instantiation of the accepted sweep block.  PHASE ORDER IS WORD
    -- ORDER: the `L` sweep is FIRST and its zero run second; the marker sits BETWEEN the two
    -- block streams; the `E` sweep and its zero run come LAST before the reversal.  The
    -- predecessor emitted the two sweeps adjacently and the marker first, which no choice of
    -- sweep function can repair.
  ∧ (∃ (fLa : tm.σ → Option (tm.Γ kpd1) → tm.σ) (gLa : tm.σ → Bool) (dLa : tm.σ → tm.Λ)
        (fEa : tm.σ → Option (tm.Γ kpd1) → tm.σ) (gEa : tm.σ → Bool) (dEa : tm.σ → tm.Λ)
        (fz : tm.σ → Option (tm.Γ kfu) → tm.σ) (gz : tm.σ → Bool)
        (fq : tm.σ → Option (tm.Γ kqc) → tm.σ) (gq : tm.σ → Bool)
        (sqa : tm.σ → tm.Γ kscA) (sqb : tm.σ → tm.Γ kscB)
        (fma : tm.σ → Option (tm.Γ kscA) → tm.σ) (gma : tm.σ → Bool)
        (fmb : tm.σ → Option (tm.Γ kscB) → tm.σ) (gmb : tm.σ → Bool),
      tm.m lL = Stmt.pop kpd1 fLa (Stmt.branch gLa
        (Stmt.goto dLa) (Stmt.goto (fun _ => lZa)))
    ∧ tm.m lL5 = Stmt.push kopc (fun _ => c5) (Stmt.goto (fun _ => lL1))
    ∧ tm.m lL1 = Stmt.push kopc (fun _ => c1) (Stmt.goto (fun _ => lL))
    ∧ tm.m lW = Stmt.pop kpd1 fEa (Stmt.branch gEa
        (Stmt.goto dEa) (Stmt.goto (fun _ => lZb)))
    ∧ tm.m lW8 = Stmt.push kopc (fun _ => c8) (Stmt.goto (fun _ => lW1))
    ∧ tm.m lW1 = Stmt.push kopc (fun _ => c1) (Stmt.goto (fun _ => lW))
    ∧ tm.m lWa = Stmt.push kopc (fun _ => c5) (Stmt.goto (fun _ => lWb))
    ∧ tm.m lWb = Stmt.push kopc (fun _ => c8) (Stmt.goto (fun _ => lWc))
    ∧ tm.m lWc = Stmt.push kopc (fun _ => c5) (Stmt.goto (fun _ => lW1))
    ∧ tm.m lZa = Stmt.pop kfu fz (Stmt.branch gz
        (Stmt.push kopc (fun _ => c0) (Stmt.goto (fun _ => lZa)))
        (Stmt.goto (fun _ => lGT)))
    ∧ tm.m lZb = Stmt.pop kfu fz (Stmt.branch gz
        (Stmt.push kopc (fun _ => c0) (Stmt.goto (fun _ => lZb)))
        (Stmt.goto (fun _ => lGR)))
    ∧ tm.m lQX = Stmt.pop kqc fq (Stmt.branch gq
        (Stmt.push kscA sqa (Stmt.push kscB sqb (Stmt.goto (fun _ => lQX))))
        (Stmt.goto (fun _ => lPa)))
    ∧ tm.m lPa = Stmt.pop kscA fma (Stmt.branch gma
        (Stmt.push kopc (fun _ => c1) (Stmt.goto (fun _ => lPa)))
        (Stmt.goto (fun _ => lPm)))
    ∧ tm.m lPm = Stmt.push kopc (fun _ => c8) (Stmt.goto (fun _ => lPb))
    ∧ tm.m lPb = Stmt.pop kscB fmb (Stmt.branch gmb
        (Stmt.push kopc (fun _ => c0) (Stmt.goto (fun _ => lPb)))
        (Stmt.goto (fun _ => lGTz)))
    ∧ (∀ (w : tm.σ) (y : tm.Γ kpd1), gLa (fLa w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gLa (fLa w Option.none) = false)
    ∧ (∀ w : tm.σ, dLa (fLa w (Option.some (o1 true))) = lL5)
    ∧ (∀ w : tm.σ, dLa (fLa w (Option.some (o1 false))) = lL1)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kpd1), gEa (fEa w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gEa (fEa w Option.none) = false)
    ∧ (∀ w : tm.σ, dEa (fEa w (Option.some (o1 true))) = lW8)
    ∧ (∀ w : tm.σ, dEa (fEa w (Option.some (o1 false))) = lWa)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kfu), gz (fz w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gz (fz w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kqc), gq (fq w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gq (fq w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kqc), sqa (fq w (Option.some y)) = msA)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kqc), sqb (fq w (Option.some y)) = msB)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kscA), gma (fma w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gma (fma w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kscB), gmb (fmb w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gmb (fmb w Option.none) = false))
    -- (10) THE FORWARD GATE LOOP, ITS MIRRORED ONE-INDEX EMITTER AND ITS MIRRORED CNOT
    -- EMITTER, IN ONE EXISTENTIAL.  Bundling them is not cosmetic: the orientation bit set at
    -- `lXA`/`lXB`, preserved by the diagonal guard and read by the CNOT emitter is ONE
    -- register function, and the predecessor bound it TWICE, leaving that seam unpinned.  The
    -- opcode and repeat registers are likewise shared with the tag reader, which is what lets
    -- the last conjunct here SOURCE the emitter's opcode-and-repeat law from the wiring.
    -- MIRRORING: the index loops push the `1` nibble and the scratch drains the `0` nibble
    -- (the reverse of the adjoint loop), the two CNOT tag nibbles are exchanged, and the
    -- `i < j` exit takes the orientation bit `j < i` takes in the adjoint loop.  The net
    -- effect is that each record's contribution to the opcode port is the REVERSE of its
    -- forward block -- which, on a port whose list order is the reverse of the emitted word,
    -- is exactly the forward block in the forward slot.
  ∧ (∃ (rt : tm.σ → tm.σ) (pg : tm.σ → Option (tm.Γ ktok) → tm.σ)
        (gsv gbv : tm.σ → Bool) (dsp : tm.σ → tm.Λ) (sdf sdt : tm.σ → tm.σ)
        (dir : tm.σ → Bool) (pk : tm.σ → Option (tm.Γ kidx) → tm.σ)
        (pa : tm.σ → Option (tm.Γ kscA) → tm.σ) (bT bF bv : tm.σ → tm.Γ kidx)
        (aT aF : tm.σ → tm.Γ kscA) (ea : Bool → tm.Γ kscA) (tc : tm.σ → ℕ)
        (f₁ : tm.σ → Option (tm.Γ ktok) → tm.σ) (g₁ : tm.σ → Bool)
        (pscr : tm.σ → tm.Γ kscA) (pout ptag pone : tm.σ → tm.Γ kopc)
        (f₂ : tm.σ → Option (tm.Γ kscA) → tm.σ) (g₂ : tm.σ → Bool) (dec : tm.σ → tm.σ)
        (grep : tm.σ → Bool) (cnt : tm.σ → ℕ) (op : tm.σ → tm.Γ kopc)
        (e₁ : tm.σ → Option (tm.Γ kidx) → tm.σ) (h₁ : tm.σ → Bool)
        (e₂ : tm.σ → Option (tm.Γ kscA) → tm.σ) (h₂ : tm.σ → Bool)
        (e₃ : tm.σ → Option (tm.Γ kscB) → tm.σ) (h₃ : tm.σ → Bool)
        (qscr : tm.σ → tm.Γ kscA) (qscr2 : tm.σ → tm.Γ kscB)
        (qout qtag7 qtag6 qone qone2 : tm.σ → tm.Γ kopc)
        (fkt : tm.σ → Option (tm.Γ ktok) → tm.σ) (gkt : tm.σ → Bool),
      tm.m lGT = Stmt.load rt (Stmt.goto (fun _ => lTz))
    ∧ tm.m lTz = Stmt.pop ktok pg (Stmt.branch gsv
        (Stmt.branch gbv (Stmt.goto (fun _ => lTz)) (Stmt.goto dsp))
        (Stmt.goto (fun _ => lQX)))
    ∧ tm.m lXA = Stmt.load sdt (Stmt.goto (fun _ => lP1))
    ∧ tm.m lXB = Stmt.load sdf (Stmt.goto (fun _ => lQ1))
    ∧ (∀ v : tm.σ, dir (sdf v) = false) ∧ (∀ v : tm.σ, dir (sdt v) = true)
    ∧ tm.m lP1 = Stmt.pop kidx pk (Stmt.branch gbv
        (Stmt.push kscA aT (Stmt.goto (fun _ => lP1)))
        (Stmt.push kscA aF (Stmt.goto (fun _ => lP2))))
    ∧ tm.m lP2 = Stmt.pop kidx pk (Stmt.branch gbv
        (Stmt.push kidx bT (Stmt.goto (fun _ => lP3)))
        (Stmt.push kidx bF (Stmt.goto (fun _ => lP4))))
    ∧ tm.m lP3 = Stmt.pop kscA pa (Stmt.branch gsv
        (Stmt.push kidx bv (Stmt.goto (fun _ => lP3))) (Stmt.goto (fun _ => lQ1)))
    ∧ tm.m lP4 = Stmt.pop kscA pa (Stmt.branch gsv
        (Stmt.push kidx bv (Stmt.goto (fun _ => lP4))) (Stmt.goto (fun _ => lSK)))
    ∧ tm.m lSK = Stmt.pop kidx pk (Stmt.branch gsv
        (Stmt.goto (fun _ => lSK)) (Stmt.goto (fun _ => lGT)))
    ∧ tm.m lSKT = Stmt.pop ktok fkt (Stmt.branch gkt
        (Stmt.goto (fun _ => lSKT)) (Stmt.goto (fun _ => lGT)))
    ∧ (∀ (w : tm.σ) (b : Bool), gkt (fkt w (Option.some (eo b))) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ ktok), gsv (pg v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pg v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), gbv (pg v (Option.some (eo b))) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kidx), gsv (pk v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pk v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), gbv (pk v (Option.some (ei b))) = b)
    ∧ (∀ v : tm.σ, bT v = ei true) ∧ (∀ v : tm.σ, bF v = ei false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kscA), gsv (pa v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pa v Option.none) = false)
    ∧ (∀ v : tm.σ, aT v = ea true) ∧ (∀ v : tm.σ, aF v = ea false)
    ∧ (∀ (v : tm.σ) (b : Bool), bv (pa v (Option.some (ea b))) = ei b)
    -- THE TAG COUNTER AND THE DISPATCH.  The increment law is stated under the CAP the
    -- machine actually realises; it is FALSE without that guard.
    ∧ (∀ v : tm.σ, tc (rt v) = 0)
    ∧ (∀ v : tm.σ, tc v < 7 → tc (pg v (Option.some (eo true))) = tc v + 1)
    ∧ (∀ v : tm.σ, tc (pg v (Option.some (eo false))) = tc v)
    ∧ (∀ v : tm.σ, tc v < 4 → dsp v = lN1)
    ∧ (∀ v : tm.σ, tc v = 4 → dsp v = lA)
    -- THE SKIP ARM AND THE TOTALITY OF THE DISPATCH.  The accumulator saturates at seven,
    -- so `5 ≤ tc v` holds exactly when the true tag is four-or-more AND not four, which is
    -- exactly the set of records the renderer sends to the EMPTY block.  With this arm the
    -- dispatch is total into three labels and no caller needs a tag side condition.
    ∧ (∀ v : tm.σ, 5 ≤ tc v → dsp v = lSKT)
    ∧ (∀ v : tm.σ, dsp v = lN1 ∨ dsp v = lA ∨ dsp v = lSKT)
    -- THE GUARD AND THE TAG READER BOTH PRESERVE THE ORIENTATION BIT.
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ kidx)), dir (pk v o) = dir v)
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ kscA)), dir (pa v o) = dir v)
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ ktok)), dir (pg v o) = dir v)
    -- THE MIRRORED ONE-INDEX EMITTER
    ∧ tm.m lN1 = Stmt.pop ktok f₁ (Stmt.branch g₁
        (Stmt.push kscA pscr (Stmt.push kopc pout (Stmt.goto (fun _ => lN1))))
        (Stmt.goto (fun _ => lN2)))
    ∧ tm.m lN2 = Stmt.push kopc ptag (Stmt.load dec (Stmt.branch grep
        (Stmt.goto (fun _ => lN2)) (Stmt.goto (fun _ => lN3))))
    ∧ tm.m lN3 = Stmt.pop kscA f₂ (Stmt.branch g₂
        (Stmt.push kopc pone (Stmt.goto (fun _ => lN3)))
        (Stmt.goto (fun _ => lGT)))
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (eo true))) = true)
    ∧ (∀ w : tm.σ, pscr (f₁ w (Option.some (eo true))) = msA)
    ∧ (∀ w : tm.σ, pout (f₁ w (Option.some (eo true))) = c1)
    ∧ (∀ w : tm.σ, ptag w = op w)
    ∧ (∀ w : tm.σ, op (dec w) = op w)
    ∧ (∀ w : tm.σ, cnt (dec w) = cnt w - 1)
    ∧ (∀ w : tm.σ, 0 < cnt w → grep w = true)
    ∧ (∀ w : tm.σ, cnt w = 0 → grep w = false)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ ktok)), cnt (f₁ w o) = cnt w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ ktok)), op (f₁ w o) = op w)
    ∧ (∀ w : tm.σ, g₂ (f₂ w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, g₂ (f₂ w Option.none) = false)
    ∧ (∀ w : tm.σ, pone (f₂ w (Option.some msA)) = c0)
    -- THE MIRRORED CNOT EMITTER, sharing `dir` with the guard above
    ∧ tm.m lQ1 = Stmt.pop kidx e₁ (Stmt.branch h₁
        (Stmt.push kscA qscr (Stmt.push kopc qout (Stmt.goto (fun _ => lQ1))))
        (Stmt.goto (fun w => cond (dir w) lQ7 lQ2)))
    ∧ tm.m lQ7 = Stmt.push kopc qtag7 (Stmt.goto (fun w => cond (dir w) lQ2 lR2))
    ∧ tm.m lQ2 = Stmt.pop kidx e₁ (Stmt.branch h₁
        (Stmt.push kscB qscr2 (Stmt.push kopc qout (Stmt.goto (fun _ => lQ2))))
        (Stmt.goto (fun w => cond (dir w) lQ6 lQ7)))
    ∧ tm.m lQ6 = Stmt.push kopc qtag6 (Stmt.goto (fun w => cond (dir w) lR2 lR1))
    ∧ tm.m lR2 = Stmt.pop kscB e₃ (Stmt.branch h₃
        (Stmt.push kopc qone2 (Stmt.goto (fun _ => lR2)))
        (Stmt.goto (fun w => cond (dir w) lR1 lQ6)))
    ∧ tm.m lR1 = Stmt.pop kscA e₂ (Stmt.branch h₂
        (Stmt.push kopc qone (Stmt.goto (fun _ => lR1)))
        (Stmt.goto (fun _ => lGT)))
    ∧ (∀ w : tm.σ, h₁ (e₁ w (Option.some (ei true))) = true)
    ∧ (∀ w : tm.σ, h₁ (e₁ w (Option.some (ei false))) = false)
    ∧ (∀ w : tm.σ, qscr (e₁ w (Option.some (ei true))) = msA)
    ∧ (∀ w : tm.σ, qscr2 (e₁ w (Option.some (ei true))) = msB)
    ∧ (∀ w : tm.σ, qout (e₁ w (Option.some (ei true))) = c1)
    ∧ (∀ w : tm.σ, qtag7 w = t6) ∧ (∀ w : tm.σ, qtag6 w = t7)
    ∧ (∀ w : tm.σ, h₂ (e₂ w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, h₂ (e₂ w Option.none) = false)
    ∧ (∀ w : tm.σ, qone (e₂ w (Option.some msA)) = c0)
    ∧ (∀ w : tm.σ, h₃ (e₃ w (Option.some msB)) = true)
    ∧ (∀ w : tm.σ, h₃ (e₃ w Option.none) = false)
    ∧ (∀ w : tm.σ, qone2 (e₃ w (Option.some msB)) = c0)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kidx)), dir (e₁ w o) = dir w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kscA)), dir (e₂ w o) = dir w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kscB)), dir (e₃ w o) = dir w)
    -- THE OPCODE-AND-REPEAT LAW, SOURCED FROM THE WIRING.  The predecessor pushed the TAG as
    -- the opcode and never initialised the repeat field, so it emitted exactly one wrong
    -- nibble per record.  Here the tag reader's TERMINATOR pop loads both, with no `Stmt`
    -- change at all -- the FORWARD copy count is ONE at every tag, i.e. one nibble, which
    -- is `rp t + 1` at the forward renderer's identically-zero repeat table.
    ∧ (∀ (v : tm.σ) (t : ℕ), t < 4 → tc v = t →
        op (pg v (Option.some (eo false))) = oc t
      ∧ cnt (pg v (Option.some (eo false))) = 1))
    -- (11) THE FORWARD LOOP'S UNARY MIN/MAX SPLIT (`MINMAX`), entry `lA`.  UNMIRRORED: it
    -- emits unary INDEX marks, not opcode nibbles, so mirroring does not touch it -- only
    -- which orientation label it exits to, and that is already in (10).
  ∧ (∃ (f₁ : tm.σ → Option (tm.Γ ktok) → tm.σ) (g₁ : tm.σ → Bool)
        (fL : tm.σ → Option (tm.Γ kscA) → tm.σ) (gL : tm.σ → Bool)
        (fR : tm.σ → Option (tm.Γ kscB) → tm.σ) (gR : tm.σ → Bool)
        (pL : tm.σ → tm.Γ kscA) (pR : tm.σ → tm.Γ kscB)
        (pdel pmin : tm.σ → tm.Γ ktok) (pbk : tm.σ → tm.Γ kscA)
        (pdout pone : tm.σ → tm.Γ kidx),
      tm.m lA = Stmt.pop ktok f₁ (Stmt.branch g₁
        (Stmt.push kscA pL (Stmt.goto (fun _ => lA))) (Stmt.goto (fun _ => lB)))
    ∧ tm.m lB = Stmt.pop ktok f₁ (Stmt.branch g₁
        (Stmt.push kscB pR (Stmt.goto (fun _ => lB))) (Stmt.goto (fun _ => lC)))
    ∧ tm.m lC = Stmt.push ktok pdel (Stmt.goto (fun _ => lD))
    ∧ tm.m lD = Stmt.pop kscA fL (Stmt.branch gL
        (Stmt.goto (fun _ => lE)) (Stmt.goto (fun _ => lFa)))
    ∧ tm.m lE = Stmt.pop kscB fR (Stmt.branch gR
        (Stmt.push ktok pmin (Stmt.goto (fun _ => lD))) (Stmt.goto (fun _ => lFb)))
    ∧ tm.m lFa = Stmt.push kidx pdout (Stmt.goto (fun _ => lGa))
    ∧ tm.m lGa = Stmt.pop kscB fR (Stmt.branch gR
        (Stmt.push kidx pone (Stmt.goto (fun _ => lGa))) (Stmt.goto (fun _ => lHa)))
    ∧ tm.m lHa = Stmt.push kidx pdout (Stmt.goto (fun _ => lKa))
    ∧ tm.m lKa = Stmt.pop ktok f₁ (Stmt.branch g₁
        (Stmt.push kidx pone (Stmt.goto (fun _ => lKa))) (Stmt.goto (fun _ => lXA)))
    ∧ tm.m lFb = Stmt.push kscA pbk (Stmt.push kidx pdout (Stmt.goto (fun _ => lGb)))
    ∧ tm.m lGb = Stmt.pop kscA fL (Stmt.branch gL
        (Stmt.push kidx pone (Stmt.goto (fun _ => lGb))) (Stmt.goto (fun _ => lHb)))
    ∧ tm.m lHb = Stmt.push kidx pdout (Stmt.goto (fun _ => lKb))
    ∧ tm.m lKb = Stmt.pop ktok f₁ (Stmt.branch g₁
        (Stmt.push kidx pone (Stmt.goto (fun _ => lKb))) (Stmt.goto (fun _ => lXB)))
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (eo true))) = true)
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (eo false))) = false)
    ∧ (∀ w : tm.σ, gL (fL w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, gL (fL w Option.none) = false)
    ∧ (∀ w : tm.σ, gR (fR w (Option.some msB)) = true)
    ∧ (∀ w : tm.σ, gR (fR w Option.none) = false)
    ∧ (∀ w : tm.σ, pL (f₁ w (Option.some (eo true))) = msA)
    ∧ (∀ w : tm.σ, pR (f₁ w (Option.some (eo true))) = msB)
    ∧ (∀ w : tm.σ, pdel w = eo false)
    ∧ (∀ w : tm.σ, pmin (fR w (Option.some msB)) = eo true)
    ∧ (∀ w : tm.σ, pbk w = msA)
    ∧ (∀ w : tm.σ, pdout w = ei false)
    ∧ (∀ w : tm.σ, pone (fR w (Option.some msB)) = ei true)
    ∧ (∀ w : tm.σ, pone (fL w (Option.some msA)) = ei true)
    ∧ (∀ w : tm.σ, pone (f₁ w (Option.some (eo true))) = ei true))
    -- (12) THE ADJOINT GATE LOOP, ITS ONE-INDEX EMITTER AND ITS CNOT EMITTER, IN ONE
    -- EXISTENTIAL.  Reads the DUPLICATED token copy; emits NORMAL symbols INTO THE HOLD.  So
    -- its per-record contribution to the hold is the adjoint block itself, and the single
    -- reversing transfer of (14) then lays the whole adjoint stream on the opcode port in
    -- the ONE order that matches the target.  This asymmetry with (10) is forced: a
    -- prepending loop and a buffered-then-transferred loop contribute record orders that are
    -- reverses of each other, and the target needs one of each.
    -- The repeat table is the ADJOINT one, `rp = 0,2,6,0` at tags `0,1,2,3`, and the
    -- register holds the COPY COUNT `rp t + 1 = 1,3,7,1`, which is exactly what turns the
    -- adjoint `T` gate into seven nibbles and the adjoint `S` gate into three.
  ∧ (∃ (rt : tm.σ → tm.σ) (pg : tm.σ → Option (tm.Γ kxin) → tm.σ)
        (gsv gbv : tm.σ → Bool) (dsp : tm.σ → tm.Λ) (sdf sdt : tm.σ → tm.σ)
        (dir : tm.σ → Bool) (pk : tm.σ → Option (tm.Γ kidx) → tm.σ)
        (pa : tm.σ → Option (tm.Γ kscA) → tm.σ) (bT bF bv : tm.σ → tm.Γ kidx)
        (aT aF : tm.σ → tm.Γ kscA) (ea : Bool → tm.Γ kscA) (tc : tm.σ → ℕ)
        (f₁ : tm.σ → Option (tm.Γ kxin) → tm.σ) (g₁ : tm.σ → Bool)
        (pscr : tm.σ → tm.Γ kscA) (pout ptag pone : tm.σ → tm.Γ khld)
        (f₂ : tm.σ → Option (tm.Γ kscA) → tm.σ) (g₂ : tm.σ → Bool) (dec : tm.σ → tm.σ)
        (grep : tm.σ → Bool) (cnt : tm.σ → ℕ) (op : tm.σ → tm.Γ khld)
        (e₁ : tm.σ → Option (tm.Γ kidx) → tm.σ) (h₁ : tm.σ → Bool)
        (e₂ : tm.σ → Option (tm.Γ kscA) → tm.σ) (h₂ : tm.σ → Bool)
        (e₃ : tm.σ → Option (tm.Γ kscB) → tm.σ) (h₃ : tm.σ → Bool)
        (qscr : tm.σ → tm.Γ kscA) (qscr2 : tm.σ → tm.Γ kscB)
        (qout qtag7 qtag6 qone qone2 : tm.σ → tm.Γ khld)
        (fkt : tm.σ → Option (tm.Γ kxin) → tm.σ) (gkt : tm.σ → Bool),
      tm.m lGTz = Stmt.load rt (Stmt.goto (fun _ => lTzz))
    ∧ tm.m lTzz = Stmt.pop kxin pg (Stmt.branch gsv
        (Stmt.branch gbv (Stmt.goto (fun _ => lTzz)) (Stmt.goto dsp))
        (Stmt.goto (fun _ => lTR)))
    ∧ tm.m lXAz = Stmt.load sdf (Stmt.goto (fun _ => lP1z))
    ∧ tm.m lXBz = Stmt.load sdt (Stmt.goto (fun _ => lQ1z))
    ∧ (∀ v : tm.σ, dir (sdf v) = false) ∧ (∀ v : tm.σ, dir (sdt v) = true)
    ∧ tm.m lP1z = Stmt.pop kidx pk (Stmt.branch gbv
        (Stmt.push kscA aT (Stmt.goto (fun _ => lP1z)))
        (Stmt.push kscA aF (Stmt.goto (fun _ => lP2z))))
    ∧ tm.m lP2z = Stmt.pop kidx pk (Stmt.branch gbv
        (Stmt.push kidx bT (Stmt.goto (fun _ => lP3z)))
        (Stmt.push kidx bF (Stmt.goto (fun _ => lP4z))))
    ∧ tm.m lP3z = Stmt.pop kscA pa (Stmt.branch gsv
        (Stmt.push kidx bv (Stmt.goto (fun _ => lP3z))) (Stmt.goto (fun _ => lQ1z)))
    ∧ tm.m lP4z = Stmt.pop kscA pa (Stmt.branch gsv
        (Stmt.push kidx bv (Stmt.goto (fun _ => lP4z))) (Stmt.goto (fun _ => lSKz)))
    ∧ tm.m lSKz = Stmt.pop kidx pk (Stmt.branch gsv
        (Stmt.goto (fun _ => lSKz)) (Stmt.goto (fun _ => lGTz)))
    ∧ tm.m lSKTz = Stmt.pop kxin fkt (Stmt.branch gkt
        (Stmt.goto (fun _ => lSKTz)) (Stmt.goto (fun _ => lGTz)))
    ∧ (∀ (w : tm.σ) (b : Bool), gkt (fkt w (Option.some (ex b))) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kxin), gsv (pg v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pg v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), gbv (pg v (Option.some (ex b))) = b)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kidx), gsv (pk v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pk v Option.none) = false)
    ∧ (∀ (v : tm.σ) (b : Bool), gbv (pk v (Option.some (ei b))) = b)
    ∧ (∀ v : tm.σ, bT v = ei true) ∧ (∀ v : tm.σ, bF v = ei false)
    ∧ (∀ (v : tm.σ) (y : tm.Γ kscA), gsv (pa v (Option.some y)) = true)
    ∧ (∀ v : tm.σ, gsv (pa v Option.none) = false)
    ∧ (∀ v : tm.σ, aT v = ea true) ∧ (∀ v : tm.σ, aF v = ea false)
    ∧ (∀ (v : tm.σ) (b : Bool), bv (pa v (Option.some (ea b))) = ei b)
    ∧ (∀ v : tm.σ, tc (rt v) = 0)
    ∧ (∀ v : tm.σ, tc v < 7 → tc (pg v (Option.some (ex true))) = tc v + 1)
    ∧ (∀ v : tm.σ, tc (pg v (Option.some (ex false))) = tc v)
    ∧ (∀ v : tm.σ, tc v < 4 → dsp v = lN1z)
    ∧ (∀ v : tm.σ, tc v = 4 → dsp v = lAz)
    ∧ (∀ v : tm.σ, 5 ≤ tc v → dsp v = lSKTz)
    ∧ (∀ v : tm.σ, dsp v = lN1z ∨ dsp v = lAz ∨ dsp v = lSKTz)
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ kidx)), dir (pk v o) = dir v)
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ kscA)), dir (pa v o) = dir v)
    ∧ (∀ (v : tm.σ) (o : Option (tm.Γ kxin)), dir (pg v o) = dir v)
    ∧ tm.m lN1z = Stmt.pop kxin f₁ (Stmt.branch g₁
        (Stmt.push kscA pscr (Stmt.push khld pout (Stmt.goto (fun _ => lN1z))))
        (Stmt.goto (fun _ => lN2z)))
    ∧ tm.m lN2z = Stmt.push khld ptag (Stmt.load dec (Stmt.branch grep
        (Stmt.goto (fun _ => lN2z)) (Stmt.goto (fun _ => lN3z))))
    ∧ tm.m lN3z = Stmt.pop kscA f₂ (Stmt.branch g₂
        (Stmt.push khld pone (Stmt.goto (fun _ => lN3z)))
        (Stmt.goto (fun _ => lGTz)))
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (ex true))) = true)
    ∧ (∀ w : tm.σ, pscr (f₁ w (Option.some (ex true))) = msA)
    ∧ (∀ w : tm.σ, pout (f₁ w (Option.some (ex true))) = uh c0)
    ∧ (∀ w : tm.σ, ptag w = op w)
    ∧ (∀ w : tm.σ, op (dec w) = op w)
    ∧ (∀ w : tm.σ, cnt (dec w) = cnt w - 1)
    ∧ (∀ w : tm.σ, 0 < cnt w → grep w = true)
    ∧ (∀ w : tm.σ, cnt w = 0 → grep w = false)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kxin)), cnt (f₁ w o) = cnt w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kxin)), op (f₁ w o) = op w)
    ∧ (∀ w : tm.σ, g₂ (f₂ w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, g₂ (f₂ w Option.none) = false)
    ∧ (∀ w : tm.σ, pone (f₂ w (Option.some msA)) = uh c1)
    ∧ tm.m lQ1z = Stmt.pop kidx e₁ (Stmt.branch h₁
        (Stmt.push kscA qscr (Stmt.push khld qout (Stmt.goto (fun _ => lQ1z))))
        (Stmt.goto (fun w => cond (dir w) lQ7z lQ2z)))
    ∧ tm.m lQ7z = Stmt.push khld qtag7 (Stmt.goto (fun w => cond (dir w) lQ2z lR2z))
    ∧ tm.m lQ2z = Stmt.pop kidx e₁ (Stmt.branch h₁
        (Stmt.push kscB qscr2 (Stmt.push khld qout (Stmt.goto (fun _ => lQ2z))))
        (Stmt.goto (fun w => cond (dir w) lQ6z lQ7z)))
    ∧ tm.m lQ6z = Stmt.push khld qtag6 (Stmt.goto (fun w => cond (dir w) lR2z lR1z))
    ∧ tm.m lR2z = Stmt.pop kscB e₃ (Stmt.branch h₃
        (Stmt.push khld qone2 (Stmt.goto (fun _ => lR2z)))
        (Stmt.goto (fun w => cond (dir w) lR1z lQ6z)))
    ∧ tm.m lR1z = Stmt.pop kscA e₂ (Stmt.branch h₂
        (Stmt.push khld qone (Stmt.goto (fun _ => lR1z)))
        (Stmt.goto (fun _ => lGTz)))
    ∧ (∀ w : tm.σ, h₁ (e₁ w (Option.some (ei true))) = true)
    ∧ (∀ w : tm.σ, h₁ (e₁ w (Option.some (ei false))) = false)
    ∧ (∀ w : tm.σ, qscr (e₁ w (Option.some (ei true))) = msA)
    ∧ (∀ w : tm.σ, qscr2 (e₁ w (Option.some (ei true))) = msB)
    ∧ (∀ w : tm.σ, qout (e₁ w (Option.some (ei true))) = uh c0)
    ∧ (∀ w : tm.σ, qtag7 w = uh t7) ∧ (∀ w : tm.σ, qtag6 w = uh t6)
    ∧ (∀ w : tm.σ, h₂ (e₂ w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, h₂ (e₂ w Option.none) = false)
    ∧ (∀ w : tm.σ, qone (e₂ w (Option.some msA)) = uh c1)
    ∧ (∀ w : tm.σ, h₃ (e₃ w (Option.some msB)) = true)
    ∧ (∀ w : tm.σ, h₃ (e₃ w Option.none) = false)
    ∧ (∀ w : tm.σ, qone2 (e₃ w (Option.some msB)) = uh c1)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kidx)), dir (e₁ w o) = dir w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kscA)), dir (e₂ w o) = dir w)
    ∧ (∀ (w : tm.σ) (o : Option (tm.Γ kscB)), dir (e₃ w o) = dir w)
    ∧ (∀ (v : tm.σ) (t : ℕ), t < 4 → tc v = t →
        op (pg v (Option.some (ex false))) = uh (oc t)
      ∧ cnt (pg v (Option.some (ex false))) = rp t + 1))
    -- (13) THE ADJOINT LOOP'S UNARY MIN/MAX SPLIT, on the duplicated token copy.
  ∧ (∃ (f₁ : tm.σ → Option (tm.Γ kxin) → tm.σ) (g₁ : tm.σ → Bool)
        (fL : tm.σ → Option (tm.Γ kscA) → tm.σ) (gL : tm.σ → Bool)
        (fR : tm.σ → Option (tm.Γ kscB) → tm.σ) (gR : tm.σ → Bool)
        (pL : tm.σ → tm.Γ kscA) (pR : tm.σ → tm.Γ kscB)
        (pdel pmin : tm.σ → tm.Γ kxin) (pbk : tm.σ → tm.Γ kscA)
        (pdout pone : tm.σ → tm.Γ kidx),
      tm.m lAz = Stmt.pop kxin f₁ (Stmt.branch g₁
        (Stmt.push kscA pL (Stmt.goto (fun _ => lAz))) (Stmt.goto (fun _ => lBz)))
    ∧ tm.m lBz = Stmt.pop kxin f₁ (Stmt.branch g₁
        (Stmt.push kscB pR (Stmt.goto (fun _ => lBz))) (Stmt.goto (fun _ => lCz)))
    ∧ tm.m lCz = Stmt.push kxin pdel (Stmt.goto (fun _ => lDz))
    ∧ tm.m lDz = Stmt.pop kscA fL (Stmt.branch gL
        (Stmt.goto (fun _ => lEz)) (Stmt.goto (fun _ => lFaz)))
    ∧ tm.m lEz = Stmt.pop kscB fR (Stmt.branch gR
        (Stmt.push kxin pmin (Stmt.goto (fun _ => lDz))) (Stmt.goto (fun _ => lFbz)))
    ∧ tm.m lFaz = Stmt.push kidx pdout (Stmt.goto (fun _ => lGaz))
    ∧ tm.m lGaz = Stmt.pop kscB fR (Stmt.branch gR
        (Stmt.push kidx pone (Stmt.goto (fun _ => lGaz))) (Stmt.goto (fun _ => lHaz)))
    ∧ tm.m lHaz = Stmt.push kidx pdout (Stmt.goto (fun _ => lKaz))
    ∧ tm.m lKaz = Stmt.pop kxin f₁ (Stmt.branch g₁
        (Stmt.push kidx pone (Stmt.goto (fun _ => lKaz))) (Stmt.goto (fun _ => lXAz)))
    ∧ tm.m lFbz = Stmt.push kscA pbk (Stmt.push kidx pdout (Stmt.goto (fun _ => lGbz)))
    ∧ tm.m lGbz = Stmt.pop kscA fL (Stmt.branch gL
        (Stmt.push kidx pone (Stmt.goto (fun _ => lGbz))) (Stmt.goto (fun _ => lHbz)))
    ∧ tm.m lHbz = Stmt.push kidx pdout (Stmt.goto (fun _ => lKbz))
    ∧ tm.m lKbz = Stmt.pop kxin f₁ (Stmt.branch g₁
        (Stmt.push kidx pone (Stmt.goto (fun _ => lKbz))) (Stmt.goto (fun _ => lXBz)))
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (ex true))) = true)
    ∧ (∀ w : tm.σ, g₁ (f₁ w (Option.some (ex false))) = false)
    ∧ (∀ w : tm.σ, gL (fL w (Option.some msA)) = true)
    ∧ (∀ w : tm.σ, gL (fL w Option.none) = false)
    ∧ (∀ w : tm.σ, gR (fR w (Option.some msB)) = true)
    ∧ (∀ w : tm.σ, gR (fR w Option.none) = false)
    ∧ (∀ w : tm.σ, pL (f₁ w (Option.some (ex true))) = msA)
    ∧ (∀ w : tm.σ, pR (f₁ w (Option.some (ex true))) = msB)
    ∧ (∀ w : tm.σ, pdel w = ex false)
    ∧ (∀ w : tm.σ, pmin (fR w (Option.some msB)) = ex true)
    ∧ (∀ w : tm.σ, pbk w = msA)
    ∧ (∀ w : tm.σ, pdout w = ei false)
    ∧ (∀ w : tm.σ, pone (fR w (Option.some msB)) = ei true)
    ∧ (∀ w : tm.σ, pone (fL w (Option.some msA)) = ei true)
    ∧ (∀ w : tm.σ, pone (f₁ w (Option.some (ex true))) = ei true))
    -- (14) THE ADJOINT TRANSFER, one label in the accepted reversing-copy shape.  It is the
    -- FIRST of this machine's two uses of that primitive, and the reason the adjoint slot can
    -- be produced at all: a prepending loop cannot put the FIRST record's block leftmost.
  ∧ (∃ (ftr : tm.σ → Option (tm.Γ khld) → tm.σ) (gtr : tm.σ → Bool)
        (qtr : tm.σ → tm.Γ kopc),
      tm.m lTR = Stmt.pop khld ftr (Stmt.branch gtr
        (Stmt.push kopc qtr (Stmt.goto (fun _ => lTR)))
        (Stmt.goto (fun _ => lVr)))
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), gtr (ftr w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gtr (ftr w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), qtr (ftr w (Option.some y)) = un y))
    -- (15) THE ONE GLOBAL REVERSAL, the SECOND use of the same primitive.  Every emitter
    -- prepends and the expander carries the port's list order forward to the output wire, so
    -- the emitted word appears REVERSED at the wire; emitting in word order and turning the
    -- whole port round once here is what makes time order and word order agree, and it is
    -- also what reconciles the emitters' stack-order convention with the sweeps'.
  ∧ (∃ (fgr : tm.σ → Option (tm.Γ kopc) → tm.σ) (ggr : tm.σ → Bool)
        (qgr : tm.σ → tm.Γ khld),
      tm.m lGR = Stmt.pop kopc fgr (Stmt.branch ggr
        (Stmt.push khld qgr (Stmt.goto (fun _ => lGR)))
        (Stmt.goto (fun _ => lY)))
    ∧ (∀ (w : tm.σ) (y : tm.Γ kopc), ggr (fgr w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, ggr (fgr w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kopc), qgr (fgr w (Option.some y)) = uh y))
    -- (16) THE INLINED NIBBLE EXPANDER (`EXPAND`), entry `lY`, exit into the drain.  The
    -- reversal leaves the word on the HOLD and the opcode port empty, so the expander is
    -- hosted with its two nibble ports in exactly that arrangement -- the block is
    -- `∀`-quantified in all three stacks, so this costs nothing.
  ∧ (∃ (f : tm.σ → Option (tm.Γ khld) → tm.σ) (g : tm.σ → Bool)
        (fh : tm.σ → Option (tm.Γ kopc) → tm.σ) (gh : tm.σ → Bool)
        (p0 p1 p2 p3 : tm.σ → tm.Γ kopc) (q : tm.σ → tm.Γ kbit)
        (j : tm.Γ kopc → tm.Γ kbit) (q0 q1 q2 q3 : tm.Γ khld → tm.Γ kopc)
        (e : tm.Γ khld → List (tm.Γ kopc)),
      (∀ y : tm.Γ khld, e y = [q0 y, q1 y, q2 y, q3 y])
    ∧ tm.m lY = Stmt.pop khld f (Stmt.branch g
        (Stmt.goto (fun _ => lY0)) (Stmt.goto (fun _ => lYD)))
    ∧ tm.m lY0 = Stmt.push kopc p0 (Stmt.goto (fun _ => lY1))
    ∧ tm.m lY1 = Stmt.push kopc p1 (Stmt.goto (fun _ => lY2))
    ∧ tm.m lY2 = Stmt.push kopc p2 (Stmt.goto (fun _ => lY3))
    ∧ tm.m lY3 = Stmt.push kopc p3 (Stmt.goto (fun _ => lY))
    ∧ tm.m lYD = Stmt.pop kopc fh (Stmt.branch gh
        (Stmt.push kbit q (Stmt.goto (fun _ => lYD))) (Stmt.goto (fun _ => ls 0)))
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), g (f w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, g (f w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kopc), gh (fh w (Option.some y)) = true)
    ∧ (∀ w : tm.σ, gh (fh w Option.none) = false)
    ∧ (∀ (w : tm.σ) (y : tm.Γ kopc), q (fh w (Option.some y)) = j y)
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), p0 (f w (Option.some y)) = q0 y)
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), p1 (f w (Option.some y)) = q1 y)
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), p2 (f w (Option.some y)) = q2 y)
    ∧ (∀ (w : tm.σ) (y : tm.Γ khld), p3 (f w (Option.some y)) = q3 y))
    -- (17) THE FIXED-ORDER DRAIN AND THE `Stmt.load` RESET BEFORE HALT (`DRAIN`), thirteen
    -- stacks in a fixed `ℕ`-indexed order -- every stack except the output port -- with
    -- distinctness as ONE injectivity hypothesis, AND the SURJECTIVITY the halt-shape bridge
    -- needs, which the predecessor's consumer had to assume.
  ∧ (∃ (fp : ∀ i : ℕ, tm.σ → Option (tm.Γ (ks i)) → tm.σ) (gt : ℕ → tm.σ → Bool),
      (∀ (i : ℕ) (w : tm.σ) (y : tm.Γ (ks i)), gt i (fp i w (Option.some y)) = true)
    ∧ (∀ (i : ℕ) (w : tm.σ), gt i (fp i w Option.none) = false)
    ∧ (∀ i i' : ℕ, i < 13 → i' < 13 → i ≠ i' → ks i ≠ ks i')
    ∧ (∀ i : ℕ, i < 13 → ks i ≠ kbit)
    ∧ (∀ k : tm.K, k ≠ kbit → (∃ i : ℕ, i < 13 ∧ ks i = k))
    ∧ (∀ i : ℕ, i < 13 → tm.m (ls i) = Stmt.pop (ks i) (fp i)
        (Stmt.branch (gt i) (Stmt.goto (fun _ => ls i))
          (Stmt.goto (fun _ => ls (i + 1)))))
    ∧ tm.m (ls 13) = Stmt.load (fun _ => tm.initialState) (Stmt.goto (fun _ => lH))
    ∧ tm.m lH = Stmt.halt)
    -- (18) THE SEAM PACK IS NOT DEGENERATE: every shared encoder is injective on the two
    -- bits, the nine opcode nibbles the phases emit are PAIRWISE distinct (one `Nodup`, not
    -- a pack), and the two nibble ports' symbol map really is a bijection on the nose, so
    -- the buffered adjoint stream and the transferred one are the same word.
  ∧ (∀ a b : Bool, ec a = ec b → a = b) ∧ (∀ a b : Bool, es a = es b → a = b)
  ∧ (∀ a b : Bool, ex a = ex b → a = b) ∧ (∀ a b : Bool, eh a = eh b → a = b)
  ∧ (∀ a b : Bool, eo a = eo b → a = b) ∧ (∀ a b : Bool, ei a = ei b → a = b)
  ∧ (∀ a b : Bool, o1 a = o1 b → a = b) ∧ (∀ a b : Bool, o2 a = o2 b → a = b)
  ∧ ([c0, c1, c2, c3, c4, c5, t6, t7, c8] : List (tm.Γ kopc)).Nodup
  ∧ (∀ y : tm.Γ kopc, un (uh y) = y)
    -- (19) THE OPCODE TABLE.  The four one-index opcodes are the four DISTINCT nibbles the
    -- renderer demands, read off the tag, and they are the seam-pack symbols by name.
  ∧ (oc 0 = c2 ∧ oc 1 = c4 ∧ oc 2 = c3 ∧ oc 3 = c5
   ∧ rp 0 = 0 ∧ rp 1 = 2 ∧ rp 2 = 6 ∧ rp 3 = 0
   ∧ (∀ t : ℕ, rp t ≤ 6))
    -- (20) THE UNIVERSAL FRAME CLAUSE.  Every block's frame is stated as
    -- `∀ k, k ≠ a → k ≠ b → T k = S k`, which is worthless to a consumer who cannot tell
    -- that the fourteen named ports EXHAUST the stack index type.  They do, and with the
    -- `Nodup` of (1) that turns every block frame into a concrete twelve-equation transport,
    -- at every phase, with no per-theorem frame conjunct to omit.
  ∧ (∀ k : tm.K, k = kin ∨ k = ksrc ∨ k = kxin ∨ k = khld ∨ k = kpd1 ∨ k = kpd2
      ∨ k = kqc ∨ k = kfu ∨ k = ktok ∨ k = kidx ∨ k = kopc ∨ k = kbit ∨ k = kscA
      ∨ k = kscB)
    -- (21) NON-VACUITY, INSIDE THE THEOREM, WITH THE ALPHABETS FIXED CONCRETELY AND FINITE
    -- IN ALL OF `K`, `Λ` AND `σ`.  One hundred and twenty-six labels, fourteen stacks, a
    -- sixteen-value nibble alphabet on the two opcode-side ports and bits on the wires.
  ∧ (@Fintype.card tm.K tm.kFin = 14 ∧ @Fintype.card tm.Λ tm.ΛFin = 126
   ∧ Nonempty (tm.Γ kopc ≃ Fin 16) ∧ Nonempty (tm.Γ khld ≃ Fin 16)
   ∧ Nonempty (tm.Γ kin ≃ Bool) ∧ Nonempty (tm.Γ kbit ≃ Bool)
   ∧ (∃ q : tm.σ ≃ (Option Bool × Option (Fin 16) × Fin 8 × Fin 8 × Bool × Bool),
        q tm.initialState = (Option.none, Option.none, 0, 0, false, false))
   ∧ lS ≠ lH ∧ lGT ≠ lGTz ∧ lN1 ≠ lN1z ∧ lQ1 ≠ lQ1z ∧ lXA ≠ lXB ∧ lXAz ≠ lXBz
   ∧ lTR ≠ lGR ∧ lZa ≠ lZb ∧ lVp ≠ lVr ∧ lV0 ≠ lV1 ∧ lV0 ≠ lSD ∧ lSD ≠ lV1
   ∧ lSD ≠ lFD ∧ lFD ≠ lV1 ∧ lV0 ≠ lFD ∧ lSK ≠ lSKT ∧ lSKz ≠ lSKTz ∧ lSKT ≠ lSKTz
   ∧ lN1 ≠ lSKT ∧ lA ≠ lSKT ∧ lN1z ≠ lSKTz ∧ lAz ≠ lSKTz ∧ lL ≠ lW ∧ lPa ≠ lPb
   ∧ ls 0 ≠ lH) := by
  refine ⟨tmA, Stk.kin, Stk.ksrc, Stk.kxin, Stk.khld, Stk.kpd1, Stk.kpd2, Stk.kqc,
    Stk.kfu, Stk.ktok, Stk.kidx, Stk.kopc, Stk.kbit, Stk.kscA, Stk.kscB, ksF, lsF,
    Lbl.lS, Lbl.lT, Lbl.lDL, Lbl.lDR, Lbl.lF1, Lbl.lF2, Lbl.lF3, Lbl.lFA, Lbl.lFC,
    Lbl.lU, Lbl.lTg, Lbl.lJ1, Lbl.lJ2, Lbl.lCl, Lbl.lFin,
    Lbl.lV0, Lbl.lSD, Lbl.lFD, Lbl.lV1, Lbl.lV2, Lbl.lVp, Lbl.lVq,
    Lbl.lL, Lbl.lL5, Lbl.lL1, Lbl.lZa, Lbl.lGT, Lbl.lTz,
    Lbl.lN1, Lbl.lN2, Lbl.lN3, Lbl.lA, Lbl.lB, Lbl.lC, Lbl.lD, Lbl.lE, Lbl.lFa,
    Lbl.lGa, Lbl.lHa, Lbl.lKa, Lbl.lXA, Lbl.lFb, Lbl.lGb, Lbl.lHb, Lbl.lKb, Lbl.lXB,
    Lbl.lP1, Lbl.lP2, Lbl.lP3, Lbl.lP4, Lbl.lSK, Lbl.lSKT,
    Lbl.lQ1, Lbl.lQ7, Lbl.lQ2, Lbl.lQ6, Lbl.lR2, Lbl.lR1,
    Lbl.lQX, Lbl.lPa, Lbl.lPm, Lbl.lPb,
    Lbl.lGTz, Lbl.lTzz, Lbl.lN1z, Lbl.lN2z, Lbl.lN3z,
    Lbl.lAz, Lbl.lBz, Lbl.lCz, Lbl.lDz, Lbl.lEz, Lbl.lFaz, Lbl.lGaz, Lbl.lHaz,
    Lbl.lKaz, Lbl.lXAz, Lbl.lFbz, Lbl.lGbz, Lbl.lHbz, Lbl.lKbz, Lbl.lXBz,
    Lbl.lP1z, Lbl.lP2z, Lbl.lP3z, Lbl.lP4z, Lbl.lSKz, Lbl.lSKTz,
    Lbl.lQ1z, Lbl.lQ7z, Lbl.lQ2z, Lbl.lQ6z, Lbl.lR2z, Lbl.lR1z,
    Lbl.lTR, Lbl.lVr, Lbl.lVs,
    Lbl.lW, Lbl.lW8, Lbl.lW1, Lbl.lWa, Lbl.lWb, Lbl.lWc, Lbl.lZb, Lbl.lGR,
    Lbl.lY, Lbl.lY0, Lbl.lY1, Lbl.lY2, Lbl.lY3, Lbl.lYD, Lbl.lH,
    id, id, id, id, (fun b => if b then (1 : Fin 16) else 0), id, id, id, id, id,
    true, true, true, true,
    0, 1, 2, 3, 4, 5, 8, 6, 7, ocN, rpN, id, id,
    rfl, rfl, rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (2) SPLIT
  · refine ⟨pb, pp, gS, gS, gO, qb, qb, pb, gS, qb, pb, gS, qb, id, id, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
    · intro v y z
      cases y <;> rfl
  -- (3) FIELDS
  · refine ⟨pb, gS, gB, qF, qF, qT, qT, pb, gS, nb, pt, gN, qo, qo, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (4) TOKENISE, exiting into the scratch-trail drain
  · refine ⟨pfu, gS, qT, ptg, pb, gS, gB, gS, gB, gC, nb, nb, qF, qF, pb, gB, pt, pt,
      gN, qo, false, true, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
    · exact fun v y n => hcnA v y n
  -- (5) the scratch-trail drain, then the SOURCE drain, then the FUEL drain
  · refine ⟨pb, gS, pb, gS, pb, gS, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (6) duplicator 1, the token stream
  · refine ⟨pb, gS, nb, pt, gN, qo, qo, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (7) duplicator 2, the first padded copy
  · refine ⟨pb, gS, qb, pb, gS, qb, qb, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (8) duplicator 3, the second padded copy
  · refine ⟨pb, gS, qb, pb, gS, qb, qb, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (9) the two sweeps, the two zero runs and the marker
  · refine ⟨pb, gS, dLF, pb, gS, dEF, pb, gS, pb, gS, qT, qT, pb, gS, pb, gS, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (10) the forward gate loop with its mirrored emitters
  · refine ⟨rtg, pgF, gS, gB, dspF, sdF, sdT, gDir, pb, pb, qT, qF, qb, qT, qF, id,
      (fun v => ((v.2.2.1 : Fin 8) : ℕ)),
      pb, gB, qT, n1, ntg, n0, pb, gS, dcr, gRep, (fun v => (v.2.2.2.1 : ℕ)), ntg,
      pb, gB, pb, gS, pb, gS, qT, qT, n1, n6, n7, n0, n0, pb, gB, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
    -- the capped increment
    · intro v h
      have hlt : ((v.2.2.1 : Fin 8) : ℕ) < 7 := h
      have e : capT v.2.2.1 = (⟨((v.2.2.1 : Fin 8) : ℕ) + 1, by omega⟩ : Fin 8) :=
        dif_pos hlt
      exact congrArg Fin.val e
    -- the dispatch below four
    · intro v h
      have h' : ((v.2.2.1 : Fin 8) : ℕ) < 4 := h
      have hne : ¬ (v.2.2.1 = (4 : Fin 8)) := by
        intro hc
        rw [hc] at h'
        exact absurd h' (by decide)
      have h5 : ¬ (5 ≤ (v.2.2.1 : ℕ)) := by omega
      show (if v.2.2.1 = (4 : Fin 8) then Lbl.lA
          else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKT else Lbl.lN1) = Lbl.lN1
      rw [if_neg hne, if_neg h5]
    -- the dispatch at four
    · intro v h
      have h4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have he : v.2.2.1 = (4 : Fin 8) := Fin.val_injective (by rw [h4]; exact h)
      exact if_pos he
    -- the dispatch at five or more
    · intro v h
      have h' : 5 ≤ (v.2.2.1 : ℕ) := h
      have hne : ¬ (v.2.2.1 = (4 : Fin 8)) := by
        intro hc
        rw [hc] at h'
        exact absurd h' (by decide)
      show (if v.2.2.1 = (4 : Fin 8) then Lbl.lA
          else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKT else Lbl.lN1) = Lbl.lSKT
      rw [if_neg hne, if_pos h']
    -- the dispatch is TOTAL into the three arms
    · intro v
      by_cases hc : v.2.2.1 = (4 : Fin 8)
      · exact Or.inr (Or.inl (if_pos hc))
      · by_cases h5 : 5 ≤ (v.2.2.1 : ℕ)
        · refine Or.inr (Or.inr ?_)
          show (if v.2.2.1 = (4 : Fin 8) then Lbl.lA
              else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKT else Lbl.lN1) = Lbl.lSKT
          rw [if_neg hc, if_pos h5]
        · refine Or.inl ?_
          show (if v.2.2.1 = (4 : Fin 8) then Lbl.lA
              else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKT else Lbl.lN1) = Lbl.lN1
          rw [if_neg hc, if_neg h5]
    · intro w h
      exact decide_eq_true h
    · intro w h
      have h' : (w.2.2.2.1 : ℕ) = 0 := h
      exact decide_eq_false (by omega)
    -- the opcode-and-repeat law, sourced from the tag reader's terminator pop
    · intro v t ht htc
      exact ⟨hocA v.2.2.1 t ht htc, rfl⟩
  -- (11) the forward loop's min/max split
  · refine ⟨pb, gB, pb, gS, pb, gS, qT, qT, qF, qT, qT, qF, qT, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (12) the adjoint gate loop with its normal emitters, buffering into the hold
  · refine ⟨rtg, pgA, gS, gB, dspA, sdF, sdT, gDir, pb, pb, qT, qF, qb, qT, qF, id,
      (fun v => ((v.2.2.1 : Fin 8) : ℕ)),
      pb, gB, qT, n0, ntg, n1, pb, gS, dcr, gRep, (fun v => (v.2.2.2.1 : ℕ)), ntg,
      pb, gB, pb, gS, pb, gS, qT, qT, n0, n7, n6, n1, n1, pb, gB, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
    · intro v h
      have hlt : ((v.2.2.1 : Fin 8) : ℕ) < 7 := h
      have e : capT v.2.2.1 = (⟨((v.2.2.1 : Fin 8) : ℕ) + 1, by omega⟩ : Fin 8) :=
        dif_pos hlt
      exact congrArg Fin.val e
    · intro v h
      have h' : ((v.2.2.1 : Fin 8) : ℕ) < 4 := h
      have hne : ¬ (v.2.2.1 = (4 : Fin 8)) := by
        intro hc
        rw [hc] at h'
        exact absurd h' (by decide)
      have h5 : ¬ (5 ≤ (v.2.2.1 : ℕ)) := by omega
      show (if v.2.2.1 = (4 : Fin 8) then Lbl.lAz
          else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKTz else Lbl.lN1z) = Lbl.lN1z
      rw [if_neg hne, if_neg h5]
    · intro v h
      have h4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have he : v.2.2.1 = (4 : Fin 8) := Fin.val_injective (by rw [h4]; exact h)
      exact if_pos he
    · intro v h
      have h' : 5 ≤ (v.2.2.1 : ℕ) := h
      have hne : ¬ (v.2.2.1 = (4 : Fin 8)) := by
        intro hc
        rw [hc] at h'
        exact absurd h' (by decide)
      show (if v.2.2.1 = (4 : Fin 8) then Lbl.lAz
          else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKTz else Lbl.lN1z) = Lbl.lSKTz
      rw [if_neg hne, if_pos h']
    · intro v
      by_cases hc : v.2.2.1 = (4 : Fin 8)
      · exact Or.inr (Or.inl (if_pos hc))
      · by_cases h5 : 5 ≤ (v.2.2.1 : ℕ)
        · refine Or.inr (Or.inr ?_)
          show (if v.2.2.1 = (4 : Fin 8) then Lbl.lAz
              else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKTz else Lbl.lN1z) = Lbl.lSKTz
          rw [if_neg hc, if_pos h5]
        · refine Or.inl ?_
          show (if v.2.2.1 = (4 : Fin 8) then Lbl.lAz
              else if 5 ≤ (v.2.2.1 : ℕ) then Lbl.lSKTz else Lbl.lN1z) = Lbl.lN1z
          rw [if_neg hc, if_neg h5]
    · intro w h
      exact decide_eq_true h
    · intro w h
      have h' : (w.2.2.2.1 : ℕ) = 0 := h
      exact decide_eq_false (by omega)
    · intro v t ht htc
      exact ⟨hocA v.2.2.1 t ht htc, hrpAv v.2.2.1 t ht htc⟩
  -- (13) the adjoint loop's min/max split
  · refine ⟨pb, gB, pb, gS, pb, gS, qT, qT, qF, qT, qT, qF, qT, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (14) the adjoint transfer
  · refine ⟨pt, gN, nt, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (15) the one global reversal
  · refine ⟨pt, gN, nt, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (16) EXPAND, with the two nibble ports in the roles the reversal leaves them in
  · refine ⟨pt, gN, pt, gN, p0F, p1F, p2F, p3F, qjF, jF, q0F, q1F, q2F, q3F, eF, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
  -- (17) DRAIN
  · refine ⟨fpF, gtF, ?_⟩
    repeat' apply And.intro
    all_goals try (intros; first | rfl | (cases ‹Bool› <;> rfl))
    · exact hgTA
    · exact hgFA
    · exact hinjA
    · exact hbitA
    · exact hsurA
    · exact hdrA
  -- (18) the seam pack is not degenerate
  · intro a b h; exact h
  · intro a b h; exact h
  · intro a b h; exact h
  · intro a b h
    cases a <;> cases b <;> simp_all
  · intro a b h; exact h
  · intro a b h; exact h
  · intro a b h; exact h
  · intro a b h; exact h
  · decide
  · exact fun y => rfl
  -- (19) the opcode table
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro t
    match t with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | (_ + 4) => simp [rpN]
  -- (20) the fourteen ports exhaust the stack index type
  · decide
  -- (21) non-vacuity
  · refine ⟨rfl, rfl, ⟨Equiv.refl (Fin 16)⟩, ⟨Equiv.refl (Fin 16)⟩, ⟨Equiv.refl Bool⟩,
      ⟨Equiv.refl Bool⟩, ⟨Equiv.refl _, rfl⟩, ?_⟩
    repeat' apply And.intro
    all_goals decide

end BQPReferenceValidation.Source28

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate28
    let target ← getConstInfo ``ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate28
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch; axioms {axioms}"
