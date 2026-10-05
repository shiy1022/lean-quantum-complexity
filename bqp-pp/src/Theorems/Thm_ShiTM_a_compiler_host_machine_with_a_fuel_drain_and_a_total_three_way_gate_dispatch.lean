-- Isolated target snapshot from saved campaign metadata; NOT a proof.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

namespace ShiTM

theorem a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch :
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
  sorry

end ShiTM

