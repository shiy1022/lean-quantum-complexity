-- Isolated target snapshot from saved campaign metadata; NOT a proof.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

namespace ShiTM

theorem the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run
    -- THE HOST MACHINE.  `MACH-A5b` exhibits it existentially; a consumer obtains `tm`
    -- together with `tm.k₀ = kin` and `tm.k₁ = kbit` from its conjunct (1) and rewrites,
    -- which is why the input and output ports appear here as `tm.k₀` and `tm.k₁`.
    (tm : Turing.FinTM2)
    (ksrc kxin khld kpd1 kpd2 kqc kfu ktok kidx kopc kscA kscB : tm.K)
    -- `MACH-A5b` (1): the fourteen ports are pairwise distinct, as ONE `Nodup`.
    (hnd : ([tm.k₀, ksrc, kxin, khld, kpd1, kpd2, kqc, kfu, ktok, kidx, kopc, tm.k₁,
      kscA, kscB] : List tm.K).Nodup)
    -- `MACH-A5b` (20): the fourteen ports EXHAUST the stack index type.
    (hexh : ∀ k : tm.K, k = tm.k₀ ∨ k = ksrc ∨ k = kxin ∨ k = khld ∨ k = kpd1 ∨ k = kpd2
      ∨ k = kqc ∨ k = kfu ∨ k = ktok ∨ k = kidx ∨ k = kopc ∨ k = tm.k₁ ∨ k = kscA
      ∨ k = kscB)
    -- Only the three labels the weld actually names: the entry, the seam and the halt.
    (lS lGTz lH : tm.Λ)
    -- `MACH-A5b` (1) and (17): the entry label is the machine's `main`, and the exit label
    -- the drain's terminal `Stmt.load` goes to really is a `halt`.
    (hmain : tm.main = lS)
    (hhalt : tm.m lH = Stmt.halt)
    -- THE SEAM PACK, exactly the symbols `MACH-A5b` binds by name in its outermost
    -- existential, plus the opcode reader `oc` of its conjunct (19).
    (ec : Bool → tm.Γ tm.k₀) (ex : Bool → tm.Γ kxin)
    (eo : Bool → tm.Γ ktok) (ef : Bool → tm.Γ kfu)
    (o1 : Bool → tm.Γ kpd1) (o2 : Bool → tm.Γ kpd2)
    (c0 c1 c8 : tm.Γ kopc) (oc : ℕ → tm.Γ kopc)
    (uh : tm.Γ kopc → tm.Γ khld)
    (expn : tm.Γ khld → List (tm.Γ kopc)) (jb : tm.Γ kopc → tm.Γ tm.k₁)
    -- THE MACHINE-SIDE UNINTERPRETED FUNCTIONS the two chains are stated over.
    (unL unR : List Bool → List Bool) (E : List ℕ → List Bool)
    (tr : List (List ℕ) → List (tm.Γ kscA))
    (enc : List ℕ → List (tm.Γ ktok)) (encx : List ℕ → List (tm.Γ kxin))
    (blk blkA : List ℕ → List (tm.Γ kopc))
    (Lf Ef : List (tm.Γ kpd1) → List (tm.Γ kopc))
    -- THE TARGET-SIDE FUNCTIONS, i.e. the ones `COMPILE-STRcb`/`WELD-E` speak about.
    (unpack : List Bool → List ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
    (Lw Ew : List Bool → List ℕ) (blkN blkAN : List ℕ → List ℕ)
    (encb : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool)
    (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (pr cr : ℕ)
    -- THE OPCODE-READBACK GLUE.  Every symbol the phases emit on the opcode port is the
    -- `oc`-image of the natural number the renderer puts there.  These six equations are
    -- what turns the machine's symbol-level word into the target's `List ℕ` program; they
    -- are the seam `MACH-A5b` (19) pins by name on the emitters' side.
    (hLf : ∀ l : List Bool, Lf (l.map o1) = (Lw l).map oc)
    (hEf : ∀ l : List Bool, Ef (l.map o1) = (Ew l).map oc)
    (hblk : ∀ r : List ℕ, blk r = (blkN r).map oc)
    (hblkA : ∀ r : List ℕ, blkA r = (blkAN r).map oc)
    (hc0 : c0 = oc 0) (hc1 : c1 = oc 1) (hc8 : c8 = oc 8)
    -- THE WIRE GLUE.  The nibble expander followed by the output-port symbol map is the
    -- target's bit encoder, read through the output alphabet identification.  This is
    -- `EXPANDc`'s renderer clause at the two alphabets the machine actually uses.
    (hWIRE : ∀ P : List ℕ,
      (((P.map oc).map uh).flatMap expn).map jb = List.map eb.invFun (encb P))
    -- THE INPUT ALPHABET IDENTIFICATION: `WELD-E` feeds the machine `map ea.invFun w` and
    -- the front end reads `map ec w`.
    (hea : ∀ b : Bool, ea.invFun b = ec b)
    -- `COMPILE-STRcb` (3), verbatim as `WELD-E` states it, at the pair of decoders.
    (he : ∀ P : List ℕ, (encb P).length = 4 * P.length)
    (h3 : ∀ (s x : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack s = anc :: out :: ng :: rest →
      encCompile s x
        = encb (Lw (x ++ List.replicate (anc + 1) false)
            ++ (List.replicate (x.length + (anc + 1)) 0
            ++ ((((pg ng rest).1).map blkN).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pg ng rest).1).reverse).map blkAN).flatten
            ++ (Ew (x ++ List.replicate (anc + 1) false)
              ++ List.replicate (x.length + (anc + 1)) 0)))))))
    -- `PARSE-TOT`'s gate-parser equations, three of the six, taken as binders exactly as
    -- `FLAT-1b` takes them.  They are cited ONLY by the two witness computations (4) and (5);
    -- the chain itself needs no defining equation for `pg` at all.
    (pg0 : ∀ ts : List ℕ, pg 0 ts = ([], ts))
    (pg2 : ∀ t k : ℕ, pg (k + 1) [t] = ([], []))
    (pg4 : ∀ (t i k : ℕ) (rest : List ℕ), ¬ t = 4 →
      pg (k + 1) (t :: i :: rest) = ([t, i] :: (pg k rest).1, (pg k rest).2))
    -- THE PARSER SEAM, `FLAT-1b` (7) VERBATIM -- PROVED, NOT HYPOTHESISED, AND THE WHOLE
    -- POINT OF THIS RE-ISSUE.  It replaces `MACH-B4d`'s `hSHAPE`, which RESUME 487, 489 and
    -- 492 refuted three independent times.  Three differences carry the repair:
    --  * it is stated over the GATE parser `pg`, never the layer parser `pl`.  `pl` eats its
    --    per-layer length token and never re-emits it, so `(pl k ts).1.flatten` is a
    --    SUBSEQUENCE and not a prefix of `ts` -- falsehood number three, RESUME 492.
    --  * the third header block is `1^(recs.length)` with `recs = (pg ng rest).1`, and the
    --    non-truncation side condition `((pg ng rest).1).length = ng` is EXPLICIT rather
    --    than silently assumed; where it fails the run is composed in `keyT` below
    --    from `ROLLBACK`, which is the whole point of this re-issue.
    --  * the residue `tl` is existential, absorbing the unterminated trailing `true`-run the
    --    decoder discards -- falsehood number one, RESUME 487.
    -- It needs NO defining equation for `unL`: the seam is a fact about strings, so the
    -- splitter enters only as a name.
    (hSEAM : ∀ (unL : List Bool → List Bool) (w : List Bool) (anc out ng : ℕ)
        (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ((pg ng rest).1).length = ng →
      ∃ (recs : List (List ℕ)) (tl : List Bool),
        recs = (pg ng rest).1 ∧ recs.length = ng ∧
        unL w = List.replicate anc true ++ false :: (List.replicate out true ++ false ::
          (List.replicate recs.length true ++ false ::
            (E recs.flatten ++ tl))))
    -- THE ONE UNDISCHARGED OBLIGATION: the REJECT-PATH run.  On an input whose left half
    -- decodes to fewer than three fields the machine takes the header parser's reject arm
    -- into the drain and halts with the output port empty, and `COMPILE-STRcb` (4) says the
    -- compiler is empty there too.  No banked theorem covers that run; `pr` and `cr` are
    -- universally quantified so its cost is not prejudged.
    (hREJ : ∀ w : List Bool, ¬ (3 ≤ (unpack (unL w)).length) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (pr * w.length + cr)))
    -- ELEMENTARY DECODER BUDGETS.  Neither half of a tagged pair is longer than the pair.
    (hunLl : ∀ w : List Bool, (unL w).length ≤ w.length)
    (hunRl : ∀ w : List Bool, (unR w).length ≤ w.length)
    -- THE ROLLBACK TRAIL IS LINEAR IN THE TOKEN STREAM AND THE RECORD COUNT: one mark per
    -- copied symbol plus one boundary per record.  Without it the front half's drain cost
    -- is unbounded in the input.
    (htr : ∀ rs : List (List ℕ),
      (tr rs).length ≤ (E rs.flatten).length + rs.length)
    -- `ShiTM.initList_haltList_laws` (the initial half) and
    -- `ShiTM.outputsInTime_of_run_to_halt` (1), both accepted, taken as hypotheses because
    -- this file imports nothing but `Mathlib.Computability.TuringMachine.Computable`.
    (hIL : ∀ s : List (tm.Γ tm.k₀),
      (Turing.initList tm s).l = Option.some tm.main
      ∧ (Turing.initList tm s).var = tm.initialState
      ∧ (Turing.initList tm s).stk tm.k₀ = s
      ∧ (∀ k : tm.K, k ≠ tm.k₀ → (Turing.initList tm s).stk k = []))
    (hOIT : ∀ (inp : List (tm.Γ tm.k₀)) (out : List (tm.Γ tm.k₁)) (lfin : tm.Λ)
        (S : ∀ k, List (tm.Γ k)) (N : ℕ),
      tm.m lfin = Stmt.halt →
      (fun cf : Option (Cfg tm.Γ tm.Λ tm.σ) => cf.bind (step tm.m))^[N]
          (Option.some (Turing.initList tm inp))
        = Option.some (⟨Option.some lfin, tm.initialState, S⟩ : Cfg tm.Γ tm.Λ tm.σ) →
      S tm.k₁ = out → (∀ k, k ≠ tm.k₁ → S k = []) →
      Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (N + 1)))
    (hgl : ∀ rs : List (List ℕ), (E rs.flatten).map eo = (rs.map enc).flatten)
    (hglx : ∀ rs : List (List ℕ), (E rs.flatten).map ex = (rs.map encx).flatten)
    -- `MACH-B4a`'s nine phase-run hypotheses and `MACH-B4b`'s eight (plus the symbol-map
    -- cancellation and the two drain-order clauses) are NOT binders here: `hA` and `hB`
    -- below are those two theorems ALREADY APPLIED to them, which is the form in which a
    -- consumer holding the accepted block theorems at this machine produces them.  Carrying
    -- them here as well would leave twenty binders this proof never touches.
    -- `MACH-B4a` CONJUNCT (1), applied to its nine phase-run hypotheses.  Its
    -- ninety-one stack disequalities and its exhaustion clause are kept as binders and
    -- discharged below from `MACH-A5b` (1) and (20).
    -- =================================================================================
    -- EVERYTHING FROM HERE TO `hA` IS WHAT `MACH-B4f` ADDS TO `MACH-B4e`: the labels,
    -- symbols and accepted block specifications the machine's OWN truncating path runs
    -- through, so that `MACH-B4e`'s `hBAD` becomes a THEOREM of this file.
    -- =================================================================================
    -- THE TWELVE INTERIOR LABELS the chain passes through between `lS` and `lGTz`.
    -- `lFD` is the fuel drain `MACH-A5d` added; it appears only on this branch.
    (lF1 lU lV0 lSD lFD lV1 lVp lL lZa lGT lQX lPa : tm.Λ)
    -- THE SOURCE ENCODER and the four block marks the interior phases use, taken by name
    -- from `MACH-A5b`'s outermost existential exactly as the seam pack above is.
    (es : Bool → tm.Γ ksrc) (eh : Bool → tm.Γ khld)
    (mfu : tm.Γ kfu) (mq : tm.Γ kqc)
    (msA : tm.Γ kscA) (msB : tm.Γ kscB)
    -- THE FIELD RENDERER'S TWO DEFINING EQUATIONS, `PARSE-TOT`'s, as `FLAT-1b` and
    -- `ROLLBACK` both take them.  `MACH-B4e` needed no equation for `E`; the truncating
    -- branch does, because it must split the source at the last complete record.
    (e0 : E [] = [])
    (e1 : ∀ (c : ℕ) (cs : List ℕ), E (c :: cs) = List.replicate c true ++ false :: E cs)
    -- THE THREE REMAINING GATE-PARSER EQUATIONS (`pg0`, `pg2`, `pg4` are above).  With all
    -- six present the shape and residue lemmas above apply, and with them the
    -- well-formedness disjunct is free and the rejecting tail is one of three shapes.
    (pg1 : ∀ k : ℕ, pg (k + 1) ([] : List ℕ) = ([], []))
    (pg3 : ∀ i k : ℕ, pg (k + 1) [4, i] = ([], []))
    (pg5 : ∀ (i j k : ℕ) (rest : List ℕ),
      pg (k + 1) (4 :: i :: j :: rest) = ([4, i, j] :: (pg k rest).1, (pg k rest).2))
    -- `FLAT-1b` (4): THE ONE-SIDED FUEL BOUND.  The record count never exceeds the third
    -- header field, so the negation of the non-truncation side condition really is
    -- `|recs| < ng` and not merely `|recs| <> ng`.
    (hLen : ∀ (k : ℕ) (ts : List ℕ), ((pg k ts).1).length ≤ k)
    -- `FLAT-1b`'s PRIVATE `flt_shape_gen`, PROVED THERE IN FULL GENERALITY from the four
    -- decoder equations and the two renderer equations, and exported only in the weaker,
    -- side-conditioned conjunct (7).  Every bit string is the rendering of its own decode
    -- followed by an unterminated run of ones, and that run is what the decoder discards
    -- (RESUME 487, 515, 552 -- its fourth appearance).  Re-exporting it is a one-conjunct
    -- re-issue of an accepted file; it is the ONLY parser-side thing this file assumes
    -- that is not already a banked conjunct.
    (hSHAPEg : ∀ s : List Bool, ∃ m : ℕ, s = E (unpack s) ++ List.replicate m true)
    -- (A) THE INPUT DEMULTIPLEXER, accepted, `lS` to `lF1`, in the form `MACH-B1` takes
    -- it: the paired input is split onto the two forward ports and the input port is left
    -- empty.
    (hSPLIT : ∀ (w : List Bool) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        S tm.k₀ = w.map ec → S kscA = [] → S kscB = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[w.length / 2
                + (unL w).length + (unR w).length + 3]
              (Option.some (⟨Option.some lS, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lF1, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T tm.k₀ = [] ∧ T kscA = [] ∧ T kscB = []
        ∧ T ksrc = (unL w).map es ++ S ksrc
        ∧ T kxin = (unR w).map ex ++ S kxin
        ∧ (∀ k, k ≠ tm.k₀ → k ≠ kscA → k ≠ kscB → k ≠ ksrc → k ≠ kxin → T k = S k))
    -- (B) THE THREE-FIELD HEADER PARSER AND PADDED-INPUT BUILDER, accepted, `lF1` to `lU`,
    -- with its third-field mark taken to be the record parser's fuel mark `mfu`.  Note the
    -- third field is laid down as `ng` marks -- the DECODED field, not a derived count --
    -- which is exactly why the truncating branch has fuel left over at the rollback exit.
    (hFIELDS : ∀ (anc out nl : ℕ) (rest x : List Bool) (v : tm.σ)
        (S : ∀ k, List (tm.Γ k)),
        S ksrc = (List.replicate anc true ++ false :: (List.replicate out true ++ false ::
          (List.replicate nl true ++ false :: rest))).map es →
        S kxin = x.map ex → S khld = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[anc + out + nl
                + 2 * x.length + 5]
              (Option.some (⟨Option.some lF1, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lU, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T ksrc = rest.map es ∧ T kxin = [] ∧ T khld = []
        ∧ T kqc = List.replicate out mq ++ S kqc
        ∧ T kfu = List.replicate nl mfu ++ S kfu
        ∧ T kpd1 = (x ++ List.replicate (anc + 1) false).map o1 ++ S kpd1
        ∧ T kpd2 = (x ++ List.replicate (anc + 1) false).map o2 ++ S kpd2
        ∧ (∀ k, k ≠ ksrc → k ≠ kxin → k ≠ khld → k ≠ kqc → k ≠ kfu → k ≠ kpd1 →
              k ≠ kpd2 → T k = S k))
    -- (C) THE PARSE LOOP WITH THE ROLLBACK TRAIL IN ITS FRAME.  THIS IS THE ONE GENUINELY
    -- OPEN RUN OBLIGATION OF THIS FILE, and it is carried by name rather than absorbed:
    -- it is `TOKENISEb` (1) verbatim plus the single conjunct `T kscA = tr recs ++ S kscA`
    -- (`loopMany` and `recStep` push the trail but drop the trail port from their frame).
    -- It is being built in parallel as `PARSEKC`; `MACH-B4a3`'s `hFRONT` already assumes
    -- the same `tr recs`, so it is SHARED with the accepting branch, not new work created
    -- here.
    (hPARSE : ∀ recs : List (List ℕ),
        (∀ rec ∈ recs,
          (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
        ∀ (x : List Bool) (fr : List (tm.Γ kfu)) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
          S ksrc = (E recs.flatten ++ x).map es →
          S kfu = List.replicate recs.length mfu ++ fr →
          ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
            (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[recs.length
                  + (E recs.flatten).length]
                (Option.some (⟨Option.some lU, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
              = Option.some (⟨Option.some lU, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
          ∧ T ksrc = x.map es
          ∧ T kfu = fr
          ∧ T khld = ((E recs.flatten).map eh).reverse ++ S khld
          ∧ T kscA = tr recs ++ S kscA
          ∧ (∀ k, k ≠ ksrc → k ≠ kfu → k ≠ khld → k ≠ kscA → T k = S k))
    -- (D) `ROLLBACK` (1), ACCEPTED (EXIT=0, 106s), STATED AS AN IMPLICATION FROM `hPARSE`
    -- SO THAT THE OPEN PART IS VISIBLE.  Its other five hypotheses ARE discharged:
    -- `hREJ` and `hFIN` by accepted `TOKREJ` (character for character, verified), and
    -- `hV0R`, `hSDR`, `hFDR` by three instantiations of accepted `LV0RUNb` at `kscA`,
    -- `ksrc` and the new `kfu` drain, whose wiring `MACH-A5d` supplies.  The exit is
    -- configuration-identical to the accepting exit at `lV1`: token port FORWARD, hold,
    -- trail, source and FUEL all empty.  `T kfu = []` is the whole truncation repair.
    (hROLL :
        (∀ recs : List (List ℕ),
          (∀ rec ∈ recs,
            (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
          ∀ (x : List Bool) (fr : List (tm.Γ kfu)) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
            S ksrc = (E recs.flatten ++ x).map es →
            S kfu = List.replicate recs.length mfu ++ fr →
            ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
              (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[recs.length
                    + (E recs.flatten).length]
                  (Option.some (⟨Option.some lU, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
                = Option.some (⟨Option.some lU, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
            ∧ T ksrc = x.map es
            ∧ T kfu = fr
            ∧ T khld = ((E recs.flatten).map eh).reverse ++ S khld
            ∧ T kscA = tr recs ++ S kscA
            ∧ (∀ k, k ≠ ksrc → k ≠ kfu → k ≠ khld → k ≠ kscA → T k = S k)) →
      ∀ (recs : List (List ℕ)) (bad : List ℕ) (n ng leftover : ℕ) (v : tm.σ)
        (S : ∀ k, List (tm.Γ k)),
        (∀ rec ∈ recs,
          (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
        (bad = [] ∨ (∃ t : ℕ, bad = [t]) ∨ (∃ i : ℕ, bad = [4, i])) →
        recs.length + 1 ≤ ng →
        ng = recs.length + leftover + 1 →
        S kfu = List.replicate ng mfu →
        S ksrc = (E (recs.flatten ++ bad) ++ List.replicate n true).map es →
        S khld = [] → S kscA = [] → S ktok = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[
                (recs.length + (E recs.flatten).length)
              + (2 * ((E bad).length + n) + 3)
              + ((E recs.flatten).length + 1)
              + ((tr recs).length + 1)
              + 1
              + (leftover + 1)]
              (Option.some (⟨Option.some lU, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lV1, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T ktok = (E ((pg ng (recs.flatten ++ bad)).1.flatten)).map eo
        ∧ T khld = []
        ∧ T kscA = []
        ∧ T ksrc = []
        ∧ T kfu = []
        ∧ (∀ P : (∀ k, List (tm.Γ k)) → Prop,
            (∀ A B : (∀ k, List (tm.Γ k)),
                (∀ k, k ≠ ksrc → k ≠ khld → k ≠ kfu → k ≠ ktok → k ≠ kscA → A k = B k) →
              P A → P B) → P S → P T))
    -- (E) DUPLICATOR 1, accepted, ON THE TOKEN STREAM, `lV1` to `lVp`.  `MACH-B4a3`'s
    -- phase (III), unchanged: this is where the two exits become one run.
    (hDUPtok : ∀ (bits : List Bool) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        S ktok = bits.map eo → S khld = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[2 * bits.length + 2]
              (Option.some (⟨Option.some lV1, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lVp, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T ktok = bits.map eo ∧ T kxin = bits.map ex ++ S kxin ∧ T khld = []
        ∧ (∀ k, k ≠ ktok → k ≠ khld → k ≠ kxin → T k = S k))
    -- (F) DUPLICATOR 2, `MACH-B4a3`'s phase (IV), at the first padded copy.
    (hDUPpad : ∀ (bits : List Bool) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        S kpd1 = bits.map o1 → S tm.k₀ = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[2 * bits.length + 2]
              (Option.some (⟨Option.some lVp, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lL, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T kpd1 = bits.map o1 ∧ T kfu = bits.map ef ++ S kfu ∧ T tm.k₀ = []
        ∧ (∀ k, k ≠ kpd1 → k ≠ tm.k₀ → k ≠ kfu → T k = S k))
    -- (G) THE `L` SWEEP, `MACH-B4a3`'s phase (V).
    (hLsw : ∀ (l : List (tm.Γ kpd1)), (∀ y ∈ l, y = o1 true ∨ y = o1 false) →
      ∀ (v : tm.σ) (S : ∀ k, List (tm.Γ k)), S kpd1 = l →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[l.length
                + (Lf l).length + 1]
              (Option.some (⟨Option.some lL, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lZa, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T kpd1 = [] ∧ T kopc = (Lf l).reverse ++ S kopc
        ∧ (∀ k, k ≠ kpd1 → k ≠ kopc → T k = S k))
    -- (H) THE FIRST ZERO RUN, `MACH-B4a3`'s phase (VI).  ITS LENGTH IS `(S kfu).length`,
    -- WHICH IS THE WHOLE OF RESUME 538 MODE (i): on the old machine the truncating branch
    -- arrived here with `leftover` extra marks still on `kfu` and emitted `leftover` extra
    -- zeroes.  `ROLLBACK` above now guarantees `T kfu = []` at `lV1`, so what this phase
    -- sees is exactly the padded copy the duplicator laid, and nothing else.
    (hZ1 : ∀ (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[(S kfu).length + 1]
              (Option.some (⟨Option.some lZa, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T kfu = [] ∧ T kopc = List.replicate (S kfu).length c0 ++ S kopc
        ∧ (∀ k, k ≠ kfu → k ≠ kopc → T k = S k))
    -- (I) THE MIRRORED FORWARD GATE LOOP, `MACH-B4a3`'s phase (VII), AT THE WEAKENED
    -- PREDICATE.  This is the one place where `MACH-A5d`'s second edit is consumed: at
    -- `MACH-A5c` this block holds only for `t < 4`, and accepted `SKIPRUN` is the run
    -- theorem for the `lSKT` arm that extends it to every tag.  The re-issue is not yet
    -- banked and is named in the header as the remaining cost.
    (hFWD : ∀ (recs : List (List ℕ)) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        (∀ r ∈ recs, (∃ t i : ℕ, ¬ t = 4 ∧ r = [t, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
        S ktok = (recs.map enc).flatten →
        S kidx = [] → S kscA = [] → S kscB = [] →
        ∃ (N : ℕ) (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          N ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length + 2
        ∧ (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[N]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lQX, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T ktok = [] ∧ T kidx = [] ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = ((recs.reverse.map (fun r => (blk r).reverse)).flatten ++ S kopc)
        ∧ (∀ k, k ≠ ktok → k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k))
    -- (J) THE OUTPUT-COUNT DUPLICATOR, `MACH-B4a3`'s phase (VIII).
    (hDUPq : ∀ (m : ℕ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        S kqc = List.replicate m mq → S kscA = [] → S kscB = [] →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[m + 1]
              (Option.some (⟨Option.some lQX, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lPa, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T kscA = List.replicate m msA ∧ T kscB = List.replicate m msB ∧ T kqc = []
        ∧ (∀ k, k ≠ kqc → k ≠ kscA → k ≠ kscB → T k = S k))
    -- (K) THE OUTPUT-WIRE MARKER, `MACH-B4a3`'s phase (IX), the weld's last step.
    (hMark : ∀ (m : ℕ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
        S kscA = List.replicate m msA → S kscB = List.replicate m msB →
        ∃ (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
          (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[2 * m + 3]
              (Option.some (⟨Option.some lPa, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
            = Option.some (⟨Option.some lGTz, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
        ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = List.replicate m c0 ++ (c8 :: (List.replicate m c1 ++ S kopc))
        ∧ (∀ k, k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k))
    (hA :
          tm.k₀ ≠ ksrc → tm.k₀ ≠ kxin → tm.k₀ ≠ khld → tm.k₀ ≠ kpd1 →
          tm.k₀ ≠ kpd2 → tm.k₀ ≠ kqc → tm.k₀ ≠ kfu → tm.k₀ ≠ ktok →
          tm.k₀ ≠ kidx → tm.k₀ ≠ kopc → tm.k₀ ≠ tm.k₁ → tm.k₀ ≠ kscA →
          tm.k₀ ≠ kscB → ksrc ≠ kxin → ksrc ≠ khld → ksrc ≠ kpd1 →
          ksrc ≠ kpd2 → ksrc ≠ kqc → ksrc ≠ kfu → ksrc ≠ ktok →
          ksrc ≠ kidx → ksrc ≠ kopc → ksrc ≠ tm.k₁ → ksrc ≠ kscA →
          ksrc ≠ kscB → kxin ≠ khld → kxin ≠ kpd1 → kxin ≠ kpd2 →
          kxin ≠ kqc → kxin ≠ kfu → kxin ≠ ktok → kxin ≠ kidx →
          kxin ≠ kopc → kxin ≠ tm.k₁ → kxin ≠ kscA → kxin ≠ kscB →
          khld ≠ kpd1 → khld ≠ kpd2 → khld ≠ kqc → khld ≠ kfu →
          khld ≠ ktok → khld ≠ kidx → khld ≠ kopc → khld ≠ tm.k₁ →
          khld ≠ kscA → khld ≠ kscB → kpd1 ≠ kpd2 → kpd1 ≠ kqc →
          kpd1 ≠ kfu → kpd1 ≠ ktok → kpd1 ≠ kidx → kpd1 ≠ kopc →
          kpd1 ≠ tm.k₁ → kpd1 ≠ kscA → kpd1 ≠ kscB → kpd2 ≠ kqc →
          kpd2 ≠ kfu → kpd2 ≠ ktok → kpd2 ≠ kidx → kpd2 ≠ kopc →
          kpd2 ≠ tm.k₁ → kpd2 ≠ kscA → kpd2 ≠ kscB → kqc ≠ kfu →
          kqc ≠ ktok → kqc ≠ kidx → kqc ≠ kopc → kqc ≠ tm.k₁ →
          kqc ≠ kscA → kqc ≠ kscB → kfu ≠ ktok → kfu ≠ kidx →
          kfu ≠ kopc → kfu ≠ tm.k₁ → kfu ≠ kscA → kfu ≠ kscB →
          ktok ≠ kidx → ktok ≠ kopc → ktok ≠ tm.k₁ → ktok ≠ kscA →
          ktok ≠ kscB → kidx ≠ kopc → kidx ≠ tm.k₁ → kidx ≠ kscA →
          kidx ≠ kscB → kopc ≠ tm.k₁ → kopc ≠ kscA → kopc ≠ kscB →
          tm.k₁ ≠ kscA → tm.k₁ ≠ kscB → kscA ≠ kscB →
          (∀ k : tm.K, k = tm.k₀ ∨ k = ksrc ∨ k = kxin ∨ k = khld ∨ k = kpd1 ∨ k = kpd2
            ∨ k = kqc ∨ k = kfu ∨ k = ktok ∨ k = kidx ∨ k = kopc ∨ k = tm.k₁ ∨ k = kscA
            ∨ k = kscB) →
        (∀ (w : List Bool) (anc out : ℕ) (recs : List (List ℕ)) (tl pad : List Bool)
            (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
            pad = unR w ++ List.replicate (anc + 1) false →
            unL w = List.replicate anc true ++ false :: (List.replicate out true ++ false ::
              (List.replicate recs.length true ++ false :: (E recs.flatten ++ tl))) →
            (∀ rec ∈ recs,
              (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
            S tm.k₀ = w.map ec → (∀ k, k ≠ tm.k₀ → S k = []) →
            ∃ (N : ℕ) (u : tm.σ) (T : ∀ k, List (tm.Γ k)),
              N ≤ w.length / 2 + (unL w).length + (unR w).length + 3
                    + (anc + out + recs.length + 2 * (unR w).length + 5)
                    + (2 * (E recs.flatten).length + recs.length + 2)
                  + ((tr recs).length + 1)
                  + (tl.length + 1)
                  + (2 * (E recs.flatten).length + 2)
                  + (2 * pad.length + 2)
                  + ((pad.map o1).length + (Lf (pad.map o1)).length + 1)
                  + ((pad.map ef).length + 1)
                  + (9 * ((recs.map enc).flatten).length + 26 * recs.length + 2)
                  + (out + 1)
                  + (2 * out + 3)
            ∧ (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[N]
                  (Option.some (⟨Option.some lS, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
                = Option.some (⟨Option.some lGTz, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
            ∧ T kxin = (recs.map encx).flatten
            ∧ T kpd2 = pad.map o2
            ∧ T kopc = List.replicate out c0 ++ (c8 :: (List.replicate out c1
                ++ ((recs.reverse.map (fun r => (blk r).reverse)).flatten
                  ++ (List.replicate pad.length c0 ++ (Lf (pad.map o1)).reverse))))
            ∧ (∀ k, k ≠ kxin → k ≠ kpd2 → k ≠ kopc → T k = [])))
    -- `MACH-B4b` CONJUNCT (1), applied to its eight phase-run hypotheses, with its
    -- terminal register instantiated at the machine's own initial state.
    (hB :
          tm.k₀ ≠ ksrc → tm.k₀ ≠ kxin → tm.k₀ ≠ khld → tm.k₀ ≠ kpd1 →
          tm.k₀ ≠ kpd2 → tm.k₀ ≠ kqc → tm.k₀ ≠ kfu → tm.k₀ ≠ ktok →
          tm.k₀ ≠ kidx → tm.k₀ ≠ kopc → tm.k₀ ≠ tm.k₁ → tm.k₀ ≠ kscA →
          tm.k₀ ≠ kscB → ksrc ≠ kxin → ksrc ≠ khld → ksrc ≠ kpd1 →
          ksrc ≠ kpd2 → ksrc ≠ kqc → ksrc ≠ kfu → ksrc ≠ ktok →
          ksrc ≠ kidx → ksrc ≠ kopc → ksrc ≠ tm.k₁ → ksrc ≠ kscA →
          ksrc ≠ kscB → kxin ≠ khld → kxin ≠ kpd1 → kxin ≠ kpd2 →
          kxin ≠ kqc → kxin ≠ kfu → kxin ≠ ktok → kxin ≠ kidx →
          kxin ≠ kopc → kxin ≠ tm.k₁ → kxin ≠ kscA → kxin ≠ kscB →
          khld ≠ kpd1 → khld ≠ kpd2 → khld ≠ kqc → khld ≠ kfu →
          khld ≠ ktok → khld ≠ kidx → khld ≠ kopc → khld ≠ tm.k₁ →
          khld ≠ kscA → khld ≠ kscB → kpd1 ≠ kpd2 → kpd1 ≠ kqc →
          kpd1 ≠ kfu → kpd1 ≠ ktok → kpd1 ≠ kidx → kpd1 ≠ kopc →
          kpd1 ≠ tm.k₁ → kpd1 ≠ kscA → kpd1 ≠ kscB → kpd2 ≠ kqc →
          kpd2 ≠ kfu → kpd2 ≠ ktok → kpd2 ≠ kidx → kpd2 ≠ kopc →
          kpd2 ≠ tm.k₁ → kpd2 ≠ kscA → kpd2 ≠ kscB → kqc ≠ kfu →
          kqc ≠ ktok → kqc ≠ kidx → kqc ≠ kopc → kqc ≠ tm.k₁ →
          kqc ≠ kscA → kqc ≠ kscB → kfu ≠ ktok → kfu ≠ kidx →
          kfu ≠ kopc → kfu ≠ tm.k₁ → kfu ≠ kscA → kfu ≠ kscB →
          ktok ≠ kidx → ktok ≠ kopc → ktok ≠ tm.k₁ → ktok ≠ kscA →
          ktok ≠ kscB → kidx ≠ kopc → kidx ≠ tm.k₁ → kidx ≠ kscA →
          kidx ≠ kscB → kopc ≠ tm.k₁ → kopc ≠ kscA → kopc ≠ kscB →
          tm.k₁ ≠ kscA → tm.k₁ ≠ kscB → kscA ≠ kscB →
          (∀ k : tm.K, k = tm.k₀ ∨ k = ksrc ∨ k = kxin ∨ k = khld ∨ k = kpd1 ∨ k = kpd2
            ∨ k = kqc ∨ k = kfu ∨ k = ktok ∨ k = kidx ∨ k = kopc ∨ k = tm.k₁ ∨ k = kscA
            ∨ k = kscB) →
        (∀ (recs : List (List ℕ)) (pad2 : List Bool) (pre bdy word : List (tm.Γ kopc))
            (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
            (∀ r ∈ recs, (∃ t i : ℕ, ¬ t = 4 ∧ r = [t, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
            bdy = (recs.reverse.map blkA).flatten →
            word = pre.reverse
                ++ (bdy ++ (Ef (pad2.map o1) ++ List.replicate pad2.length c0)) →
            S kxin = (recs.map encx).flatten →
            S kpd2 = pad2.map o2 →
            S kopc = pre →
            (∀ k, k ≠ kxin → k ≠ kpd2 → k ≠ kopc → S k = []) →
            ∃ (N : ℕ) (T : ∀ k, List (tm.Γ k)),
              N ≤ (9 * ((recs.map encx).flatten).length + 26 * recs.length + 2)
                  + (bdy.length + 1)
                  + (2 * pad2.length + 2)
                  + ((pad2.map o1).length + (Ef (pad2.map o1)).length + 1)
                  + ((pad2.map ef).length + 1)
                  + (word.length + 1)
                  + (9 * word.length + 2)
                  + 14
            ∧ (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[N]
                  (Option.some (⟨Option.some lGTz, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ))
                = Option.some (⟨Option.some lH, tm.initialState, T⟩ : Cfg tm.Γ tm.Λ tm.σ)
            ∧ T tm.k₁ = ((word.map uh).flatMap expn).map jb
            ∧ (∀ k : tm.K, k ≠ tm.k₁ → T k = []))) :

    -- (1) THE RUN, IN `WELD-E`'s SHAPE EXACTLY.  The machine's step count, the three
    -- coefficients, the machine, both alphabet identifications and every compiler-side
    -- function are exhibited or already universally quantified; `(hf)` is the first
    -- component and `(hbd)` the second, character for character as `WELD-E` (2) binds them.
    (∃ (f : List Bool → ℕ) (p q c : ℕ),
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (f w)))
    ∧ (∀ w : List Bool,
        f w ≤ p * w.length + q * (encCompile (unL w) (unR w)).length + c))
    -- (2) THE WORD IDENTITY, THE NEW CONTENT.  What the back half leaves on the wire, as a
    -- function of the front half's prefix, IS the `oc`-image of the target program, chunk
    -- for chunk and in the target's order: the load sweep, the leading zero run, the
    -- FORWARD block stream, the output-wire marker, the ADJOINT block stream, the store
    -- sweep and the trailing zero run.  The forward slot is the mirrored loop's per-record
    -- `(blk r).reverse` in reverse record order, turned round by the ONE global reversal;
    -- the adjoint slot is the buffered loop's, untouched.  Stated for every `pd`, `n`,
    -- `out` and `recs`, so nothing about the run is assumed.
  ∧ (∀ (pd : List Bool) (n out : ℕ) (recs : List (List ℕ)),
      (List.replicate out c0 ++ (c8 :: (List.replicate out c1
          ++ ((recs.reverse.map (fun r => (blk r).reverse)).flatten
            ++ (List.replicate n c0 ++ (Lf (pd.map o1)).reverse))))).reverse
        ++ (((recs.reverse).map blkA).flatten
          ++ (Ef (pd.map o1) ++ List.replicate n c0))
      = (Lw pd
          ++ (List.replicate n 0
          ++ ((recs.map blkN).flatten
          ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
          ++ (((recs.reverse).map blkAN).flatten
          ++ (Ew pd ++ List.replicate n 0)))))).map oc)
    -- (3) BOTH SURVIVING BRANCHES FIT UNDER THE ONE BUDGET.  `MACH-B4e` needed three
    -- clauses here, one of them for `hBAD`'s free budget `pb * |w| + cb`.  There are now
    -- TWO branches, not three: the header-reject run at its own free budget, and the
    -- COMPILING run -- accepting or truncating -- at the single composed budget, because
    -- `back` below shows the two share their whole tail.  No branch is made vacuous: the
    -- accepting branch is inhabited by conjunct (4), the truncating one by conjunct (6).
  ∧ (∀ w : List Bool,
      pr * w.length + cr
        ≤ (256 + pr) * w.length + 32 * (encCompile (unL w) (unR w)).length + (128 + cr)
    ∧ 256 * w.length + 32 * (encCompile (unL w) (unR w)).length + 128
        ≤ (256 + pr) * w.length
            + 32 * (encCompile (unL w) (unR w)).length + (128 + cr))
    -- (4) THE ACCEPTING BRANCH IS REACHABLE, COMPUTED, NOT ARGUED.  `FLAT-1b` (8)'s
    -- canonical one-gate witness: third field one, body `[0, 0]`, one record, so the
    -- non-truncation side condition holds and this stream takes the accepting chain.
  ∧ (pg 1 [0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ((pg 1 [0, 0]).1).length = 1)
    -- (5) REFUTATION-FIRST CHECK, MODE (ii) OF RESUME 538, AND THE POINT OF THE TAG-SKIP
    -- ARM.  `pg 1 [7, 0]` is a PARSED record whose tag is neither below four nor equal to
    -- four -- the exact stream on which `MACH-A5c` emitted a non-empty block where
    -- `RENDER-TOTb` demands an empty one.  It is NOT truncated, and it satisfies the
    -- weakened well-formedness predicate that `MACH-A5d`'s three-way dispatch supports,
    -- while REFUTING the old `t < 4` predicate.  So at the repaired machine this stream
    -- is on the ACCEPTING branch, and mode (ii) has no residue to route anywhere: the
    -- disjunct `MACH-B4e`'s `hBAD` existed to absorb is gone, not weakened.
  ∧ (pg 1 [7, 0] = (([[7, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ((pg 1 [7, 0]).1).length = 1
      ∧ (∀ rec ∈ (pg 1 [7, 0]).1,
          (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]))
      ∧ ¬ (∀ rec ∈ (pg 1 [7, 0]).1,
          (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])))
    -- (6) REFUTATION-FIRST CHECK, MODE (i), BOTH SUB-CASES, WITH THEIR FUEL PROFILES.
    -- `pg 2 [0]` completes NO record with two units of fuel, so `leftover = 1`: this is
    -- the witness that refuted the old `hBAD`, because the undrained unit lengthened the
    -- zero run by one.  `pg 2 [0, 0, 0]` completes one record and leaves `leftover = 0`:
    -- the BENIGN sub-case, the only truncating input anyone had ever looked at, and the
    -- reason the defect survived four rounds (RESUME 538's lesson).  Both satisfy
    -- `ROLLBACK`'s two fuel premises, written out here so neither can be mistaken for the
    -- other, and BOTH are handled by the SAME clause of the truncating branch.
  ∧ (pg 2 [0] = (([], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 2 [0]).1).length = 2)
      ∧ ((pg 2 [0]).1).length + 1 ≤ 2
      ∧ (2 : ℕ) = ((pg 2 [0]).1).length + 1 + 1
      ∧ pg 2 [0, 0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 2 [0, 0, 0]).1).length = 2)
      ∧ ((pg 2 [0, 0, 0]).1).length + 1 ≤ 2
      ∧ (2 : ℕ) = ((pg 2 [0, 0, 0]).1).length + 0 + 1)
    -- (7) WHY THE WELL-FORMEDNESS DISJUNCT IS FREE, AS A THEOREM RATHER THAN A REMARK.
    -- Every record the parser can return has one of the two shapes the repaired machine
    -- compiles, with the two-field arm guarded by `not t = 4` and NOT by `t < 4`.  This
    -- is the formal content of `MACH-A5d`'s dispatch totality on the compiler side: no
    -- caller needs a tag side condition, and `MACH-B4e`'s compound `hBAD` antecedent
    -- collapses to pure truncation, which is the single branch discharged above.
  ∧ (∀ (k : ℕ) (ts : List ℕ), ∀ rec ∈ (pg k ts).1,
      (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) := by
  sorry

end ShiTM

