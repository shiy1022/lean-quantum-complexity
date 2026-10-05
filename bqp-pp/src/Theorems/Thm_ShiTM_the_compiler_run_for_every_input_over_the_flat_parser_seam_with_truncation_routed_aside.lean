-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

namespace ShiTM

theorem the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside
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
    (pr cr pb cb : ℕ)
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
    --    than silently assumed; where it fails the run is routed to `hBAD` below.
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
    -- THE SECOND UNDISCHARGED OBLIGATION, and the one `MACH-B4c` hid inside a false
    -- hypothesis: the NON-ACCEPTING PARSE.  It now covers TWO failures, not one, because the
    -- new seam has an explicit side condition the old one lacked.
    --  * ILL-FORMED TAG.  The parser returns `[t, i]` for every tag other than four; the
    --    renderer empties those blocks and the gate loop has no arm for them, so a record
    --    carrying a tag of five or more is not compiled by the accepting chain (RESUME 489).
    --  * TRUNCATION, NEW HERE.  When `((pg ng rest).1).length < ng` the declared gate count
    --    outruns the body and the record run stops short; conjunct (5) below exhibits such a
    --    stream.  The seam does not apply there either.
    -- Both are taken at the SAME free budget `pb * |w| + cb`, with `pb` and `cb` universally
    -- quantified so nothing about the run is prejudged -- same status, same shape and same
    -- packaging discipline as `hREJ`, and conjunct (1) stays unconditional on `∀ w`.
    (hBAD : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ¬ (((pg ng rest).1).length = ng
          ∧ (∀ rec ∈ (pg ng rest).1,
              (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]))) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (pb * w.length + cb)))
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
              (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
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
            (∀ r ∈ recs, (∃ t i : ℕ, t < 4 ∧ r = [t, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
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
    -- (3) ALL THREE BRANCHES REALLY DO FIT UNDER THE ONE BUDGET: the accepting run's
    -- composed cost, the reject run's and the ill-formed-tag run's are each dominated by the
    -- exhibited `f`, so the single affine bound of (1) is not achieved by making a branch
    -- vacuous.  With the seam replaced by the PROVED `FLAT-1b` (7) the accepting branch is
    -- the one that is now genuinely inhabited, and conjuncts (4) and (5) compute that.
  ∧ (∀ w : List Bool,
      pr * w.length + cr
        ≤ (128 + pr + pb) * w.length + 16 * (encCompile (unL w) (unR w)).length
            + (64 + cr + cb)
    ∧ pb * w.length + cb
        ≤ (128 + pr + pb) * w.length + 16 * (encCompile (unL w) (unR w)).length
            + (64 + cr + cb)
    ∧ 128 * w.length + 16 * (encCompile (unL w) (unR w)).length + 64
        ≤ (128 + pr + pb) * w.length
            + 16 * (encCompile (unL w) (unR w)).length + (64 + cr + cb))
    -- (4) THE ACCEPTING BRANCH IS REACHABLE, AND THIS IS COMPUTED, NOT ARGUED.  At the
    -- smallest non-degenerate flat witness -- `FLAT-1b` (8)'s canonical one-gate case,
    -- `anc = 0`, `out = 0`, third field one, body `[0, 0]`, the decode of
    -- `E [0, 0, 1, 0, 0]` -- the gate parser returns exactly one record `[0, 0]`.  So BOTH
    -- premises of the accepting branch hold simultaneously: the non-truncation side
    -- condition AND well-formedness.  The branch the three `hSHAPE` falsehoods made
    -- unreachable is therefore genuinely inhabited here.
  ∧ (((pg 1 [0, 0]).1).length = 1
      ∧ (∀ rec ∈ (pg 1 [0, 0]).1,
          (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])))
    -- (5) THE TRUNCATING CASE REALLY DOES ROUTE TO `hBAD`, ALSO COMPUTED.  `FLAT-1b` (9)'s
    -- witness: a third field of one over a ONE-token body parses to NO records at all, so
    -- the side condition fails and the conjunction `hBAD` negates is refuted -- which is
    -- exactly the form in which the non-accepting branch consumes it.  The new case the
    -- seam creates is thus discharged, not swept up.
  ∧ (pg 1 [0] = (([], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 1 [0]).1).length = 1
          ∧ (∀ rec ∈ (pg 1 [0]).1,
              (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])))) := by
  sorry

end ShiTM
