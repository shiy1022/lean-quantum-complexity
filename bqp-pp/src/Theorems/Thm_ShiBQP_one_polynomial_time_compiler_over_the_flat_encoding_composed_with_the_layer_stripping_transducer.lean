-- Isolated target snapshot from saved campaign metadata; NOT a proof.
import Theorems.Thm_ShiBQP_the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities
import Theorems.Thm_ShiBQP_polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run
import Theorems.Thm_ShiTM_the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside
import Theorems.Thm_ShiBQP_one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2 ShiShallow ShiClass ShiBQP

namespace ShiBQP

theorem one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer
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
    (encb : List ℕ → List Bool)
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
    -- ===================== THE TWO MACHINE-SIDE RUN OBLIGATIONS =====================
    -- `MACH-B4e` states both of these with the output
    -- `map eb.invFun (encCompile (unL w) (unR w))`, where `encCompile` is one of ITS binders.
    -- Here the compiler is bound by `COMPILE-FLATb`'s existential, so per RESUME 483 both are
    -- stated COMPILER-FREE and reattached inside the proof: `hREJ0` outputs literally `[]`
    -- (which is what the totality clauses say the compiler is there), and `hBAD0` outputs the
    -- structure clause's right-hand side spelled out (which is what `COMPILE-FLATb` (4) says
    -- the compiler is there).  Nothing is absorbed by either restatement.
    -- THE ILL-FORMED / TRUNCATED PARSE.  `MACH-B4e`'s `hBAD`, at the same free budget
    -- `pb * |w| + cb`.  RESUME 528: this is STRICTLY WIDER than `MACH-B4d`'s, because the
    -- flat seam carries an explicit non-truncation side condition that the old seam lacked,
    -- so a truncated record run routes here too.  UNDISCHARGED.
    (hBAD0 : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ¬ (((pg ng rest).1).length = ng
          ∧ (∀ rec ∈ (pg ng rest).1,
              (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]))) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun
          (encb (Lw (unR w ++ List.replicate (anc + 1) false)
              ++ (List.replicate ((unR w).length + (anc + 1)) 0
              ++ ((((pg ng rest).1).map blkN).flatten
              ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
              ++ (((((pg ng rest).1).reverse).map blkAN).flatten
              ++ (Ew (unR w ++ List.replicate (anc + 1) false)
                ++ List.replicate ((unR w).length + (anc + 1)) 0)))))))))
        (pb * w.length + cb)))
    -- THE REJECT-PATH RUN, COMPILER-FREE.  Discharged by accepted `MACH-REJ` at
    -- `pr := 20, cr := 32` (RESUME 529: it transfers to the flat encoding free), but a binder
    -- here because this file does not import `MACH-REJ`.
    (hREJ0 : ∀ w : List Bool, ¬ (3 ≤ (unpack (unL w)).length) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some ([] : List (tm.Γ tm.k₁)))
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
            ∧ (∀ k : tm.K, k ≠ tm.k₁ → T k = [])))
    -- ============ `COMPILE-FLATb`'s REMAINING FUNCTIONS AND ITS NINE INPUTS ============
    -- The gate tokeniser, the padded-input builder, the two sweep aggregators, the route-(A)
    -- syntactic compiler and the FLAT family encoding.
    (tk : ∀ m : ℕ, Instr m → List ℕ)
    (T : ∀ n m' : ℕ, Bits n → List Bool)
    (D DA : ∀ m : ℕ, List (Instr m) → List ℕ)
    (C : ∀ n m' : ℕ, List (Instr (n + m')) → Bits n → Fin (n + m') → List ℕ)
    (encFlat : Family → ℕ → PvsNP.Str)
    -- THE `encFlat` CONTRACT, character for character (`wave30 ENCFLAT_CONTRACT.md`).  The
    -- same binder serves `COMPILE-FLATb` and `PHI-M5`, which is what makes them weld.
    (hFlat : ∀ (F : Family) (n : ℕ),
      encFlat F n
        = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
          ++ encNat (((F.circ n).flatten).length)
          ++ ((((F.circ n).flatten).map encInstr).flatten))
    -- `COMPILE-STR` (1)-(2): the decoder, one unary-terminated field at a time.
    (hnil : unpack [] = [])
    (hnat : ∀ (k : ℕ) (r : PvsNP.Str), unpack (encNat k ++ r) = k :: unpack r)
    -- `COMPILE-STR` (8): decoding is compositional over instruction codes.
    (hinstr : ∀ (m : ℕ) (g : Instr m) (r : PvsNP.Str),
      unpack (encInstr g ++ r) = tk m g ++ unpack r)
    -- `COMPILE-STR` (16): the GATE parser's round trip on a token stream.
    (hpg : ∀ (m : ℕ) (l : List (Instr m)) (r : List ℕ),
      pg l.length ((l.map (tk m)).flatten ++ r) = (l.map (tk m), r))
    -- `COMPILE-STRb` (8)-(9): rendering reproduces the forward and adjoint sweeps.
    (hfwd : ∀ (m : ℕ) (gs : List (Instr m)), ((gs.map (tk m)).map blkN).flatten = D m gs)
    (hadj : ∀ (m : ℕ) (gs : List (Instr m)),
      (((gs.map (tk m)).reverse).map blkAN).flatten = DA m gs)
    -- `BRIDGE-C2c`: the padded input and the whole route-(A) program.
    (hT : ∀ (n m' : ℕ) (x : Bits n), T n m' x
      = List.ofFn (fun k : Fin (n + m') =>
          if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false))
    (hC : ∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
      C n m' gs x out
        = Lw (T n m' x) ++ (List.replicate (n + m') 0 ++ (D (n + m') gs
            ++ ((List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0))
              ++ (DA (n + m') gs
                ++ (Ew (T n m' x) ++ List.replicate (n + m') 0))))))

    -- ============ THE SIX REMAINING LENGTH BUDGETS (`PAIRDECd` (1)) ============
    -- `he` is the seventh and is already a binder above, shared with `MACH-B4e`.
    (hu : ∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
    (hp : ∀ (k : ℕ) (ts : List ℕ),
      ((pg k ts).1.map List.sum).sum + ((pg k ts).1.map List.length).sum
        ≤ ts.sum + ts.length)
    (hLw : ∀ l : List Bool, (Lw l).length ≤ 2 * l.length)
    (hEw : ∀ l : List Bool, (Ew l).length ≤ 4 * l.length)
    (hbN : ∀ d : List ℕ, (blkN d).length ≤ 2 * (d.sum + d.length))
    (hbAN : ∀ d : List ℕ, (blkAN d).length ≤ 2 * (d.sum + d.length))

    -- ============ THE EIGHT DECODER EQUATIONS (`PAIRDECc` (3)) ============
    -- `rfl`s for a consumer holding the concrete tagged decoders.
    (l0 : unL [] = []) (l1 : ∀ b : Bool, unL [b] = [])
    (lf : ∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t)
    (lt : ∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = [])
    (r0 : unR [] = []) (r1 : ∀ b : Bool, unR [b] = [])
    (rf : ∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t)
    (rt : ∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t)

    -- ============ `PHI-M5`'s FOUR HYPOTHESES, VERBATIM ============
    -- `PHI-M5`'s published statement is CONDITIONAL on these four (plus the `encFlat`
    -- contract, which is `hFlat` above).  Each is accepted: `hAc` is `PHI-Ac` (A), `hSat` is
    -- `PHI-Ac` (5), `hBlift` is `PHI-B` (1), and `hPTCphi` is `PHI-M3` (6) composed with
    -- `PHI-M4` (1).  They are binders here purely to avoid importing four more files; the
    -- eight functions and nineteen equations they quantify over are LOCAL to each binder and
    -- shadow nothing that this file's conclusion mentions.
    (hAc :
      (∀ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        bump [] = [] →
        (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t)) →
        upk [] = [] →
        (∀ r : List Bool, upk (false :: r) = 0 :: upk r) →
        (∀ r : List Bool, upk (true :: r) = bump (upk r)) →
        (∀ t : ℕ, ar t = if t = 4 then 3 else 2) →
        (∀ ts : List ℕ, pg 0 ts = ([], ts)) →
        (∀ k : ℕ, pg (k + 1) [] = ([], [])) →
        (∀ (k t : ℕ) (u : List ℕ),
          pg (k + 1) (t :: u)
            = (if ar t ≤ u.length + 1 then
                ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                  (pg k ((t :: u).drop (ar t))).2)
              else ([], []))) →
        (∀ ts : List ℕ, sl 0 ts = []) →
        (∀ k : ℕ, sl (k + 1) [] = []) →
        (∀ (k l : ℕ) (u : List ℕ),
          sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2) →
        pt [] = [] →
        (∀ a : ℕ, pt [a] = [a]) →
        (∀ a b : ℕ, pt [a, b] = [a, b]) →
        (∀ (a b n : ℕ) (r : List ℕ),
          pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten) →
        (∀ s : List Bool, Φ s = E (pt (upk s))) →
        ((E [] = []
            ∧ (∀ (c : ℕ) (cs : List ℕ),
                E (c :: cs) = List.replicate c true ++ false :: E cs))
          ∧ (∀ (anc out : ℕ) (c : List (List (List ℕ))),
              (∀ q ∈ c, ∀ rec ∈ q,
                (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
              Φ (E (anc :: out :: c.length
                      :: (c.map (fun q => q.length :: q.flatten)).flatten))
                = E (anc :: out :: c.flatten.length :: c.flatten.flatten))
          ∧ (∀ s : List Bool, (Φ s).length ≤ s.length)
          ∧ (∀ (anc out : ℕ) (c : List (List (List ℕ))),
              (E (anc :: out :: c.length
                    :: (c.map (fun q => q.length :: q.flatten)).flatten)).length
                = (E (anc :: out :: c.flatten.length :: c.flatten.flatten)).length
                  + 2 * c.length))))
    (hSat :
      (∃ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = []
        ∧ (∀ (c : ℕ) (cs : List ℕ),
            E (c :: cs) = List.replicate c true ++ false :: E cs)
        ∧ bump [] = []
        ∧ (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t))
        ∧ upk [] = []
        ∧ (∀ r : List Bool, upk (false :: r) = 0 :: upk r)
        ∧ (∀ r : List Bool, upk (true :: r) = bump (upk r))
        ∧ (∀ t : ℕ, ar t = if t = 4 then 3 else 2)
        ∧ (∀ ts : List ℕ, pg 0 ts = ([], ts))
        ∧ (∀ k : ℕ, pg (k + 1) [] = ([], []))
        ∧ (∀ (k t : ℕ) (u : List ℕ),
            pg (k + 1) (t :: u)
              = (if ar t ≤ u.length + 1 then
                  ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                    (pg k ((t :: u).drop (ar t))).2)
                else ([], [])))
        ∧ (∀ ts : List ℕ, sl 0 ts = [])
        ∧ (∀ k : ℕ, sl (k + 1) [] = [])
        ∧ (∀ (k l : ℕ) (u : List ℕ),
            sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2)
        ∧ pt [] = []
        ∧ (∀ a : ℕ, pt [a] = [a])
        ∧ (∀ a b : ℕ, pt [a, b] = [a, b])
        ∧ (∀ (a b n : ℕ) (r : List ℕ),
            pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten)
        ∧ (∀ s : List Bool, Φ s = E (pt (upk s)))
        ∧ Φ (E [0, 0, 0]) = E [0, 0, 0]
        ∧ Φ (E [0, 0, 1, 1, 0, 0]) = E [0, 0, 1, 0, 0]
        ∧ Φ (E [0, 0, 2, 2, 0, 0, 1, 1, 1, 4, 0, 1]) = E [0, 0, 3, 0, 0, 1, 1, 4, 0, 1]
        ∧ (E [0, 0, 2, 2, 0, 0, 1, 1, 1, 4, 0, 1]).length = 24
        ∧ (E [0, 0, 3, 0, 0, 1, 1, 4, 0, 1]).length = 20))
    (hBlift :
      (∀ (E : List ℕ → List Bool) (Φ : List Bool → List Bool)
          (encFlat' : Family → ℕ → PvsNP.Str),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        (∀ (anc out : ℕ) (c : List (List (List ℕ))),
          (∀ q ∈ c, ∀ rec ∈ q,
            (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
          Φ (E (anc :: out :: c.length
                  :: (c.map (fun q => q.length :: q.flatten)).flatten))
            = E (anc :: out :: c.flatten.length :: c.flatten.flatten)) →
        (∀ (anc out : ℕ) (c : List (List (List ℕ))),
          (E (anc :: out :: c.length
                :: (c.map (fun q => q.length :: q.flatten)).flatten)).length
            = (E (anc :: out :: c.flatten.length :: c.flatten.flatten)).length
              + 2 * c.length) →
        (∀ (F : Family) (n : ℕ),
          encFlat' F n
            = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
              ++ encNat (((F.circ n).flatten).length)
              ++ ((((F.circ n).flatten).map encInstr).flatten)) →
        ∀ (F : Family) (n : ℕ),
          Φ (encFamilyAt F n) = encFlat' F n
          ∧ (encFamilyAt F n).length
              = (encFlat' F n).length + 2 * (F.circ n).length))
    (hPTCphi :
      (∀ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        bump [] = [] →
        (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t)) →
        upk [] = [] →
        (∀ r : List Bool, upk (false :: r) = 0 :: upk r) →
        (∀ r : List Bool, upk (true :: r) = bump (upk r)) →
        (∀ t : ℕ, ar t = if t = 4 then 3 else 2) →
        (∀ ts : List ℕ, pg 0 ts = ([], ts)) →
        (∀ k : ℕ, pg (k + 1) [] = ([], [])) →
        (∀ (k t : ℕ) (u : List ℕ),
          pg (k + 1) (t :: u)
            = (if ar t ≤ u.length + 1 then
                ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                  (pg k ((t :: u).drop (ar t))).2)
              else ([], []))) →
        (∀ ts : List ℕ, sl 0 ts = []) →
        (∀ k : ℕ, sl (k + 1) [] = []) →
        (∀ (k l : ℕ) (u : List ℕ),
          sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2) →
        pt [] = [] →
        (∀ a : ℕ, pt [a] = [a]) →
        (∀ a b : ℕ, pt [a, b] = [a, b]) →
        (∀ (a b n : ℕ) (r : List ℕ),
          pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten) →
        (∀ s : List Bool, Φ s = E (pt (upk s))) →
        PvsNP.PolyTimeComputable Φ))

    -- ============================== THE CONCLUSION ==============================
    : ∃ encCompile : PvsNP.Str → PvsNP.Str → PvsNP.Str,
      -- (1) THE HEADLINE.  The string-level compiler over the FLAT encoding, read along the
      -- tagged pairing decoders, is polynomial-time computable.  Nothing existential is left
      -- inside: `encCompile` is the SAME function as in (2)-(6).
      PvsNP.PolyTimeComputable (fun w => encCompile (unL w) (unR w))
      -- (2) AND IT IS THE RIGHT COMPILER: on a FLAT-encoded family it produces the encoded
      -- route-(A) program.  `COMPILE-FLATb` (3) at this compiler.  (1) ∧ (2) is the joint
      -- statement the campaign has never had NON-VACUOUSLY.
    ∧ (∀ (F : Family) (x : PvsNP.Str),
        encCompile (encFlat F x.length) x
          = encb (C x.length (F.anc x.length + 1) ((F.circ x.length).flatten)
              (toBits x) (F.out x.length)))
      -- (3) THE OUTPUT BUDGET ON EVERY PAIR OF STRINGS, garbage included.
    ∧ (∀ s x : PvsNP.Str, (encCompile s x).length ≤ 56 * (s.length + x.length + 1))
      -- (4) THE STRUCTURE CLAUSE, over the GATE parser `pg` and over no layer parser.
    ∧ (∀ (s x : PvsNP.Str) (anc out ng : ℕ) (rest : List ℕ),
        unpack s = anc :: out :: ng :: rest →
        encCompile s x
          = encb (Lw (x ++ List.replicate (anc + 1) false)
              ++ (List.replicate (x.length + (anc + 1)) 0
              ++ ((((pg ng rest).1).map blkN).flatten
              ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
              ++ (((((pg ng rest).1).reverse).map blkAN).flatten
              ++ (Ew (x ++ List.replicate (anc + 1) false)
                ++ List.replicate (x.length + (anc + 1)) 0)))))))
      -- (5) TOTALITY AT THE NUMERIC PREDICATE, not merely at the three shapes.
    ∧ (∀ s x : PvsNP.Str, ¬ (3 ≤ (unpack s).length) → encCompile s x = [])
      -- (6) THE COMPOSITE, AT THE *LAYERED* ENCODING.  ONE transducer `Phi`, poly-time,
      -- carrying `encFamilyAt` to `encFlat`, so that the compiler above is a compiler for the
      -- encoding that `ShiBQP.Uniform` and `READ-1c` actually produce.  The last clause is the
      -- consumer's form: for ANY poly-time source `g` with `g x = encFamilyAt F x.length`,
      -- `Phi ∘ g` is poly-time, produces the flat encoding, and feeds `encCompile` to give
      -- the encoded route-(A) program.  This is `PvsNP.polyTimeComputable_comp`, one line.
    ∧ (∃ Phi : PvsNP.Str → PvsNP.Str,
        PvsNP.PolyTimeComputable Phi
      ∧ (∀ (F : Family) (n : ℕ), Phi (encFamilyAt F n) = encFlat F n)
      ∧ (∀ (F : Family) (x : PvsNP.Str),
          encCompile (Phi (encFamilyAt F x.length)) x
            = encb (C x.length (F.anc x.length + 1) ((F.circ x.length).flatten)
                (toBits x) (F.out x.length)))
      ∧ (∀ (F : Family) (g : PvsNP.Str → PvsNP.Str),
          PvsNP.PolyTimeComputable g →
          (∀ x : PvsNP.Str, g x = encFamilyAt F x.length) →
          ∃ h : PvsNP.Str → PvsNP.Str,
            PvsNP.PolyTimeComputable h
          ∧ (∀ x : PvsNP.Str, h x = encFlat F x.length)
          ∧ (∀ x : PvsNP.Str, encCompile (h x) x
              = encb (C x.length (F.anc x.length + 1) ((F.circ x.length).flatten)
                  (toBits x) (F.out x.length)))))
      -- (7) NON-VACUITY, A COMPUTATION (RESUME 503): the contract's right-hand side at the
      -- smallest non-degenerate witness -- no ancillas, output wire `0`, one `H` gate.
    ∧ (encNat 0 ++ encNat 0 ++ encNat (([Instr.h (0 : Fin 1)]).length)
          ++ (([Instr.h (0 : Fin 1)]).map encInstr).flatten
        = [false, false, true, false, false, false])
      -- (8) THE DEGENERATE WITNESS: an empty circuit carries NO layer token under the flat
      -- encoding.  This is the witness class on which `hSHAPE` was refuted (RESUME 492).
    ∧ (∀ (F : Family) (n : ℕ), (F.circ n).flatten = [] →
        encFlat F n = encNat (F.anc n) ++ encNat ((F.out n : ℕ)) ++ encNat 0)
      -- (9) the three empty unary fields, computed.
    ∧ (encNat 0 ++ encNat 0 ++ encNat 0 = [false, false, false])
      -- (10) THE FLAT DECODE, exported so no later consumer redoes it: the third field is the
      -- GATE count and the body is a single run of records.
    ∧ (∀ (F : Family) (n : ℕ),
        unpack (encFlat F n)
          = F.anc n :: ((F.out n : ℕ)) :: (((F.circ n).flatten).length)
            :: ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))).flatten))
      -- (11) AND THE GATE PARSER CONSUMES THE WHOLE BODY.
    ∧ (∀ (F : Family) (n : ℕ),
        pg (((F.circ n).flatten).length) ((unpack (encFlat F n)).drop 3)
          = ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))), [])) := by
  sorry

end ShiBQP

