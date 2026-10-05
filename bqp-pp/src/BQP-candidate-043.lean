import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside

namespace BQPReferenceValidation.Source43
/-
MACH-B4e.  `MACH-B4d` RE-ISSUED OVER THE *FLAT* PARSER SEAM: THE SAME TWO SPEC CHAINS WELDED
AT `lGTz`, THE SAME WORD IDENTITY AND THE SAME THREE-BRANCH PACKAGING, WITH THE THREE-TIMES-
FALSE `hSHAPE` REPLACED BY THE PROVED `FLAT-1b` (7).

WHY THIS FILE EXISTS.  `MACH-B4d` is accepted (EXIT=0, 76s) and TRUE, but its conjunct (1) is
VACUOUS: the hypothesis `hSHAPE` it consumes was refuted three independent times --
RESUME 487 (the decoder discards an unterminated trailing `true`-run, so a canonical string is
not determined by its decode), RESUME 489 (`pg`'s accepted guard is `¬ t = 4`, not `t < 4`, so
`[7, 0]` is a parsed record satisfying neither well-formedness disjunct), and RESUME 492 (the
DESIGN-level one: `pl` COUNTS layers while `(pl nl rest).1` COLLECTS gates, and `pl` eats its
per-layer length token, so `(pl nl rest).1.flatten` is a subsequence and not a prefix of the
body).  None of the three is reintroduced here.  Route (b) is taken: the encoding is FLAT, so
the layer parser `pl` does not appear in this file at all, and the seam is stated over the
GATE parser `pg`.

WHAT ACTUALLY CHANGED, AND IT IS SLIGHTLY MORE THAN TRANSCRIPTION.
 (a) `pl`/`nl` are gone; every occurrence is `pg`/`ng`, and `h3` is the flat structure clause,
     i.e. `COMPILE-FLATb` (4) rather than `COMPILE-STRcb` (3).  That part IS transcription.
 (b) `hSHAPE` is replaced by `hSEAM`, which is `FLAT-1b` (7) CHARACTER FOR CHARACTER.  It is
     PROVED there, not hypothesised, and it carries an explicit non-truncation side condition
     `((pg ng rest).1).length = ng` that `hSHAPE` did not have.
 (c) THE SIDE CONDITION CREATES A CASE THE OLD SEAM DID NOT HAVE, so `hBAD` is EXTENDED: its
     antecedent is now the negation of the CONJUNCTION "not truncated AND well formed",
     covering truncation as well as bad tags, at the same free budget `pb * |w| + cb`.  The
     three-way split of `MACH-B4d` therefore becomes a three-way split with a wider middle
     arm, not a four-way split, and conjunct (1) stays unconditional on `∀ w`.
 (d) TWO WITNESS COMPUTATIONS are added as conjuncts (4) and (5), so the reachability of the
     accepting branch and the routing of the truncating case are CHECKED by this compile and
     not asserted in prose.
Nothing else moves: the ninety-one disequalities, the weld by `mbChainN`, the word identity
`hWID`, the budget arithmetic and the reject arm are `MACH-B4d`'s, unchanged.

WHY THE SEAM FITS `hFRONT` WITHOUT A NEW RUN THEOREM, CHECKED RATHER THAN ASSUMED.
`MACH-B4a3`'s `hFRONT` binds `recs : List (List ℕ)` and `tl : List Bool` UNIVERSALLY and asks
only for the string equation
  `unL w = 1^anc 0 1^out 0 1^(recs.length) 0 (E recs.flatten ++ tl)`
plus per-record well-formedness.  `FLAT-1b` (7) produces exactly that pair, with
`recs = (pg ng rest).1`; substituting that equation leaves the hypothesis in the literal shape
`hFRONT` demands.  The only other place `recs` is pinned is `h3`, and over the flat encoding
`h3` is already stated at `(pg ng rest).1` (`COMPILE-FLATb` (4)).  So the two agree on the
nose, which is precisely what failed in RESUME 492: there `hFRONT` wanted `recs.length` in the
third block while `h3` forced `recs := (pl nl rest).1`, and those two numbers are unrelated.

THE REFUTATION-FIRST CHECK, RUN BEFORE THE CHAIN WAS TRUSTED (RESUME 498).
 * ACCEPTING, conjunct (4).  The canonical one-gate flat witness of `FLAT-1b` (8):
   `unpack (E [0, 0, 1, 0, 0]) = [0, 0, 1, 0, 0]` (banked there), so `anc = 0`, `out = 0`,
   `ng = 1`, `rest = [0, 0]`.  Here `pg 1 [0, 0] = ([[0, 0]], [])` from `pg4` and `pg0`, hence
   `((pg 1 [0, 0]).1).length = 1 = ng` AND `[0, 0]` is well formed with tag `0 < 4`.  Both
   premises of the accepting branch hold at once.
 * TRUNCATING, conjunct (5).  `FLAT-1b` (9)'s witness: `pg 1 [0] = ([], [])` from `pg2`, so
   `((pg 1 [0]).1).length = 0 ≠ 1 = ng`.  The conjunction `hBAD` negates is refuted, so this
   stream routes to `hBAD` and to nothing else.
Both are `pg`-equation computations, so a 492-class fault would surface as a failed rewrite.

SOURCES.  `hA` is `MACH-B4a3` (1) applied to its ten phase-run hypotheses; `hB` is
`MACH-B4b` (1) applied to its eight; `hSEAM` is `FLAT-1b` (7); `h3` is `COMPILE-FLATb` (4);
`hREJ` is `MACH-REJ`; `pg0`, `pg2`, `pg4` are three of `PARSE-TOT`'s six gate-parser
equations.  `hBAD` is the one genuinely undischarged machine-side run, at a free budget.
No `namespace` and no `open ShiTM` (gotcha 468); import is
`Mathlib.Computability.TuringMachine.Computable` only, as in `MACH-B4d`.

NOT CLAIMED.  This file does not build the transducer `Φ`, does not discharge `hBAD`, and
says nothing about `encFamilyAt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2


/-- Chain two runs of known length. -/
private lemma mbChainN {A : Type} {f : A → A} {a b c : A} {m n t : ℕ} (ht : t = m + n)
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[t] a = c := by
  subst ht
  rw [Nat.add_comm m n, Function.iterate_add_apply f n m a, h1]
  exact h2

/-- `TM2OutputsInTime` is an upper bound, so it is monotone in the budget. -/
private lemma bumpTime {tm : Turing.FinTM2} {u : List (tm.Γ tm.k₀)}
    {o : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (hm : m ≤ m')
    (h : Nonempty (Turing.TM2OutputsInTime tm u o m)) :
    Nonempty (Turing.TM2OutputsInTime tm u o m') := by
  obtain ⟨hi⟩ := h
  obtain ⟨he, hle⟩ := hi
  exact ⟨⟨he, Nat.le_trans hle hm⟩⟩

/-- One pairwise disequality out of a `Nodup`. -/
private lemma neOfNodup {α : Type} {a b : α} {l : List α}
    (h : (a :: l).Nodup) (hb : b ∈ l) : a ≠ b := by
  intro e
  exact (List.nodup_cons.1 h).1 (e ▸ hb)

/-- Reversing a buffered, per-block-reversed, reverse-order rendering gives the plain
rendering back.  This is the whole content of Design R's global reversal. -/
private lemma revFlattenRev {α : Type} (L : List (List α)) :
    ((L.reverse.map (fun r => r.reverse)).flatten).reverse = L.flatten := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, List.map_append, List.flatten_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.reverse_reverse, ih, List.flatten_cons]


theorem _root_.BQPReferenceValidation.candidate43
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
  -- THE NINETY-ONE DISEQUALITIES, PEELED OFF `MACH-A5b` (1)'s SINGLE `Nodup`.
  have hn0 := hnd
  have hn1 := (List.nodup_cons.1 hn0).2
  have hn2 := (List.nodup_cons.1 hn1).2
  have hn3 := (List.nodup_cons.1 hn2).2
  have hn4 := (List.nodup_cons.1 hn3).2
  have hn5 := (List.nodup_cons.1 hn4).2
  have hn6 := (List.nodup_cons.1 hn5).2
  have hn7 := (List.nodup_cons.1 hn6).2
  have hn8 := (List.nodup_cons.1 hn7).2
  have hn9 := (List.nodup_cons.1 hn8).2
  have hn10 := (List.nodup_cons.1 hn9).2
  have hn11 := (List.nodup_cons.1 hn10).2
  have hn12 := (List.nodup_cons.1 hn11).2
  have nab : tm.k₀ ≠ ksrc := neOfNodup hn0 (by simp)
  have nac : tm.k₀ ≠ kxin := neOfNodup hn0 (by simp)
  have nad : tm.k₀ ≠ khld := neOfNodup hn0 (by simp)
  have nae : tm.k₀ ≠ kpd1 := neOfNodup hn0 (by simp)
  have naf : tm.k₀ ≠ kpd2 := neOfNodup hn0 (by simp)
  have nag : tm.k₀ ≠ kqc := neOfNodup hn0 (by simp)
  have nah : tm.k₀ ≠ kfu := neOfNodup hn0 (by simp)
  have nai : tm.k₀ ≠ ktok := neOfNodup hn0 (by simp)
  have naj : tm.k₀ ≠ kidx := neOfNodup hn0 (by simp)
  have nam : tm.k₀ ≠ kopc := neOfNodup hn0 (by simp)
  have nan : tm.k₀ ≠ tm.k₁ := neOfNodup hn0 (by simp)
  have nap : tm.k₀ ≠ kscA := neOfNodup hn0 (by simp)
  have naq : tm.k₀ ≠ kscB := neOfNodup hn0 (by simp)
  have nbc : ksrc ≠ kxin := neOfNodup hn1 (by simp)
  have nbd : ksrc ≠ khld := neOfNodup hn1 (by simp)
  have nbe : ksrc ≠ kpd1 := neOfNodup hn1 (by simp)
  have nbf : ksrc ≠ kpd2 := neOfNodup hn1 (by simp)
  have nbg : ksrc ≠ kqc := neOfNodup hn1 (by simp)
  have nbh : ksrc ≠ kfu := neOfNodup hn1 (by simp)
  have nbi : ksrc ≠ ktok := neOfNodup hn1 (by simp)
  have nbj : ksrc ≠ kidx := neOfNodup hn1 (by simp)
  have nbm : ksrc ≠ kopc := neOfNodup hn1 (by simp)
  have nbn : ksrc ≠ tm.k₁ := neOfNodup hn1 (by simp)
  have nbp : ksrc ≠ kscA := neOfNodup hn1 (by simp)
  have nbq : ksrc ≠ kscB := neOfNodup hn1 (by simp)
  have ncd : kxin ≠ khld := neOfNodup hn2 (by simp)
  have nce : kxin ≠ kpd1 := neOfNodup hn2 (by simp)
  have ncf : kxin ≠ kpd2 := neOfNodup hn2 (by simp)
  have ncg : kxin ≠ kqc := neOfNodup hn2 (by simp)
  have nch : kxin ≠ kfu := neOfNodup hn2 (by simp)
  have nci : kxin ≠ ktok := neOfNodup hn2 (by simp)
  have ncj : kxin ≠ kidx := neOfNodup hn2 (by simp)
  have ncm : kxin ≠ kopc := neOfNodup hn2 (by simp)
  have ncn : kxin ≠ tm.k₁ := neOfNodup hn2 (by simp)
  have ncp : kxin ≠ kscA := neOfNodup hn2 (by simp)
  have ncq : kxin ≠ kscB := neOfNodup hn2 (by simp)
  have nde : khld ≠ kpd1 := neOfNodup hn3 (by simp)
  have ndf : khld ≠ kpd2 := neOfNodup hn3 (by simp)
  have ndg : khld ≠ kqc := neOfNodup hn3 (by simp)
  have ndh : khld ≠ kfu := neOfNodup hn3 (by simp)
  have ndi : khld ≠ ktok := neOfNodup hn3 (by simp)
  have ndj : khld ≠ kidx := neOfNodup hn3 (by simp)
  have ndm : khld ≠ kopc := neOfNodup hn3 (by simp)
  have ndn : khld ≠ tm.k₁ := neOfNodup hn3 (by simp)
  have ndp : khld ≠ kscA := neOfNodup hn3 (by simp)
  have ndq : khld ≠ kscB := neOfNodup hn3 (by simp)
  have nef : kpd1 ≠ kpd2 := neOfNodup hn4 (by simp)
  have neg : kpd1 ≠ kqc := neOfNodup hn4 (by simp)
  have neh : kpd1 ≠ kfu := neOfNodup hn4 (by simp)
  have nei : kpd1 ≠ ktok := neOfNodup hn4 (by simp)
  have nej : kpd1 ≠ kidx := neOfNodup hn4 (by simp)
  have nem : kpd1 ≠ kopc := neOfNodup hn4 (by simp)
  have nen : kpd1 ≠ tm.k₁ := neOfNodup hn4 (by simp)
  have nep : kpd1 ≠ kscA := neOfNodup hn4 (by simp)
  have neq : kpd1 ≠ kscB := neOfNodup hn4 (by simp)
  have nfg : kpd2 ≠ kqc := neOfNodup hn5 (by simp)
  have nfh : kpd2 ≠ kfu := neOfNodup hn5 (by simp)
  have nfi : kpd2 ≠ ktok := neOfNodup hn5 (by simp)
  have nfj : kpd2 ≠ kidx := neOfNodup hn5 (by simp)
  have nfm : kpd2 ≠ kopc := neOfNodup hn5 (by simp)
  have nfn : kpd2 ≠ tm.k₁ := neOfNodup hn5 (by simp)
  have nfp : kpd2 ≠ kscA := neOfNodup hn5 (by simp)
  have nfq : kpd2 ≠ kscB := neOfNodup hn5 (by simp)
  have ngh : kqc ≠ kfu := neOfNodup hn6 (by simp)
  have ngi : kqc ≠ ktok := neOfNodup hn6 (by simp)
  have ngj : kqc ≠ kidx := neOfNodup hn6 (by simp)
  have ngm : kqc ≠ kopc := neOfNodup hn6 (by simp)
  have ngn : kqc ≠ tm.k₁ := neOfNodup hn6 (by simp)
  have ngp : kqc ≠ kscA := neOfNodup hn6 (by simp)
  have ngq : kqc ≠ kscB := neOfNodup hn6 (by simp)
  have nhi : kfu ≠ ktok := neOfNodup hn7 (by simp)
  have nhj : kfu ≠ kidx := neOfNodup hn7 (by simp)
  have nhm : kfu ≠ kopc := neOfNodup hn7 (by simp)
  have nhn : kfu ≠ tm.k₁ := neOfNodup hn7 (by simp)
  have nhp : kfu ≠ kscA := neOfNodup hn7 (by simp)
  have nhq : kfu ≠ kscB := neOfNodup hn7 (by simp)
  have nij : ktok ≠ kidx := neOfNodup hn8 (by simp)
  have nim : ktok ≠ kopc := neOfNodup hn8 (by simp)
  have nin : ktok ≠ tm.k₁ := neOfNodup hn8 (by simp)
  have nip : ktok ≠ kscA := neOfNodup hn8 (by simp)
  have niq : ktok ≠ kscB := neOfNodup hn8 (by simp)
  have njm : kidx ≠ kopc := neOfNodup hn9 (by simp)
  have njn : kidx ≠ tm.k₁ := neOfNodup hn9 (by simp)
  have njp : kidx ≠ kscA := neOfNodup hn9 (by simp)
  have njq : kidx ≠ kscB := neOfNodup hn9 (by simp)
  have nmn : kopc ≠ tm.k₁ := neOfNodup hn10 (by simp)
  have nmp : kopc ≠ kscA := neOfNodup hn10 (by simp)
  have nmq : kopc ≠ kscB := neOfNodup hn10 (by simp)
  have nnp : tm.k₁ ≠ kscA := neOfNodup hn11 (by simp)
  have nnq : tm.k₁ ≠ kscB := neOfNodup hn11 (by simp)
  have npq : kscA ≠ kscB := neOfNodup hn12 (by simp)
  -- The two renderers, in the unapplied form `simp` needs under a `List.map`.
  have hblkf : blk = fun r => List.map oc (blkN r) := funext hblk
  have hblkAf : blkA = fun r => List.map oc (blkAN r) := funext hblkA
  -- THE WORD IDENTITY (conjunct 2), proved once and used by the run.
  have hWID : ∀ (pd : List Bool) (n out : ℕ) (recs : List (List ℕ)),
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
          ++ (Ew pd ++ List.replicate n 0)))))).map oc := by
    intro pd n out recs
    have hFWr : ∀ L : List (List ℕ),
        ((L.reverse.map (fun r => (blk r).reverse)).flatten).reverse
          = ((L.map blkN).flatten).map oc := by
      intro L
      have h1 : L.reverse.map (fun r => (blk r).reverse)
          = (L.map blk).reverse.map (fun r => r.reverse) := by
        simp [List.map_map, Function.comp_def]
      rw [h1, revFlattenRev]
      simp [hblkf, List.map_flatten, List.map_map, Function.comp_def]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.reverse_reverse, hFWr, hLf, hEf, hblkAf, hc0, hc1, hc8,
      List.map_append, List.map_flatten, List.map_replicate, List.map_cons,
      List.map_nil, List.map_map, Function.comp_def,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  -- THE ACCEPTING RUN, END TO END.
  have key : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ((pg ng rest).1).length = ng →
      (∀ rec ∈ (pg ng rest).1,
        (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (128 * w.length + 16 * (encCompile (unL w) (unR w)).length + 64)) := by
    intro w anc out ng rest hup hnt hmem
    -- THE SEAM, INSTANTIATED.  `hFRONT` (inside `hA`) binds `recs` and `tl` GENERICALLY, so
    -- the seam's pair drops straight into it once `recs` is identified with `(pg ng rest).1`.
    obtain ⟨recs, tl, hrecs, hrl, hdec⟩ := hSEAM unL w anc out ng rest hup hnt
    subst hrecs
    have hcomp := h3 (unL w) (unR w) anc out ng rest hup
    obtain ⟨hl, hv, hk0, hko⟩ := hIL (List.map ea.invFun w)
    have hinpec : (Turing.initList tm (List.map ea.invFun w)).stk tm.k₀ = w.map ec := by
      rw [hk0]
      exact List.map_congr_left (fun b _ => hea b)
    have hpl : (unR w ++ List.replicate (anc + 1) false).length
        = ((unR w).length + (anc + 1)) := by simp
    -- the front half, `MACH-B4a` at the machine
    obtain ⟨NA, u, T, bA, rA, tAx, tAf, tAm, tAe⟩ :=
      hA
      nab nac nad nae naf nag nah nai naj nam
      nan nap naq nbc nbd nbe nbf nbg nbh nbi
      nbj nbm nbn nbp nbq ncd nce ncf ncg nch
      nci ncj ncm ncn ncp ncq nde ndf ndg ndh
      ndi ndj ndm ndn ndp ndq nef neg neh nei
      nej nem nen nep neq nfg nfh nfi nfj nfm
      nfn nfp nfq ngh ngi ngj ngm ngn ngp ngq
      nhi nhj nhm nhn nhp nhq nij nim nin nip
      niq njm njn njp njq nmn nmp nmq nnp nnq
      npq
        hexh w anc out ((pg ng rest).1) tl (unR w ++ List.replicate (anc + 1) false) tm.initialState
        ((Turing.initList tm (List.map ea.invFun w)).stk) rfl hdec hmem hinpec hko
    -- the back half, `MACH-B4b` at the machine, welded at `lGTz`
    obtain ⟨NB, T8, bB, rB, tBn, tBe⟩ :=
      hB
      nab nac nad nae naf nag nah nai naj nam
      nan nap naq nbc nbd nbe nbf nbg nbh nbi
      nbj nbm nbn nbp nbq ncd nce ncf ncg nch
      nci ncj ncm ncn ncp ncq nde ndf ndg ndh
      ndi ndj ndm ndn ndp ndq nef neg neh nei
      nej nem nen nep neq nfg nfh nfi nfj nfm
      nfn nfp nfq ngh ngi ngj ngm ngn ngp ngq
      nhi nhj nhm nhn nhp nhq nij nim nin nip
      niq njm njn njp njq nmn nmp nmq nnp nnq
      npq
        hexh ((pg ng rest).1) (unR w ++ List.replicate (anc + 1) false) (T kopc)
        (((((pg ng rest).1).reverse).map blkA).flatten)
        ((List.replicate out c0 ++ (c8 :: (List.replicate out c1
            ++ ((((pg ng rest).1).reverse.map (fun r => (blk r).reverse)).flatten
              ++ (List.replicate ((unR w).length + (anc + 1)) c0
                  ++ (Lf ((unR w
                      ++ List.replicate (anc + 1) false).map o1)).reverse))))).reverse
          ++ (((((pg ng rest).1).reverse).map blkA).flatten
            ++ (Ef ((unR w ++ List.replicate (anc + 1) false).map o1)
                ++ List.replicate ((unR w).length + (anc + 1)) c0)))
        u T hmem rfl (by rw [tAm, hpl]) tAx tAf rfl tAe
    have hw := hWID (unR w
        ++ List.replicate (anc + 1) false) ((unR w).length + (anc + 1)) out ((pg ng rest).1)
    -- the wire carries the compiled program
    have hout : T8 tm.k₁ = List.map eb.invFun (encCompile (unL w) (unR w)) := by
      rw [tBn, hw, hWIRE, hcomp]
    -- the two runs are one run from the initial configuration
    have hstart : (Turing.initList tm (List.map ea.invFun w))
        = (⟨Option.some lS, tm.initialState,
            (Turing.initList tm (List.map ea.invFun w)).stk⟩ : Cfg tm.Γ tm.Λ tm.σ) := by
      rw [← hmain, ← hl, ← hv]
      rfl
    have rfull := mbChainN (rfl : NA + NB = NA + NB) rA rB
    rw [← hstart] at rfull
    have hrun := hOIT (List.map ea.invFun w)
      (List.map eb.invFun (encCompile (unL w) (unR w))) lH T8 (NA + NB) hhalt rfull hout tBe
    -- the cost bookkeeping
    have hUl : (unL w).length
        = anc + out + ((pg ng rest).1).length + (E (((pg ng rest).1).flatten)).length
          + tl.length + 3 := by
      rw [hdec]
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega
    have hULw := hunLl w
    have hURw := hunRl w
    have htrl := htr ((pg ng rest).1)
    have hencl : ((((pg ng rest).1).map enc).flatten).length
        = (E (((pg ng rest).1).flatten)).length := by
      have h := congrArg List.length (hgl ((pg ng rest).1))
      simpa using h.symm
    have hencxl : ((((pg ng rest).1).map encx).flatten).length
        = (E (((pg ng rest).1).flatten)).length := by
      have h := congrArg List.length (hglx ((pg ng rest).1))
      simpa using h.symm
    have hmapo1 : ((unR w ++ List.replicate (anc + 1) false).map o1).length
        = ((unR w).length + (anc + 1)) := by simp
    have hmapef : ((unR w ++ List.replicate (anc + 1) false).map ef).length
        = ((unR w).length + (anc + 1)) := by simp
    have hLfl : (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).length = (Lw (unR w
        ++ List.replicate (anc + 1) false)).length := by
      rw [hLf]; simp
    have hEfl : (Ef ((unR w ++ List.replicate (anc + 1) false).map o1)).length = (Ew (unR w
        ++ List.replicate (anc + 1) false)).length := by
      rw [hEf]; simp
    have hbdyl : (((((pg ng rest).1).reverse).map blkA).flatten).length
        = ((((((pg ng rest).1).reverse).map blkAN)).flatten).length := by
      simp [hblkAf, List.length_flatten, List.map_map, Function.comp_def]
    have hwordl : (((List.replicate out c0 ++ (c8 :: (List.replicate out c1
            ++ ((((pg ng rest).1).reverse.map (fun r => (blk r).reverse)).flatten
              ++ (List.replicate ((unR w).length + (anc + 1)) c0 ++ (Lf ((unR w
                  ++ List.replicate (anc + 1) false).map o1)).reverse))))).reverse
          ++ (((((pg ng rest).1).reverse).map blkA).flatten
            ++ (Ef ((unR w ++ List.replicate (anc + 1) false).map o1)
                ++ List.replicate ((unR w).length + (anc + 1)) c0)))).length = ((Lw (unR w
                    ++ List.replicate (anc + 1) false)
            ++ (List.replicate ((unR w).length + (anc + 1)) 0
            ++ ((((pg ng rest).1).map blkN).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pg ng rest).1).reverse).map blkAN).flatten
            ++ (Ew (unR w ++ List.replicate (anc + 1) false)
                ++ List.replicate ((unR w).length + (anc + 1)) 0))))))).length := by
      rw [hw]; simp only [List.length_map]
    have hOl : (encCompile (unL w) (unR w)).length = 4 * ((Lw (unR w
        ++ List.replicate (anc + 1) false)
            ++ (List.replicate ((unR w).length + (anc + 1)) 0
            ++ ((((pg ng rest).1).map blkN).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pg ng rest).1).reverse).map blkAN).flatten
            ++ (Ew (unR w ++ List.replicate (anc + 1) false)
                ++ List.replicate ((unR w).length + (anc + 1)) 0))))))).length := by
      rw [hcomp]; exact he _
    have hPROGl : ((Lw (unR w ++ List.replicate (anc + 1) false)
            ++ (List.replicate ((unR w).length + (anc + 1)) 0
            ++ ((((pg ng rest).1).map blkN).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pg ng rest).1).reverse).map blkAN).flatten
            ++ (Ew (unR w ++ List.replicate (anc + 1) false)
                ++ List.replicate ((unR w).length + (anc + 1)) 0))))))).length
        = (Lw (unR w ++ List.replicate (anc + 1) false)).length + ((unR w).length + (anc + 1))
          + ((((pg ng rest).1).map blkN).flatten).length + (2 * out + 1)
          + ((((((pg ng rest).1).reverse).map blkAN)).flatten).length
          + (Ew (unR w ++ List.replicate (anc + 1) false)).length + ((unR w).length + (anc + 1))
              := by
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      omega
    rw [hpl] at bA bB
    exact bumpTime (by omega) hrun
  -- the one arithmetic fact every branch needs: the exhibited budget splits
  -- THE TWO REFUTATION-FIRST WITNESS COMPUTATIONS (RESUME 498), DONE BEFORE THE CHAIN IS
  -- TRUSTED AND BANKED AS CONJUNCTS (4) AND (5) SO THEY ARE CHECKED AND NOT ASSERTED.
  have hw2 : pg 1 [0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ) := by
    have h := pg4 0 0 0 [] (by omega)
    rw [pg0] at h
    simpa using h
  have hw2f : (pg 1 [0, 0]).1 = ([[0, 0]] : List (List ℕ)) := by simp [hw2]
  have hw3 : pg 1 [0] = (([], []) : List (List ℕ) × List ℕ) := by simpa using pg2 0 0
  have hw3f : (pg 1 [0]).1 = ([] : List (List ℕ)) := by simp [hw3]
  have hNV1 : ((pg 1 [0, 0]).1).length = 1
      ∧ (∀ rec ∈ (pg 1 [0, 0]).1,
          (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) := by
    refine ⟨by simp [hw2f], ?_⟩
    rw [hw2f]
    intro rec hrec
    exact Or.inl ⟨0, 0, by omega, List.mem_singleton.1 hrec⟩
  have hNV2 : pg 1 [0] = (([], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 1 [0]).1).length = 1
          ∧ (∀ rec ∈ (pg 1 [0]).1,
              (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]))) := by
    refine ⟨hw3, ?_⟩
    rintro ⟨h1, -⟩
    simp [hw3f] at h1
  have hsplit : ∀ n : ℕ, (128 + pr + pb) * n = 128 * n + pr * n + pb * n := by
    intro n; ring
  refine ⟨⟨fun w => (128 + pr + pb) * w.length
        + 16 * (encCompile (unL w) (unR w)).length + (64 + cr + cb),
      128 + pr + pb, 16, 64 + cr + cb, ?_, fun w => le_refl _⟩, hWID, ?_, hNV1, hNV2⟩
  · intro w
    show Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun w)
      (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
      ((128 + pr + pb) * w.length + 16 * (encCompile (unL w) (unR w)).length
        + (64 + cr + cb)))
    by_cases hlen : 3 ≤ (unpack (unL w)).length
    · rcases hup : unpack (unL w) with _ | ⟨anc, t1⟩
      · simp [hup] at hlen
      · rcases t1 with _ | ⟨out, t2⟩
        · simp [hup] at hlen
        · rcases t2 with _ | ⟨ng, rest⟩
          · simp [hup] at hlen
          · by_cases hok : (((pg ng rest).1).length = ng
                ∧ (∀ rec ∈ (pg ng rest).1,
                    (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])))
            · exact bumpTime (by have hx := hsplit w.length; omega)
                (key w anc out ng rest hup hok.1 hok.2)
            · exact bumpTime (by have hx := hsplit w.length; omega)
                (hBAD w anc out ng rest hup hok)
    · exact bumpTime (by have hx := hsplit w.length; omega) (hREJ w hlen)
  · intro w
    refine ⟨?_, ?_, ?_⟩
    · have hx := hsplit w.length
      omega
    · have hx := hsplit w.length
      omega
    · have hx := hsplit w.length
      omega

end BQPReferenceValidation.Source43

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate43
    let target ← getConstInfo ``ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate43
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside; axioms {axioms}"
