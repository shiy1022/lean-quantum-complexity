import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run

namespace BQPReferenceValidation.Source44
/-
MACH-B4fb.  `MACH-B4e` RE-ISSUED OVER THE *REPAIRED* MACHINE `MACH-A5d`, WITH `hBAD`
DISCHARGED FROM `ROLLBACK` INSTEAD OF ASSUMED.

WHY THIS FILE EXISTS.  `MACH-B4e` is accepted (EXIT=0, 71s) and TRUE, but its conjunct (1)
was VACUOUS for the same reason `MACH-B4c` and `MACH-B4d` were: the hypothesis it consumes,
`hBAD`, was proved FALSE at the machine `MACH-A5c` in TWO independent modes (RESUME 538,
by the accepted diagnostic `BADDIAG-1`).
 * MODE (ii), UNRENDERABLE TAG.  `pg 1 [7, 0] = ([[7, 0]], [])` is a PARSED record with a
   tag that is neither below four nor equal to four.  `RENDER-TOTb` empties both of its
   compiled slots, but `MACH-A5c`'s two-way dispatch sent every tag other than four to the
   one-index emitter, which renders `1^i 0 0^i`, of length `2i + 1` and never empty.
 * MODE (i), TRUNCATION.  When the declared gate count outruns the body the parser rolls
   the partial record back correctly, but the LEFTOVER FUEL was never drained, so the zero
   run emitted `0^(pad + leftover)` where the compiled word demands `0^pad`.  The smallest
   refuting witness is `pg 2 [0]`, with `leftover = 1`; `pg 1 [0]`, the only truncation
   witness anyone had checked, has `leftover = 0` and is the one BENIGN sub-case.

WHAT THE REPAIR CHANGED, AND WHY `hBAD` IS NOW A THEOREM.  `MACH-A5d` (accepted, 101s, 126
labels) adds a fuel drain `lFD` wired `lSD` to `lFD` to `lV1`, which kills mode (i), and a
tag-skip arm `lSKT` reached by the guard `5 <= t`, which kills mode (ii) by emitting
NOTHING for an unrenderable tag, matching `RENDER-TOTb`'s `blk [t, i] = []`.  It proves
DISPATCH TOTALITY, `forall v, dsp v = lN1 or dsp v = lA or dsp v = lSKT`.  The consequence
for this file is structural: the well-formedness disjunct weakens from `t < 4` to ANY
`[t, i]`, and the weakened predicate is TOTAL over the parser's image -- conjunct (7)
below PROVES that from the six defining equations.  So the compound antecedent of
`MACH-B4e`'s `hBAD` collapses to PURE TRUNCATION, and there is exactly one branch left to
discharge.

HOW IT IS DISCHARGED.  The truncating run is composed here, phase by phase, from
`ROLLBACK` (accepted, 106s) and the same accepted block specifications `MACH-B4a3`
composes on the accepting path.  `ROLLBACK` exits at `lV1` CONFIGURATION-IDENTICAL to the
accepting exit -- token port forward, all four working ports empty, everything else
transported -- so phases (III) to (IX) and the whole back half are reused unchanged, and
only the head of the chain differs: `hSPLIT` then `hFIELDS` then `ROLLBACK`, in place of
`hFRONT` then the two drains.  `back` below is the shared tail, stated once and applied by
both branches, which is the formal content of "configuration-identical".

WHAT IS STILL OPEN, STATED AS BINDERS AND NOT HIDDEN.
 * `hPARSE` -- the parse-loop run with the rollback trail in its frame, `TOKENISEb` (1)
   plus one conjunct `T kscA = tr recs ++ S kscA`.  It is CARRIED HERE AS A NAMED BINDER
   and `hROLL` is stated as an IMPLICATION from it, so the reader can see exactly which of
   `ROLLBACK`'s six hypotheses this file leans on.  All six are now banked: `hPARSE` is
   accepted `PARSEKC` (1) clause for clause, at `kt := ksrc`, `kf := kfu`, `kh := khld`,
   `kc := kscA`, and it additionally supplies `|tr recs| = |recs| + |E recs.flatten|`,
   which is sharper than the `htr` bound this file carries; `hREJ` and `hFIN` are accepted
   `TOKREJ`, character for character; `hV0R`, `hSDR`, `hFDR` are three instantiations of
   accepted `LV0RUNb`.  The implication form is kept so the dependency stays legible.
 * `hA`, `hB`, `hFWD` are the accepted front half, back half and forward gate loop AT THE
   WEAKENED PREDICATE `not t = 4`.  At `MACH-A5c` they hold only at `t < 4`; at `MACH-A5d`
   the missing arm is exactly the tag-skip loop, and accepted `SKIPRUN` is its run theorem,
   generic in port, both labels, pop function, guard and encoder, so ONE instantiation
   serves each sweep.  The re-issue is mechanical and is NOT yet banked; it is named here
   rather than papered over.
 * `hSHAPEg` is `FLAT-1b`'s PRIVATE `flt_shape_gen`, proved there in full generality and
   exported only in the weaker, side-conditioned conjunct (7).  Re-exporting it is a
   one-conjunct re-issue.
 * `hREJ` is `MACH-REJ`, the header parser's reject arm, unchanged from `MACH-B4e`.

THE REFUTATION-FIRST CHECK, RUN BEFORE ANYTHING WAS BUILT (RESUME 498, 538).  All three
witnesses are banked as conjuncts, computed from the parser equations, not asserted.
 * `pg 1 [7, 0]` (conjunct 5): the record `[7, 0]` satisfies the NEW predicate and REFUTES
   the old one, so at `MACH-A5d` this stream is on the ACCEPTING branch and needs no
   special arm at all.  Mode (ii) is gone by construction, not by a side condition.
 * `pg 2 [0]` (conjunct 6): `|recs| = 0`, fuel `2`, so `leftover = 1` -- the witness that
   refuted the old `hBAD`.  It satisfies `|recs| + 1 <= ng` and `ng = |recs| + leftover + 1`,
   which are exactly `ROLLBACK`'s two fuel premises, so the truncating branch applies.
 * `pg 2 [0, 0, 0]` (conjunct 6): `|recs| = 1`, `leftover = 0`, the benign sub-case, still
   handled, by the SAME clause -- `leftover` is universally quantified in `ROLLBACK` and
   the exit `T kfu = []` is uniform in it.

NOT CLAIMED.  This file does not build the transducer, does not discharge `hPARSE`, does
not re-issue the gate loops at `MACH-A5d`, and says nothing about `encFamilyAt`.
No `namespace` and no `open ShiTM` (gotcha 468); the import is
`Mathlib.Computability.TuringMachine.Computable` only.
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


/-- The field renderer is additive on token lists.  Needed only to split the length of a
truncating source into its parsed and its rejected half. -/
private lemma encApp (E : List ℕ → List Bool) (e0 : E [] = [])
    (e1 : ∀ (c : ℕ) (cs : List ℕ), E (c :: cs) = List.replicate c true ++ false :: E cs) :
    ∀ a b : List ℕ, E (a ++ b) = E a ++ E b := by
  intro a
  induction a with
  | nil => intro b; rw [List.nil_append, e0, List.nil_append]
  | cons c cs ih =>
      intro b
      rw [List.cons_append, e1, e1, ih, List.append_assoc, List.cons_append]

/-- EVERY RECORD THE FUELLED PARSER RETURNS HAS ONE OF THE TWO LEGAL SHAPES, with the
two-field arm guarded by `not t = 4` and NOT by `t < 4`.  This is what makes the
well-formedness disjunct of `MACH-B4e`'s `hA`, `hB` and `hBAD` free at `MACH-A5d`: the
machine's tag-skip arm covers every tag of five or more, so the predicate the gate loops
need is exactly the predicate the parser already guarantees.  Proved from the six total
defining equations, so it holds of any parser satisfying them. -/
private lemma pgShape (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
    (p0 : ∀ ts : List ℕ, pg 0 ts = ([], ts))
    (p1 : ∀ k : ℕ, pg (k + 1) ([] : List ℕ) = ([], []))
    (p2 : ∀ t k : ℕ, pg (k + 1) [t] = ([], []))
    (p3 : ∀ i k : ℕ, pg (k + 1) [4, i] = ([], []))
    (p4 : ∀ (t i k : ℕ) (rest : List ℕ), ¬ t = 4 →
      pg (k + 1) (t :: i :: rest) = ([t, i] :: (pg k rest).1, (pg k rest).2))
    (p5 : ∀ (i j k : ℕ) (rest : List ℕ),
      pg (k + 1) (4 :: i :: j :: rest) = ([4, i, j] :: (pg k rest).1, (pg k rest).2)) :
    ∀ (k : ℕ) (ts : List ℕ), ∀ rec ∈ (pg k ts).1,
      (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]) := by
  intro k
  induction k with
  | zero =>
      intro ts rec hrec
      have e : (pg 0 ts).1 = ([] : List (List ℕ)) := congrArg Prod.fst (p0 ts)
      rw [e] at hrec
      cases hrec
  | succ k ih =>
      intro ts rec hrec
      rcases ts with _ | ⟨t, ts'⟩
      · have e : (pg (k + 1) ([] : List ℕ)).1 = ([] : List (List ℕ)) :=
          congrArg Prod.fst (p1 k)
        rw [e] at hrec
        cases hrec
      · rcases ts' with _ | ⟨i, rest⟩
        · have e : (pg (k + 1) [t]).1 = ([] : List (List ℕ)) := congrArg Prod.fst (p2 t k)
          rw [e] at hrec
          cases hrec
        · by_cases ht : t = 4
          · subst ht
            rcases rest with _ | ⟨j, rest'⟩
            · have e : (pg (k + 1) [4, i]).1 = ([] : List (List ℕ)) :=
                congrArg Prod.fst (p3 i k)
              rw [e] at hrec
              cases hrec
            · have e : (pg (k + 1) (4 :: i :: j :: rest')).1
                  = [4, i, j] :: (pg k rest').1 := congrArg Prod.fst (p5 i j k rest')
              rw [e] at hrec
              rcases List.mem_cons.1 hrec with h | h
              · exact Or.inr ⟨i, j, h⟩
              · exact ih rest' rec h
          · have e : (pg (k + 1) (t :: i :: rest)).1 = [t, i] :: (pg k rest).1 :=
              congrArg Prod.fst (p4 t i k rest ht)
            rw [e] at hrec
            rcases List.mem_cons.1 hrec with h | h
            · exact Or.inl ⟨t, i, ht, h⟩
            · exact ih rest rec h

/-- THE RESIDUE OF A TRUNCATING PARSE IS ONE OF THE THREE REJECTING TOKEN SHAPES.  When
the fuel STRICTLY exceeds the record count the parser stopped because the SOURCE ran out,
not because the fuel did, so what is left after the completed records is a partial record:
empty, a lone tag, or a CNOT missing its second index.  This is precisely the hypothesis
`ROLLBACK` takes on its rejecting tail, and it is the step `FLAT-1b` (3) does not make --
that conjunct produces a residue but says nothing about its shape. -/
private lemma pgResid (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
    (p0 : ∀ ts : List ℕ, pg 0 ts = ([], ts))
    (p1 : ∀ k : ℕ, pg (k + 1) ([] : List ℕ) = ([], []))
    (p2 : ∀ t k : ℕ, pg (k + 1) [t] = ([], []))
    (p3 : ∀ i k : ℕ, pg (k + 1) [4, i] = ([], []))
    (p4 : ∀ (t i k : ℕ) (rest : List ℕ), ¬ t = 4 →
      pg (k + 1) (t :: i :: rest) = ([t, i] :: (pg k rest).1, (pg k rest).2))
    (p5 : ∀ (i j k : ℕ) (rest : List ℕ),
      pg (k + 1) (4 :: i :: j :: rest) = ([4, i, j] :: (pg k rest).1, (pg k rest).2)) :
    ∀ (k : ℕ) (ts : List ℕ), ((pg k ts).1).length + 1 ≤ k →
      ∃ bad : List ℕ, ts = ((pg k ts).1).flatten ++ bad
        ∧ (bad = [] ∨ (∃ t : ℕ, bad = [t]) ∨ (∃ i : ℕ, bad = [4, i])) := by
  intro k
  induction k with
  | zero => intro ts h; exact absurd h (by omega)
  | succ k ih =>
      intro ts h
      rcases ts with _ | ⟨t, ts'⟩
      · have e : (pg (k + 1) ([] : List ℕ)).1 = ([] : List (List ℕ)) :=
          congrArg Prod.fst (p1 k)
        exact ⟨[], by simp [e], Or.inl rfl⟩
      · rcases ts' with _ | ⟨i, rest⟩
        · have e : (pg (k + 1) [t]).1 = ([] : List (List ℕ)) := congrArg Prod.fst (p2 t k)
          exact ⟨[t], by simp [e], Or.inr (Or.inl ⟨t, rfl⟩)⟩
        · by_cases ht : t = 4
          · subst ht
            rcases rest with _ | ⟨j, rest'⟩
            · have e : (pg (k + 1) [4, i]).1 = ([] : List (List ℕ)) :=
                congrArg Prod.fst (p3 i k)
              exact ⟨[4, i], by simp [e], Or.inr (Or.inr ⟨i, rfl⟩)⟩
            · have e : (pg (k + 1) (4 :: i :: j :: rest')).1
                  = [4, i, j] :: (pg k rest').1 := congrArg Prod.fst (p5 i j k rest')
              rw [e] at h
              simp only [List.length_cons] at h
              obtain ⟨bad, hb, hs⟩ := ih rest' (by omega)
              refine ⟨bad, ?_, hs⟩
              have hf : ((pg (k + 1) (4 :: i :: j :: rest')).1).flatten ++ bad
                  = 4 :: i :: j :: (((pg k rest').1).flatten ++ bad) := by
                rw [e]; simp
              rw [hf, ← hb]
          · have e : (pg (k + 1) (t :: i :: rest)).1 = [t, i] :: (pg k rest).1 :=
              congrArg Prod.fst (p4 t i k rest ht)
            rw [e] at h
            simp only [List.length_cons] at h
            obtain ⟨bad, hb, hs⟩ := ih rest (by omega)
            refine ⟨bad, ?_, hs⟩
            have hf : ((pg (k + 1) (t :: i :: rest)).1).flatten ++ bad
                = t :: i :: (((pg k rest).1).flatten ++ bad) := by
              rw [e]; simp
            rw [hf, ← hb]


theorem _root_.BQPReferenceValidation.candidate44
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
  -- THE WELL-FORMEDNESS DISJUNCT, DISCHARGED ONCE AND FOR ALL (conjunct 7).  This is the
  -- compiler-side content of `MACH-A5d`'s dispatch totality: the predicate the repaired
  -- gate loops need is exactly the predicate the parser already guarantees, so no caller
  -- carries a tag side condition and `MACH-B4e`'s compound `hBAD` antecedent collapses.
  have pgsh := pgShape pg pg0 pg1 pg2 pg3 pg4 pg5
  -- THE COMPILED WORD'S LENGTH IN THE PIECES EVERY BOUND NEEDS, hoisted because all three
  -- of `key`, `keyT` and `back` want it.
  have lens : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      (encCompile (unL w) (unR w)).length
        = 4 * ((Lw (unR w ++ List.replicate (anc + 1) false)).length
            + ((unR w).length + (anc + 1))
            + ((((pg ng rest).1).map blkN).flatten).length + (2 * out + 1)
            + ((((((pg ng rest).1).reverse).map blkAN)).flatten).length
            + (Ew (unR w ++ List.replicate (anc + 1) false)).length
            + ((unR w).length + (anc + 1))) := by
    intro w anc out ng rest hup
    have hcomp := h3 (unL w) (unR w) anc out ng rest hup
    rw [hcomp, he]
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  -- THE SHARED TAIL.  `ROLLBACK` exits at `lV1` configuration-identical to the accepting
  -- exit, so from the weld label `lGTz` onwards the accepting run and the truncating run
  -- are literally the same run.  This states that once: given ANY front half that reaches
  -- `lGTz` inside the front budget with the three live ports in the accepting shape, the
  -- back half, the wire identity and the packaging go through.  Both branches below are
  -- one application of it.
  have back : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ) (NA : ℕ) (u : tm.σ)
      (T : ∀ k, List (tm.Γ k)),
      unpack (unL w) = anc :: out :: ng :: rest →
      (∀ rec ∈ (pg ng rest).1,
        (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
      ((pg ng rest).1).length + (E (((pg ng rest).1).flatten)).length + anc + out
          ≤ w.length →
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[NA]
          (Option.some (⟨Option.some lS, tm.initialState,
            (Turing.initList tm (List.map ea.invFun w)).stk⟩ : Cfg tm.Γ tm.Λ tm.σ))
        = Option.some (⟨Option.some lGTz, u, T⟩ : Cfg tm.Γ tm.Λ tm.σ) →
      NA ≤ 160 * w.length + 16 * (encCompile (unL w) (unR w)).length + 64 →
      T kxin = (((pg ng rest).1).map encx).flatten →
      T kpd2 = (unR w ++ List.replicate (anc + 1) false).map o2 →
      T kopc = List.replicate out c0 ++ (c8 :: (List.replicate out c1
          ++ ((((pg ng rest).1).reverse.map (fun r => (blk r).reverse)).flatten
            ++ (List.replicate ((unR w).length + (anc + 1)) c0
                ++ (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).reverse)))) →
      (∀ k, k ≠ kxin → k ≠ kpd2 → k ≠ kopc → T k = []) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (256 * w.length + 32 * (encCompile (unL w) (unR w)).length + 128)) := by
    intro w anc out ng rest NA u T hup hmem hsz rA hNA hTx hTf hTm hTe
    have hcomp := h3 (unL w) (unR w) anc out ng rest hup
    obtain ⟨hl, hv, hk0, hko⟩ := hIL (List.map ea.invFun w)
    have hpl : (unR w ++ List.replicate (anc + 1) false).length
        = ((unR w).length + (anc + 1)) := by simp
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
        u T hmem rfl (by rw [hTm, hpl]) hTx hTf rfl hTe
    have hw := hWID (unR w
        ++ List.replicate (anc + 1) false) ((unR w).length + (anc + 1)) out ((pg ng rest).1)
    have hout : T8 tm.k₁ = List.map eb.invFun (encCompile (unL w) (unR w)) := by
      rw [tBn, hw, hWIRE, hcomp]
    have hstart : (Turing.initList tm (List.map ea.invFun w))
        = (⟨Option.some lS, tm.initialState,
            (Turing.initList tm (List.map ea.invFun w)).stk⟩ : Cfg tm.Γ tm.Λ tm.σ) := by
      rw [← hmain, ← hl, ← hv]
      rfl
    have rfull := mbChainN (rfl : NA + NB = NA + NB) rA rB
    rw [← hstart] at rfull
    have hrun := hOIT (List.map ea.invFun w)
      (List.map eb.invFun (encCompile (unL w) (unR w))) lH T8 (NA + NB) hhalt rfull hout tBe
    have hURw := hunRl w
    have hencxl : ((((pg ng rest).1).map encx).flatten).length
        = (E (((pg ng rest).1).flatten)).length := by
      have hq := congrArg List.length (hglx ((pg ng rest).1))
      simpa using hq.symm
    have hmapo1 : ((unR w ++ List.replicate (anc + 1) false).map o1).length
        = ((unR w).length + (anc + 1)) := by simp
    have hmapef : ((unR w ++ List.replicate (anc + 1) false).map ef).length
        = ((unR w).length + (anc + 1)) := by simp
    have hLfl : (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).length
        = (Lw (unR w ++ List.replicate (anc + 1) false)).length := by
      rw [hLf]; simp
    have hEfl : (Ef ((unR w ++ List.replicate (anc + 1) false).map o1)).length
        = (Ew (unR w ++ List.replicate (anc + 1) false)).length := by
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
                ++ List.replicate ((unR w).length + (anc + 1)) c0)))).length
        = (Lw (unR w ++ List.replicate (anc + 1) false)).length
            + ((unR w).length + (anc + 1))
            + ((((pg ng rest).1).map blkN).flatten).length + (2 * out + 1)
            + ((((((pg ng rest).1).reverse).map blkAN)).flatten).length
            + (Ew (unR w ++ List.replicate (anc + 1) false)).length
            + ((unR w).length + (anc + 1)) := by
      rw [hw]
      simp only [List.length_map, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hOl := lens w anc out ng rest hup
    rw [hpl] at bB
    exact bumpTime (by omega) hrun
  -- BRANCH ONE, THE ACCEPTING RUN: `MACH-B4e`'s, unchanged except that the well-formedness
  -- premise is no longer a case hypothesis but a THEOREM (`pgsh`), because at `MACH-A5d`
  -- the gate loops cover every tag.  So the case split below is on TRUNCATION ALONE.
  have key : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ((pg ng rest).1).length = ng →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (256 * w.length + 32 * (encCompile (unL w) (unR w)).length + 128)) := by
    intro w anc out ng rest hup hnt
    have hmem := pgsh ng rest
    obtain ⟨recs, tl, hrecs, hrl, hdec⟩ := hSEAM unL w anc out ng rest hup hnt
    subst hrecs
    obtain ⟨hl, hv, hk0, hko⟩ := hIL (List.map ea.invFun w)
    have hinpec : (Turing.initList tm (List.map ea.invFun w)).stk tm.k₀ = w.map ec := by
      rw [hk0]
      exact List.map_congr_left (fun b _ => hea b)
    have hpl : (unR w ++ List.replicate (anc + 1) false).length
        = ((unR w).length + (anc + 1)) := by simp
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
        hexh w anc out ((pg ng rest).1) tl
        (unR w ++ List.replicate (anc + 1) false) tm.initialState
        ((Turing.initList tm (List.map ea.invFun w)).stk) rfl hdec hmem hinpec hko
    rw [hpl] at bA tAm
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
      have hq := congrArg List.length (hgl ((pg ng rest).1))
      simpa using hq.symm
    have hmapo1 : ((unR w ++ List.replicate (anc + 1) false).map o1).length
        = ((unR w).length + (anc + 1)) := by simp
    have hmapef : ((unR w ++ List.replicate (anc + 1) false).map ef).length
        = ((unR w).length + (anc + 1)) := by simp
    have hLfl : (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).length
        = (Lw (unR w ++ List.replicate (anc + 1) false)).length := by
      rw [hLf]; simp
    have hOl := lens w anc out ng rest hup
    exact back w anc out ng rest NA u T hup hmem (by omega) rA (by omega) tAx tAf tAm tAe
  -- BRANCH TWO, THE TRUNCATING RUN -- `MACH-B4e`'s `hBAD`, NOW PROVED.  Ten phases, each
  -- taken in the form its own accepted theorem concludes, chained on EXACT exponents.  The
  -- head is `hSPLIT`, `hFIELDS`, `ROLLBACK`; from `lV1` on it is byte for byte the
  -- accepting chain, which is what "configuration-identical exit" buys.
  have keyT : ∀ (w : List Bool) (anc out ng : ℕ) (rest : List ℕ),
      unpack (unL w) = anc :: out :: ng :: rest →
      ¬ (((pg ng rest).1).length = ng) →
      Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (256 * w.length + 32 * (encCompile (unL w) (unR w)).length + 128)) := by
    intro w anc out ng rest hup hnt
    have hmem := pgsh ng rest
    have hle := hLen ng rest
    have hlt : ((pg ng rest).1).length + 1 ≤ ng := by omega
    obtain ⟨bad, hb, hbs⟩ := pgResid pg pg0 pg1 pg2 pg3 pg4 pg5 ng rest hlt
    obtain ⟨m, hm⟩ := hSHAPEg (unL w)
    rw [hup, e1, e1, e1] at hm
    have hdec : unL w = List.replicate anc true ++ false :: (List.replicate out true
        ++ false :: (List.replicate ng true ++ false ::
          (E (((pg ng rest).1).flatten ++ bad) ++ List.replicate m true))) := by
      rw [← hb]
      simpa only [List.append_assoc, List.cons_append] using hm
    have hEa : E ((((pg ng rest).1).flatten) ++ bad)
        = E (((pg ng rest).1).flatten) ++ E bad := encApp E e0 e1 _ _
    have hUlT : (unL w).length = anc + out + ng + 3
        + (E (((pg ng rest).1).flatten)).length + (E bad).length + m := by
      rw [hdec, hEa]
      simp only [List.length_append, List.length_cons, List.length_replicate]
      omega
    have hULw := hunLl w
    have hURw := hunRl w
    have htrl := htr ((pg ng rest).1)
    obtain ⟨hl, hv, hk0, hko⟩ := hIL (List.map ea.invFun w)
    have hinpec : (Turing.initList tm (List.map ea.invFun w)).stk tm.k₀ = w.map ec := by
      rw [hk0]
      exact List.map_congr_left (fun b _ => hea b)
    have hpl : (unR w ++ List.replicate (anc + 1) false).length
        = ((unR w).length + (anc + 1)) := by simp
    -- PHASE (A): the input demultiplexer, `lS` to `lF1`
    obtain ⟨v1, T1, r1, t1a, t1p, t1q, t1b, t1c, fr1⟩ :=
      hSPLIT w tm.initialState ((Turing.initList tm (List.map ea.invFun w)).stk)
        hinpec (hko kscA nap.symm) (hko kscB naq.symm)
    have h1a : T1 tm.k₀ = [] := t1a
    have h1p : T1 kscA = [] := t1p
    have h1q : T1 kscB = [] := t1q
    have h1b : T1 ksrc = (unL w).map es := by
      rw [t1b, hko ksrc nab.symm, List.append_nil]
    have h1c : T1 kxin = (unR w).map ex := by
      rw [t1c, hko kxin nac.symm, List.append_nil]
    have h1d : T1 khld = [] :=
      (fr1 khld nad.symm ndp ndq nbd.symm ncd.symm).trans (hko khld nad.symm)
    have h1e : T1 kpd1 = [] :=
      (fr1 kpd1 nae.symm nep neq nbe.symm nce.symm).trans (hko kpd1 nae.symm)
    have h1f : T1 kpd2 = [] :=
      (fr1 kpd2 naf.symm nfp nfq nbf.symm ncf.symm).trans (hko kpd2 naf.symm)
    have h1g : T1 kqc = [] :=
      (fr1 kqc nag.symm ngp ngq nbg.symm ncg.symm).trans (hko kqc nag.symm)
    have h1h : T1 kfu = [] :=
      (fr1 kfu nah.symm nhp nhq nbh.symm nch.symm).trans (hko kfu nah.symm)
    have h1i : T1 ktok = [] :=
      (fr1 ktok nai.symm nip niq nbi.symm nci.symm).trans (hko ktok nai.symm)
    have h1j : T1 kidx = [] :=
      (fr1 kidx naj.symm njp njq nbj.symm ncj.symm).trans (hko kidx naj.symm)
    have h1m : T1 kopc = [] :=
      (fr1 kopc nam.symm nmp nmq nbm.symm ncm.symm).trans (hko kopc nam.symm)
    have h1n : T1 tm.k₁ = [] :=
      (fr1 tm.k₁ nan.symm nnp nnq nbn.symm ncn.symm).trans (hko tm.k₁ nan.symm)
    -- PHASE (B): the three-field header parser, `lF1` to `lU`
    have h1b' : T1 ksrc = (List.replicate anc true ++ false :: (List.replicate out true
        ++ false :: (List.replicate ng true ++ false ::
          (E (((pg ng rest).1).flatten ++ bad) ++ List.replicate m true)))).map es := by
      rw [h1b, hdec]
    obtain ⟨v2, T2, r2, t2b, t2c, t2d, t2g, t2h, t2e, t2f, fr2⟩ :=
      hFIELDS anc out ng (E (((pg ng rest).1).flatten ++ bad) ++ List.replicate m true)
        (unR w) v1 T1 h1b' h1c h1d
    have h2b : T2 ksrc = (E (((pg ng rest).1).flatten ++ bad)
        ++ List.replicate m true).map es := t2b
    have h2c : T2 kxin = [] := t2c
    have h2d : T2 khld = [] := t2d
    have h2g : T2 kqc = List.replicate out mq := by rw [t2g, h1g, List.append_nil]
    have h2h : T2 kfu = List.replicate ng mfu := by rw [t2h, h1h, List.append_nil]
    have h2e : T2 kpd1 = (unR w ++ List.replicate (anc + 1) false).map o1 := by
      rw [t2e, h1e, List.append_nil]
    have h2f : T2 kpd2 = (unR w ++ List.replicate (anc + 1) false).map o2 := by
      rw [t2f, h1f, List.append_nil]
    have h2a : T2 tm.k₀ = [] := (fr2 tm.k₀ nab nac nad nag nah nae naf).trans h1a
    have h2i : T2 ktok = [] :=
      (fr2 ktok nbi.symm nci.symm ndi.symm ngi.symm nhi.symm nei.symm
        nfi.symm).trans h1i
    have h2j : T2 kidx = [] :=
      (fr2 kidx nbj.symm ncj.symm ndj.symm ngj.symm nhj.symm nej.symm
        nfj.symm).trans h1j
    have h2m : T2 kopc = [] :=
      (fr2 kopc nbm.symm ncm.symm ndm.symm ngm.symm nhm.symm nem.symm
        nfm.symm).trans h1m
    have h2n : T2 tm.k₁ = [] :=
      (fr2 tm.k₁ nbn.symm ncn.symm ndn.symm ngn.symm nhn.symm nen.symm
        nfn.symm).trans h1n
    have h2p : T2 kscA = [] :=
      (fr2 kscA nbp.symm ncp.symm ndp.symm ngp.symm nhp.symm nep.symm
        nfp.symm).trans h1p
    have h2q : T2 kscB = [] :=
      (fr2 kscB nbq.symm ncq.symm ndq.symm ngq.symm nhq.symm neq.symm
        nfq.symm).trans h1q
    -- PHASE (C): `ROLLBACK`, `lU` to `lV1`.  The fuel port comes out EMPTY.
    obtain ⟨v3, T3, r3, t3i, t3d, t3p, t3b, t3h, fr3P⟩ :=
      hROLL hPARSE ((pg ng rest).1) bad m ng (ng - ((pg ng rest).1).length - 1)
        v2 T2 hmem hbs hlt (by omega) h2h h2b h2d h2p h2i
    have fr3 : ∀ k, k ≠ ksrc → k ≠ khld → k ≠ kfu → k ≠ ktok → k ≠ kscA →
        T3 k = T2 k := by
      intro k q1 q2 q3 q4 q5
      exact fr3P (fun A => A k = T2 k)
        (fun A B hab hA => (hab k q1 q2 q3 q4 q5).symm.trans hA) rfl
    have h3i : T3 ktok = (E (((pg ng rest).1).flatten)).map eo := by
      rw [t3i, ← hb]
    have h3d : T3 khld = [] := t3d
    have h3p : T3 kscA = [] := t3p
    have h3b : T3 ksrc = [] := t3b
    have h3h : T3 kfu = [] := t3h
    have h3a : T3 tm.k₀ = [] := (fr3 tm.k₀ nab nad nah nai nap).trans h2a
    have h3c : T3 kxin = [] := (fr3 kxin nbc.symm ncd nch nci ncp).trans h2c
    have h3e : T3 kpd1 = (unR w ++ List.replicate (anc + 1) false).map o1 :=
      (fr3 kpd1 nbe.symm nde.symm neh nei nep).trans h2e
    have h3f : T3 kpd2 = (unR w ++ List.replicate (anc + 1) false).map o2 :=
      (fr3 kpd2 nbf.symm ndf.symm nfh nfi nfp).trans h2f
    have h3g : T3 kqc = List.replicate out mq :=
      (fr3 kqc nbg.symm ndg.symm ngh ngi ngp).trans h2g
    have h3j : T3 kidx = [] := (fr3 kidx nbj.symm ndj.symm nhj.symm nij.symm njp).trans h2j
    have h3m : T3 kopc = [] := (fr3 kopc nbm.symm ndm.symm nhm.symm nim.symm nmp).trans h2m
    have h3n : T3 tm.k₁ = [] :=
      (fr3 tm.k₁ nbn.symm ndn.symm nhn.symm nin.symm nnp).trans h2n
    have h3q : T3 kscB = [] :=
      (fr3 kscB nbq.symm ndq.symm nhq.symm niq.symm npq.symm).trans h2q
    -- PHASE (D): the token-stream duplicator, `lV1` to `lVp`
    obtain ⟨v4, T4, r4, t4i, t4c, t4d, fr4⟩ :=
      hDUPtok (E (((pg ng rest).1).flatten)) v3 T3 h3i h3d
    have h4i : T4 ktok = (E (((pg ng rest).1).flatten)).map eo := t4i
    have h4c : T4 kxin = (E (((pg ng rest).1).flatten)).map ex := by
      rw [t4c, h3c, List.append_nil]
    have h4d : T4 khld = [] := t4d
    have h4a := (fr4 tm.k₀ nai nad nac).trans h3a
    have h4b := (fr4 ksrc nbi nbd nbc).trans h3b
    have h4e := (fr4 kpd1 nei nde.symm nce.symm).trans h3e
    have h4f := (fr4 kpd2 nfi ndf.symm ncf.symm).trans h3f
    have h4g := (fr4 kqc ngi ndg.symm ncg.symm).trans h3g
    have h4h := (fr4 kfu nhi ndh.symm nch.symm).trans h3h
    have h4j := (fr4 kidx nij.symm ndj.symm ncj.symm).trans h3j
    have h4m := (fr4 kopc nim.symm ndm.symm ncm.symm).trans h3m
    have h4n := (fr4 tm.k₁ nin.symm ndn.symm ncn.symm).trans h3n
    have h4p := (fr4 kscA nip.symm ndp.symm ncp.symm).trans h3p
    have h4q := (fr4 kscB niq.symm ndq.symm ncq.symm).trans h3q
    -- PHASE (E): the padded-copy duplicator, `lVp` to `lL`
    obtain ⟨v5, T5, r5, t5e, t5h, t5a, fr5⟩ :=
      hDUPpad (unR w ++ List.replicate (anc + 1) false) v4 T4 h4e h4a
    have h5e : T5 kpd1 = (unR w ++ List.replicate (anc + 1) false).map o1 := t5e
    have h5h : T5 kfu = (unR w ++ List.replicate (anc + 1) false).map ef := by
      rw [t5h, h4h, List.append_nil]
    have h5a : T5 tm.k₀ = [] := t5a
    have h5b := (fr5 ksrc nbe nab.symm nbh).trans h4b
    have h5c := (fr5 kxin nce nac.symm nch).trans h4c
    have h5d := (fr5 khld nde nad.symm ndh).trans h4d
    have h5f := (fr5 kpd2 nef.symm naf.symm nfh).trans h4f
    have h5g := (fr5 kqc neg.symm nag.symm ngh).trans h4g
    have h5i := (fr5 ktok nei.symm nai.symm nhi.symm).trans h4i
    have h5j := (fr5 kidx nej.symm naj.symm nhj.symm).trans h4j
    have h5m := (fr5 kopc nem.symm nam.symm nhm.symm).trans h4m
    have h5n := (fr5 tm.k₁ nen.symm nan.symm nhn.symm).trans h4n
    have h5p := (fr5 kscA nep.symm nap.symm nhp.symm).trans h4p
    have h5q := (fr5 kscB neq.symm naq.symm nhq.symm).trans h4q
    -- PHASE (F): the `L` sweep, `lL` to `lZa`
    have hmemo1 : ∀ y ∈ (unR w ++ List.replicate (anc + 1) false).map o1,
        y = o1 true ∨ y = o1 false := by
      intro y hy
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
      cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
    obtain ⟨v6, T6, r6, t6e, t6m, fr6⟩ :=
      hLsw ((unR w ++ List.replicate (anc + 1) false).map o1) hmemo1 v5 T5 h5e
    have h6e : T6 kpd1 = [] := t6e
    have h6m : T6 kopc
        = (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).reverse := by
      rw [t6m, h5m, List.append_nil]
    have h6a := (fr6 tm.k₀ nae nam).trans h5a
    have h6b := (fr6 ksrc nbe nbm).trans h5b
    have h6c := (fr6 kxin nce ncm).trans h5c
    have h6d := (fr6 khld nde ndm).trans h5d
    have h6f := (fr6 kpd2 nef.symm nfm).trans h5f
    have h6g := (fr6 kqc neg.symm ngm).trans h5g
    have h6h := (fr6 kfu neh.symm nhm).trans h5h
    have h6i := (fr6 ktok nei.symm nim).trans h5i
    have h6j := (fr6 kidx nej.symm njm).trans h5j
    have h6n := (fr6 tm.k₁ nen.symm nmn.symm).trans h5n
    have h6p := (fr6 kscA nep.symm nmp.symm).trans h5p
    have h6q := (fr6 kscB neq.symm nmq.symm).trans h5q
    -- PHASE (G): the first zero run, `lZa` to `lGT`.  RESUME 538 MODE (i) LIVES HERE:
    -- `T6 kfu` is now EXACTLY the padded copy, with no leftover fuel behind it.
    obtain ⟨v7, T7, r7, t7h, t7m, fr7⟩ := hZ1 v6 T6
    rw [h6h] at r7 t7m
    have h7h : T7 kfu = [] := t7h
    have h7m : T7 kopc = List.replicate
        ((unR w ++ List.replicate (anc + 1) false)).length c0
        ++ (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).reverse := by
      rw [t7m, h6m, List.length_map]
    have h7a := (fr7 tm.k₀ nah nam).trans h6a
    have h7b := (fr7 ksrc nbh nbm).trans h6b
    have h7c := (fr7 kxin nch ncm).trans h6c
    have h7d := (fr7 khld ndh ndm).trans h6d
    have h7e := (fr7 kpd1 neh nem).trans h6e
    have h7f := (fr7 kpd2 nfh nfm).trans h6f
    have h7g := (fr7 kqc ngh ngm).trans h6g
    have h7i := (fr7 ktok nhi.symm nim).trans h6i
    have h7j := (fr7 kidx nhj.symm njm).trans h6j
    have h7n := (fr7 tm.k₁ nhn.symm nmn.symm).trans h6n
    have h7p := (fr7 kscA nhp.symm nmp.symm).trans h6p
    have h7q := (fr7 kscB nhq.symm nmq.symm).trans h6q
    -- PHASE (H): the mirrored forward gate loop, `lGT` to `lQX`
    have h7i' : T7 ktok = ((((pg ng rest).1)).map enc).flatten := by rw [h7i, hgl]
    obtain ⟨N8, v8, T8, b8, r8, t8i, t8j, t8p, t8q, t8m, fr8⟩ :=
      hFWD ((pg ng rest).1) v7 T7 hmem h7i' h7j h7p h7q
    have h8i : T8 ktok = [] := t8i
    have h8j : T8 kidx = [] := t8j
    have h8p : T8 kscA = [] := t8p
    have h8q : T8 kscB = [] := t8q
    have h8m : T8 kopc = ((((pg ng rest).1)).reverse.map (fun r => (blk r).reverse)).flatten
        ++ (List.replicate ((unR w ++ List.replicate (anc + 1) false)).length c0
        ++ (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).reverse) := by
      rw [t8m, h7m]
    have h8a := (fr8 tm.k₀ nai naj nap naq nam).trans h7a
    have h8b := (fr8 ksrc nbi nbj nbp nbq nbm).trans h7b
    have h8c := (fr8 kxin nci ncj ncp ncq ncm).trans h7c
    have h8d := (fr8 khld ndi ndj ndp ndq ndm).trans h7d
    have h8e := (fr8 kpd1 nei nej nep neq nem).trans h7e
    have h8f := (fr8 kpd2 nfi nfj nfp nfq nfm).trans h7f
    have h8g := (fr8 kqc ngi ngj ngp ngq ngm).trans h7g
    have h8h := (fr8 kfu nhi nhj nhp nhq nhm).trans h7h
    have h8n := (fr8 tm.k₁ nin.symm njn.symm nnp nnq nmn.symm).trans h7n
    -- PHASE (I): the output-count duplicator, `lQX` to `lPa`
    obtain ⟨v9, T9, r9, t9p, t9q, t9g, fr9⟩ := hDUPq out v8 T8 h8g h8p h8q
    have h9p : T9 kscA = List.replicate out msA := t9p
    have h9q : T9 kscB = List.replicate out msB := t9q
    have h9g : T9 kqc = [] := t9g
    have h9a := (fr9 tm.k₀ nag nap naq).trans h8a
    have h9b := (fr9 ksrc nbg nbp nbq).trans h8b
    have h9c := (fr9 kxin ncg ncp ncq).trans h8c
    have h9d := (fr9 khld ndg ndp ndq).trans h8d
    have h9e := (fr9 kpd1 neg nep neq).trans h8e
    have h9f := (fr9 kpd2 nfg nfp nfq).trans h8f
    have h9h := (fr9 kfu ngh.symm nhp nhq).trans h8h
    have h9i := (fr9 ktok ngi.symm nip niq).trans h8i
    have h9j := (fr9 kidx ngj.symm njp njq).trans h8j
    have h9m := (fr9 kopc ngm.symm nmp nmq).trans h8m
    have h9n := (fr9 tm.k₁ ngn.symm nnp nnq).trans h8n
    -- PHASE (J): the output-wire marker, `lPa` to the weld label `lGTz`
    obtain ⟨vA, TA, rJ, tAp, tAq, tAm, frA⟩ := hMark out v9 T9 h9p h9q
    have hAp : TA kscA = [] := tAp
    have hAq : TA kscB = [] := tAq
    have hAm : TA kopc = List.replicate out c0 ++ (c8 :: (List.replicate out c1
        ++ (((((pg ng rest).1)).reverse.map (fun r => (blk r).reverse)).flatten
          ++ (List.replicate ((unR w ++ List.replicate (anc + 1) false)).length c0
            ++ (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).reverse)))) := by
      rw [tAm, h9m]
    have hAa := (frA tm.k₀ nap naq nam).trans h9a
    have hAb := (frA ksrc nbp nbq nbm).trans h9b
    have hAc := (frA kxin ncp ncq ncm).trans h9c
    have hAd := (frA khld ndp ndq ndm).trans h9d
    have hAe := (frA kpd1 nep neq nem).trans h9e
    have hAf := (frA kpd2 nfp nfq nfm).trans h9f
    have hAg := (frA kqc ngp ngq ngm).trans h9g
    have hAh := (frA kfu nhp nhq nhm).trans h9h
    have hAi := (frA ktok nip niq nim).trans h9i
    have hAj := (frA kidx njp njq njm).trans h9j
    have hAn := (frA tm.k₁ nnp nnq nmn.symm).trans h9n
    rw [hpl] at hAm
    have hEMP : ∀ k, k ≠ kxin → k ≠ kpd2 → k ≠ kopc → TA k = [] := by
      intro k hk1 hk2 hk3
      rcases hexh k with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hAa
      · exact hAb
      · exact absurd rfl hk1
      · exact hAd
      · exact hAe
      · exact absurd rfl hk2
      · exact hAg
      · exact hAh
      · exact hAi
      · exact hAj
      · exact absurd rfl hk3
      · exact hAn
      · exact hAp
      · exact hAq
    have rall := mbChainN rfl (mbChainN rfl (mbChainN rfl (mbChainN rfl (mbChainN rfl
      (mbChainN rfl (mbChainN rfl (mbChainN rfl (mbChainN rfl r1 r2) r3) r4) r5)
        r6) r7) r8) r9) rJ
    have hencl : ((((pg ng rest).1).map enc).flatten).length
        = (E (((pg ng rest).1).flatten)).length := by
      have hq := congrArg List.length (hgl ((pg ng rest).1))
      simpa using hq.symm
    have hmapo1 : ((unR w ++ List.replicate (anc + 1) false).map o1).length
        = ((unR w).length + (anc + 1)) := by simp
    have hmapef : ((unR w ++ List.replicate (anc + 1) false).map ef).length
        = ((unR w).length + (anc + 1)) := by simp
    have hLfl : (Lf ((unR w ++ List.replicate (anc + 1) false).map o1)).length
        = (Lw (unR w ++ List.replicate (anc + 1) false)).length := by
      rw [hLf]; simp
    have hOl := lens w anc out ng rest hup
    refine back w anc out ng rest _ vA TA hup hmem ?_ rall ?_
      (by rw [hAc, hglx]) hAf hAm hEMP
    · omega
    · omega
  -- THE THREE REFUTATION-FIRST WITNESS COMPUTATIONS (RESUME 498, 538), DONE BEFORE THE
  -- CHAIN WAS TRUSTED AND BANKED AS CONJUNCTS SO THEY ARE CHECKED AND NOT ASSERTED.
  have hw2 : pg 1 [0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ) := by
    have hq := pg4 0 0 0 [] (by omega)
    rw [pg0] at hq
    simpa using hq
  have hw2f : (pg 1 [0, 0]).1 = ([[0, 0]] : List (List ℕ)) := by simp [hw2]
  have hw7 : pg 1 [7, 0] = (([[7, 0]], []) : List (List ℕ) × List ℕ) := by
    have hq := pg4 7 0 0 [] (by omega)
    rw [pg0] at hq
    simpa using hq
  have hw7f : (pg 1 [7, 0]).1 = ([[7, 0]] : List (List ℕ)) := by simp [hw7]
  have hw10 : pg 1 [0] = (([], []) : List (List ℕ) × List ℕ) := pg2 0 0
  have hw20 : pg 2 [0] = (([], []) : List (List ℕ) × List ℕ) := pg2 0 1
  have hw30 : pg 2 [0, 0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ) := by
    have hq : pg 2 [0, 0, 0] = ([0, 0] :: (pg 1 [0]).1, (pg 1 [0]).2) :=
      pg4 0 0 1 [0] (by omega)
    simp [hq, hw10]
  have e20 : (pg 2 [0]).1 = ([] : List (List ℕ)) := by simp [hw20]
  have e30 : (pg 2 [0, 0, 0]).1 = ([[0, 0]] : List (List ℕ)) := by simp [hw30]
  have hNV4 : pg 1 [0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ((pg 1 [0, 0]).1).length = 1 := ⟨hw2, by simp [hw2f]⟩
  have hNV5 : pg 1 [7, 0] = (([[7, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ((pg 1 [7, 0]).1).length = 1
      ∧ (∀ rec ∈ (pg 1 [7, 0]).1,
          (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j]))
      ∧ ¬ (∀ rec ∈ (pg 1 [7, 0]).1,
          (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) := by
    refine ⟨hw7, by simp [hw7f], pgsh 1 [7, 0], ?_⟩
    intro hall
    have hmem7 : ([7, 0] : List ℕ) ∈ (pg 1 [7, 0]).1 := by
      rw [hw7f]
      exact List.mem_cons.mpr (Or.inl rfl)
    rcases hall [7, 0] hmem7 with ⟨t, i, ht, hq⟩ | ⟨i, j, hq⟩
    · injection hq with q1 q2
      omega
    · injection hq with q1 q2
      omega
  have hNV6 : pg 2 [0] = (([], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 2 [0]).1).length = 2)
      ∧ ((pg 2 [0]).1).length + 1 ≤ 2
      ∧ (2 : ℕ) = ((pg 2 [0]).1).length + 1 + 1
      ∧ pg 2 [0, 0, 0] = (([[0, 0]], []) : List (List ℕ) × List ℕ)
      ∧ ¬ (((pg 2 [0, 0, 0]).1).length = 2)
      ∧ ((pg 2 [0, 0, 0]).1).length + 1 ≤ 2
      ∧ (2 : ℕ) = ((pg 2 [0, 0, 0]).1).length + 0 + 1 :=
    ⟨hw20, by simp [e20], by simp [e20], by simp [e20],
      hw30, by simp [e30], by simp [e30], by simp [e30]⟩
  have hsplit : ∀ n : ℕ, (256 + pr) * n = 256 * n + pr * n := by
    intro n; ring
  refine ⟨⟨fun w => (256 + pr) * w.length
        + 32 * (encCompile (unL w) (unR w)).length + (128 + cr),
      256 + pr, 32, 128 + cr, ?_, fun w => le_refl _⟩, hWID, ?_, hNV4, hNV5, hNV6, pgsh⟩
  · intro w
    show Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun w)
      (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
      ((256 + pr) * w.length + 32 * (encCompile (unL w) (unR w)).length
        + (128 + cr)))
    by_cases hlen : 3 ≤ (unpack (unL w)).length
    · rcases hup : unpack (unL w) with _ | ⟨anc, t1⟩
      · simp [hup] at hlen
      · rcases t1 with _ | ⟨out, t2⟩
        · simp [hup] at hlen
        · rcases t2 with _ | ⟨ng, rest⟩
          · simp [hup] at hlen
          · by_cases hok : ((pg ng rest).1).length = ng
            · exact bumpTime (by have hx := hsplit w.length; omega)
                (key w anc out ng rest hup hok)
            · exact bumpTime (by have hx := hsplit w.length; omega)
                (keyT w anc out ng rest hup hok)
    · exact bumpTime (by have hx := hsplit w.length; omega) (hREJ w hlen)
  · intro w
    refine ⟨?_, ?_⟩
    · have hx := hsplit w.length
      omega
    · have hx := hsplit w.length
      omega

end BQPReferenceValidation.Source44

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate44
    let target ← getConstInfo ``ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate44
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run; axioms {axioms}"
