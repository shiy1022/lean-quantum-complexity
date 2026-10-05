import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts

namespace BQPReferenceValidation.Source45
/-
FIN8-Bmirc.  THE *MIRRORED* GATE LOOP RUN WITH ITS FIFTH ARM: THE SAME INDUCTION OVER THE
GATE-RECORD LIST, WITH EVERY EMITTER INSTANTIATED AT THE MIRRORED OPCODE SYMBOLS, SO THAT
EACH RECORD CONTRIBUTES THE *REVERSE* OF ITS RENDERED BLOCK -- NOW TOTAL OVER THE TAG.

WHY A SECOND STATEMENT EXISTS AT ALL.  Every emitter PREPENDS to the opcode port, and the
port's list order is reversed once, globally, at the end of the run.  So a loop that runs
forward over the record stream and prepends `Y(r)` per record contributes
`Y(rₙ) ++ … ++ Y(r₁)` to the port, i.e. `reverse(Y(r₁) ++ … ++ Y(rₙ))` to the WORD.  For the
word to carry `blk r₁ ++ … ++ blk rₙ` -- the compiled program's FORWARD block slot -- the
loop must contribute `blk(rₙ).reverse ++ … ++ blk(r₁).reverse`.  That is this theorem's
conclusion, and it is why this loop is called mirrored.

WHY IT CANNOT BE OBTAINED BY INSTANTIATING THE PREDECESSOR AT `blk := blk.reverse`.  The
four-arm dispatch pairs each ARM with a block SHAPE.  Reversal exchanges the two CNOT
shapes: the reverse of the `i < j` block has the shape the `j < i` block has, and vice
versa.  The predecessor's `i < j` arm therefore proves a conclusion of the wrong shape, and
no instantiation of its block hypotheses repairs that -- the arms and the shapes must be
re-paired, which is a restatement, not an instantiation.

THE THREE SYMBOL SWAPS, ALL OF THEM, AND ALL DISCHARGED BY THE SAME ∀-QUANTIFIED BLOCKS.
The renderer hypotheses below (`hblk1`, `hblkA`, `hblkB`, `hblkD`) are UNCHANGED -- they are
facts about the real renderer, in which `osym` is the one-nibble and `zsym` the zero-nibble.
What changes is where those two symbols appear in the EMITTERS:
* (1) the one-index emitter is instantiated with the two nibbles EXCHANGED, so it emits
  `zsym^i ++ op^(r+1) ++ osym^i`, which is `(blk [t, i]).reverse`;
* (2) the orientation seam is re-routed -- `lXA` now loads the bit the `lXB` seam used to
  load and `lXB` the bit `lXA` used to load -- because `(i<j)-block.reverse` has the
  ORIENTATION-B emitted shape and `(j<i)-block.reverse` the ORIENTATION-A one;
* (3) the two nibbles are exchanged IN THE CNOT EMITTER TOO, in both orientations, and the
  two CNOT tags are exchanged with them.  This third swap is easy to miss and is not
  optional: `blk(i<j).reverse = 0^i ++ 0^d ++ [7] ++ 1^d ++ [6] ++ 1^i`, so the index loops
  must push the ONE nibble and the scratch drains must push the ZERO nibble -- exactly the
  opposite of the unmirrored loop -- and both orientations agree on that assignment.
Nothing here re-proves an emitter.  The one-index emitter, the CNOT emitter and the min/max
splitter are ∀-quantified in their symbols and are used at the mirrored instantiation.

FIVE ARMS, NOT FOUR -- AND THIS REVERSES THE PREDECESSOR'S OWN PREAMBLE, WHICH IS NOW
OBSOLETE AND MUST NOT BE READ AS A STANDING CLAIM.  The predecessor `FIN8-Bmirb` said in
this place that a `4 ≤ t` arm "is not added and must not be", that the dispatch "sends every
tag other than four to the one-index emitter, which renders a NON-empty block", and that
such a record "is not rendered correctly by this machine under any reading".  EVERY WORD OF
THAT WAS TRUE OF THE MACHINE IT WAS WRITTEN AGAINST AND IS FALSE OF THE REPAIRED ONE.  At
the old machine the tag dispatch was the TWO-WAY test `if tag = 4 then A else ONE-INDEX`, so
a tag of five rendered `1^i ++ [oc] ++ 0^i`, length `2i + 1`, where the renderer demands the
EMPTY block -- the mismatch recorded as mode (ii) of the fourth `hBAD` falsehood.  The
repaired machine makes the dispatch THREE-WAY and TOTAL -- `if tag = 4 then A else if
5 ≤ tag then SKIP else ONE-INDEX` -- and proves the totality outright rather than arguing it.
The skip arm CONSUMES the record's index field off the token port and PUSHES NOTHING on the
opcode port, which is exactly what the renderer's `4 ≤ t → blk [t, i] = []` demands.  So the
fifth arm exists, and the well-formedness predicate of this statement weakens from `t < 4`
to `¬ t = 4` accordingly.

WHAT DID *NOT* WEAKEN, AND WHY WEAKENING IT WOULD MAKE THIS THEOREM VACUOUS.  Only `henc1`
weakens.  `hblk1` -- the one-index RENDERER equation -- stays at `t < 4` and cannot be
weakened: at `t ≥ 5` its right-hand side has length `2i + rp t + 1 ≥ 1` while `hblkS` below
demands the empty list, so the two together would be CONTRADICTORY and every consumer would
be unable to supply them.  `hreg`, the register law that loads the opcode and the repeat
count from the tag, stays at `t < 4` for the same reason and because the skip arm reads
neither.  The skip class is covered instead by the SEPARATE renderer equation `hblkS`, at
`5 ≤ t`, which is where the empty block actually lives.

THE ONE PLACE THE TAG READER HAD TO GROW, STATED HONESTLY.  The tag accumulator is a capped
`Fin 8` that SATURATES at seven, so the reader's counter clause is `t < 8 → tc u = t` and
says nothing at all above the cap.  The four-arm dispatch never noticed, because it asked
only about `t < 4` and `t = 4`; the fifth arm does notice, because a record with tag
`t ≥ 8` must still reach the skip label.  So `hTAG` below carries ONE new conjunct,
`8 ≤ t → 5 ≤ tc u`: the WEAKEST fact that routes the saturated tags, chosen over the exact
`tc u = 7` so that it survives any cap at five or above.  It is true of the repaired
machine -- the accumulator saturates at seven and seven is at least five -- and it is the
only hypothesis in this file that is not already discharged by an accepted theorem.

THE DIAGONAL GUARD STILL FIRES BEFORE THE EMITTER.  At equal wire indices the renderer
demands the EMPTY block, whose reverse is also empty; the splitter hands the emitter a
degenerate pair on which it would render something non-empty.  So the guard sits between the
splitter's `i ≤ j` exit and the emitter, and on the diagonal it discards the pair and returns
to the loop head having pushed nothing.  Mirroring does not move it, and this arm is the only
one in which the opcode port is provably untouched.

THE COST.  Unchanged: the arms' step counts are symbol-independent, and the one-step load
seam at `lXA`/`lXB` -- a step no block's own cost carries -- is still counted once per
two-index record.  The composed bound is `9 * |token stream| + 26 * |records| + 2`, AFFINE in
both natural input measures, and conjunct (2) widens it only by the length of the truncated
tag field.

WHAT IS PROVED.  (1) the loop end to end on a well-formed record stream -- WELL-FORMED NOW
MEANING `¬ t = 4` RATHER THAN `t < 4` -- with the opcode port carrying each record's block
REVERSED, in reverse record order, and a FRAME clause; (2) the reject path -- a truncated
final tag field does not hang the loop -- WITH ITS OWN FRAME CLAUSE, which the unmirrored
statement omitted; (3) the bound is never the constant zero; (4) non-vacuity of the bound on
a concrete profile; (5) AN UNRELATED REPAIR CARRIED HERE BECAUSE IT IS FREE: accepted
`FLAT-1b`'s round-trip conjunct is stated at `t < 4` although its own proof uses that
hypothesis in exactly ONE place, to feed a parser equation whose guard is `¬ t = 4`.  So the
round trip holds verbatim at `¬ t = 4` -- which is the record class this whole repair is
about, and at which `FLAT-1b`'s form is unusable.  Conjunct (5) is that corrected statement,
universally quantified in the parser so no consumer is tied to a particular one.

THE COST OF THE FIFTH ARM IS BELOW THE EXISTING BUDGET, SO THE COEFFICIENTS DO NOT MOVE.  A
skip record costs `t + 2` for the tag read and `i + 1` for the field skip, `t + i + 3` in
all, against the `9 * (t + i + 2) + 26` the affine bound already allots it.  The bound is
therefore `9 * |token stream| + 26 * |records| + 2` UNCHANGED, character for character, so
a consumer citing the predecessor's bound needs no edit.

NOT CLAIMED: nothing about how the stream was parsed, nothing about the back end, no
identification of the emitted word with any bit string, no halt, no polynomial bound and no
concrete machine.  In particular NOT the ADJOINT sweep: that loop's conclusion is the
UNMIRRORED `(recs.reverse.map blkA).flatten`, not this one's per-record reversal, and the
predecessor's own argument for why the mirrored statement is not an instantiation of the
unmirrored one applies in this direction too -- reversal exchanges the two CNOT shapes, so
the arms and the shapes would have to be re-paired.  The adjoint fifth arm is the same edit
applied to the unmirrored loop and belongs in its own file; every hypothesis it needs is
already generic here (`SKIPRUN` is generic in port, both labels, the pop function, the guard
AND the encoder, so it instantiates at `kxin`/`lSKTz`/`lGTz` with no new run theorem).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Turing.TM2

/-! ### 1.  Run composition and three list identities -/

/-- Chain two runs of known length. -/
private lemma chainN {A : Type} {f : A → A} {a b c : A} {m n t : ℕ} (ht : t = m + n)
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[t] a = c := by
  subst ht
  rw [Nat.add_comm m n, Function.iterate_add_apply f n m a, h1]
  exact h2

/-- The token stream of a non-empty record list. -/
private lemma encCons {A B : Type} (f : A → List B) (a : A) (l : List A) :
    ((a :: l).map f).flatten = f a ++ (l.map f).flatten := rfl

/-- Flattening past a final block. -/
private lemma flatSnoc {A : Type} (l : List (List A)) (a : List A) :
    (l ++ [a]).flatten = l.flatten ++ a := by
  induction l with
  | nil => simp
  | cons b t ih =>
      show b ++ (t ++ [a]).flatten = (b ++ t.flatten) ++ a
      rw [ih, List.append_assoc]

/-- The opcode word of a non-empty record list, in the order the loop PREPENDS blocks. -/
private lemma revCons {A B : Type} (f : A → List B) (a : A) (l : List A) :
    ((a :: l).reverse.map f).flatten = (l.reverse.map f).flatten ++ f a := by
  rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
  exact flatSnoc _ _

/-! ### 2.  The statement -/

theorem _root_.BQPReferenceValidation.candidate45
    {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ)
    {ktok kidx kscA kscB kopc : K}
    -- the ten pairwise stack disequalities; the host machine's single `Nodup` on its
    -- fourteen-stack list supplies every one, and all twenty directed forms are derived once
    -- at the top of the proof so no direction is ever chosen again
    (nab : ktok ≠ kidx) (nac : ktok ≠ kscA) (nad : ktok ≠ kscB) (nae : ktok ≠ kopc)
    (nbc : kidx ≠ kscA) (nbd : kidx ≠ kscB) (nbe : kidx ≠ kopc)
    (ncd : kscA ≠ kscB) (nce : kscA ≠ kopc)
    (nde : kscB ≠ kopc)
    (lGT lG lN1 lA lSKT lXA lXB lP1 lQ1 : Λ)
    (dsp : σ → Λ) (sdf sdt : σ → σ) (dir : σ → Bool) (tc cnt : σ → ℕ) (op : σ → Γ kopc)
    (eo : Bool → Γ ktok) (ei : Bool → Γ kidx)
    (zsym osym t6 t7 : Γ kopc)
    (rp : ℕ → ℕ) (oc : ℕ → Γ kopc)
    (enc : List ℕ → List (Γ ktok)) (blk : List ℕ → List (Γ kopc))
    -- THE TOKEN ENCODING the parser above this loop produced: a gate record is its arity tag
    -- and then its wire indices, each a unary field closed by the same terminator.
    -- THE GUARD HERE IS `¬ t = 4`, NOT `t < 4`: this is the ENCODER, a fact about how the
    -- tokeniser wrote a two-field record, and the flat gate parser's own two-field equation
    -- is guarded by `¬ t = 4` too, so this is exactly the class the parser hands over.
    (henc1 : ∀ t i : ℕ, ¬ t = 4 → enc [t, i] = List.replicate t (eo true)
        ++ (eo false :: (List.replicate i (eo true) ++ [eo false])))
    (henc2 : ∀ i j : ℕ, enc [4, i, j] = List.replicate 4 (eo true)
        ++ (eo false :: (List.replicate i (eo true)
          ++ (eo false :: (List.replicate j (eo true) ++ [eo false])))))
    -- THE RENDERER the emitters realise, IN ITS UNMIRRORED FORM -- these four equations are
    -- the real renderer's and are NOT touched by mirroring.  `osym` is the one-nibble and
    -- `zsym` the zero-nibble throughout.  The fourth is the one that forces the guard: at
    -- EQUAL wire indices the block is EMPTY, and so is its reverse.
    (hblk1 : ∀ t i : ℕ, t < 4 → blk [t, i] = List.replicate i osym
        ++ (List.replicate (rp t + 1) (oc t) ++ List.replicate i zsym))
    (hblkA : ∀ i d : ℕ, blk [4, i, i + d + 1] = List.replicate i osym
        ++ (t6 :: (List.replicate (d + 1) osym
          ++ (t7 :: (List.replicate (d + 1) zsym ++ List.replicate i zsym)))))
    (hblkB : ∀ j d : ℕ, blk [4, j + d + 1, j] = List.replicate j osym
        ++ (List.replicate (d + 1) osym
          ++ (t6 :: (List.replicate (d + 1) zsym ++ (t7 :: List.replicate j zsym)))))
    (hblkD : ∀ i : ℕ, blk [4, i, i] = [])
    -- THE FIFTH ARM'S RENDERER EQUATION, and the reason the fifth arm can exist at all: a
    -- one-index record whose tag is FIVE OR MORE renders the EMPTY block.  This is a
    -- SEPARATE equation and not a weakening of `hblk1`, which would contradict it.  Stated
    -- at `5 ≤ t`, the weakest form the loop uses, so the renderer's `4 ≤ t` clause
    -- discharges it directly.
    (hblkS : ∀ t i : ℕ, 5 ≤ t → blk [t, i] = [])
    -- THE REPEAT COUNTER IS BOUNDED.  The largest one-index block is the adjoint of the
    -- eighth-turn gate, seven copies of its opcode, so the count never exceeds six.
    (hrp : ∀ t : ℕ, rp t ≤ 6)
    -- (I) THE TAG READER, accepted: from the loop head to the register-computed dispatch
    -- label in exactly `t + 2` steps with the tag value in the counter.  THE COUNTER READING
    -- IS CONDITIONAL ON `t < 8` and nothing else is: the machine's tag accumulator is a
    -- capped `Fin 8` whose successor SATURATES.  The tag reader is symbol-blind, so
    -- mirroring leaves it verbatim.
    (hTAG : ∀ (t : ℕ) (rest : List (Γ ktok)) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate t (eo true) ++ (eo false :: rest) →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[t + 2]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some (dsp u), u, T⟩ : Cfg Γ Λ σ)
        ∧ (t < 8 → tc u = t)
        -- THE ONE NEW CONJUNCT, AND THE ONLY ADDITION TO AN OTHERWISE VERBATIM HYPOTHESIS.
        -- ABOVE THE CAP the counter is not read exactly -- the machine does not compute it
        -- either -- but it is still at least five, because the accumulator SATURATES rather
        -- than wrapping.  That is all the fifth arm needs, and it is deliberately weaker
        -- than `tc u = 7` so that it survives any cap at five or above.
        ∧ (8 ≤ t → 5 ≤ tc u) ∧ T ktok = rest ∧ (∀ k, k ≠ ktok → T k = S k))
    -- (II) THE LOOP EXIT, accepted: an exhausted token port leaves for the back end.
    (hEXIT : ∀ (v : σ) (S : ∀ k, List (Γ k)), S ktok = [] →
        ∃ u : σ,
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[2]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lG, u, S⟩ : Cfg Γ Λ σ))
    -- (III) THE TAG READER'S REJECT ARM, accepted: a tag field with no terminator leaves for
    -- the back end instead of hanging.
    (hTRUNC : ∀ (t : ℕ) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate t (eo true) →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[t + 2]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lG, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = [] ∧ (∀ k, k ≠ ktok → T k = S k))
    -- (IV)-(V) THE TWO LOAD SEAMS, MIRRORED -- THE SECOND OF THE THREE SWAPS.  One step
    -- each, no stack touched, and the bits are the OTHER WAY ROUND from the unmirrored
    -- loop: the splitter's `i ≤ j` exit `lXA` now loads the bit that selects the
    -- orientation-B emitted shape, because that is the shape of `(i<j)-block.reverse`.
    (hXAs : ∀ (v : σ) (S : ∀ k, List (Γ k)),
        (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[1]
            (Option.some (⟨Option.some lXA, v, S⟩ : Cfg Γ Λ σ))
          = Option.some (⟨Option.some lP1, sdt v, S⟩ : Cfg Γ Λ σ)
      ∧ dir (sdt v) = true)
    (hXBs : ∀ (v : σ) (S : ∀ k, List (Γ k)),
        (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[1]
            (Option.some (⟨Option.some lXB, v, S⟩ : Cfg Γ Λ σ))
          = Option.some (⟨Option.some lQ1, sdf v, S⟩ : Cfg Γ Λ σ)
      ∧ dir (sdf v) = false)
    -- (VI) THE DIAGONAL GUARD, OFF THE DIAGONAL, accepted: the splitter's output is restored
    -- symbol for symbol, the orientation bit survives, and control reaches the emitter.  The
    -- guard touches no opcode nibble, so mirroring leaves it verbatim.
    (hGND : ∀ (i d : ℕ) (rest : List (Γ kidx)) (v : σ) (S : ∀ k, List (Γ k)),
        S kidx = List.replicate i (ei true)
            ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: rest))) →
        S kscA = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[2 * i + 4]
              (Option.some (⟨Option.some lP1, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lQ1, u, T⟩ : Cfg Γ Λ σ)
        ∧ T kidx = S kidx ∧ T kscA = [] ∧ dir u = dir v
        ∧ (∀ k, k ≠ kidx → k ≠ kscA → T k = S k))
    -- (VII) THE DIAGONAL GUARD ON THE DIAGONAL, accepted: control returns to the LOOP HEAD
    -- with the index port emptied and the opcode port untouched -- the empty block, which is
    -- its own reverse.
    (hGDG : ∀ (i : ℕ) (rest : List (Γ kidx)) (v : σ) (S : ∀ k, List (Γ k)),
        S kidx = List.replicate i (ei true) ++ (ei false :: (ei false :: rest)) →
        S kscA = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[3 * i + rest.length + 7]
              (Option.some (⟨Option.some lP1, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
        ∧ T kidx = [] ∧ T kscA = [] ∧ T kopc = S kopc
        ∧ (∀ k, k ≠ kidx → k ≠ kscA → T k = S k))
    -- (VIII) THE REGISTER DISPATCH: it reads the tag counter, which is what makes the loop a
    -- dispatcher rather than a single-arm loop.
    (hdN : ∀ v : σ, tc v < 4 → dsp v = lN1)
    (hdA : ∀ v : σ, tc v = 4 → dsp v = lA)
    -- THE THIRD DISPATCH ARM.  With this the dispatch is TOTAL in the tag and no consumer
    -- needs a tag side condition; the host machine proves it, and proves the totality
    -- `dsp v = lN1 ∨ dsp v = lA ∨ dsp v = lSKT` besides, which this loop does not need
    -- because the three readings `tc v < 4`, `tc v = 4` and `5 ≤ tc v` already exhaust ℕ.
    (hdS : ∀ v : σ, 5 ≤ tc v → dsp v = lSKT)
    -- (IX) THE OPCODE AND REPEAT COUNT ARE LOADED BY THE TAG.  The register law that makes
    -- ONE emitter serve all eight (gate, direction) cases; the mirrored loop instantiates
    -- `rp` at the forward repeat table, which is identically zero, but nothing here needs
    -- that and the hypothesis is left ∀-quantified in `rp`.
    (hreg : ∀ (v : σ) (t : ℕ), tc v = t → t < 4 → cnt v = rp t + 1 ∧ op v = oc t)
    -- (X) THE ONE-INDEX EMITTER AT THE MIRRORED SYMBOLS -- THE FIRST OF THE THREE SWAPS.
    -- Verbatim the accepted block with its two nibble parameters EXCHANGED: the index loop
    -- pushes `zsym` and the scratch drain pushes `osym`, so the emitted list is the REVERSE
    -- of the one-index rendered block.  `2i + r + 3` steps, unchanged.
    (hE1 : ∀ (i r : ℕ) (rest : List (Γ ktok)) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate i (eo true) ++ (eo false :: rest) → S kscA = [] →
        cnt v = r + 1 →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[2 * i + r + 3]
              (Option.some (⟨Option.some lN1, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = rest ∧ T kscA = []
        ∧ T kopc = List.replicate i zsym
            ++ (List.replicate (r + 1) (op v) ++ (List.replicate i osym ++ S kopc))
        ∧ (∀ k, k ≠ ktok → k ≠ kscA → k ≠ kopc → T k = S k))
    -- (X-bis) THE FIELD SKIP, accepted, AND THE WHOLE OF THE FIFTH ARM'S RUN.  The index
    -- field is popped off the token port under the bit guard until its TERMINATOR, the
    -- residue -- every following record -- is left in place, and NOTHING is pushed
    -- anywhere: the frame is over EVERY port but the token port, so the opcode port is
    -- carried unchanged and the empty block is emitted by emitting nothing.  `i + 1` steps,
    -- the `+1` being the terminator, which is not free.  This is NOT the drain primitive:
    -- that one pops to EXHAUSTION and would eat the rest of the stream.
    (hSKP : ∀ (i : ℕ) (rest : List (Γ ktok)) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate i (eo true) ++ eo false :: rest →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[i + 1]
              (Option.some (⟨Option.some lSKT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = rest ∧ (∀ k, k ≠ ktok → T k = S k))
    -- (XI) THE MIN/MAX SPLITTER, ORIENTATION A, accepted: `i ≤ j` written `j = i + d`.  It
    -- emits unary INDEX marks, not opcode nibbles, so mirroring does not touch it at all --
    -- only which orientation bit its exit label loads, and that is (IV) above.
    (hMMA : ∀ (i d : ℕ) (rest : List (Γ ktok)) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate i (eo true)
            ++ (eo false :: (List.replicate (i + d) (eo true) ++ (eo false :: rest))) →
        S kscA = [] → S kscB = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[5 * i + 2 * d + 8]
              (Option.some (⟨Option.some lA, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lXA, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = rest ∧ T kscA = [] ∧ T kscB = []
        ∧ T kidx = List.replicate i (ei true)
            ++ (ei false :: (List.replicate d (ei true) ++ (ei false :: S kidx)))
        ∧ (∀ k, k ≠ ktok → k ≠ kscA → k ≠ kscB → k ≠ kidx → T k = S k))
    -- (XII) THE MIN/MAX SPLITTER, ORIENTATION B, accepted: `j < i` written `i = j + d + 1`,
    -- three steps dearer -- the give-back -- and a DIFFERENT exit label, which IS the flag.
    (hMMB : ∀ (j d : ℕ) (rest : List (Γ ktok)) (v : σ) (S : ∀ k, List (Γ k)),
        S ktok = List.replicate (j + d + 1) (eo true)
            ++ (eo false :: (List.replicate j (eo true) ++ (eo false :: rest))) →
        S kscA = [] → S kscB = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[5 * j + 2 * d + 11]
              (Option.some (⟨Option.some lA, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lXB, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = rest ∧ T kscA = [] ∧ T kscB = []
        ∧ T kidx = List.replicate j (ei true)
            ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: S kidx)))
        ∧ (∀ k, k ≠ ktok → k ≠ kscA → k ≠ kscB → k ≠ kidx → T k = S k))
    -- (XIII) THE CNOT EMITTER AT THE MIRRORED SYMBOLS, BIT CLEAR -- THE THIRD SWAP, HALF ONE.
    -- The accepted block's orientation-A conjunct with BOTH nibble parameters exchanged AND
    -- the two CNOT tags exchanged with them.  Emitted shape: `zsym^i, t7, zsym^d, t6,
    -- osym^d, osym^i`, which is `(blk [4, i+d+1, i]).reverse` at `d` one larger.  The
    -- `j < i` arm reaches it straight from the `lXB` seam, the guard not entered.
    (hE2F : ∀ (i d : ℕ) (rest : List (Γ kidx)) (v : σ) (S : ∀ k, List (Γ k)),
        dir v = false →
        S kidx = List.replicate i (ei true)
            ++ (ei false :: (List.replicate d (ei true) ++ (ei false :: rest))) →
        S kscA = [] → S kscB = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[2 * i + 2 * d + 6]
              (Option.some (⟨Option.some lQ1, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
        ∧ T kidx = rest ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = List.replicate i zsym ++ (t7 :: (List.replicate d zsym
            ++ (t6 :: (List.replicate d osym ++ (List.replicate i osym ++ S kopc)))))
        ∧ (∀ k, k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k))
    -- (XIV) THE CNOT EMITTER AT THE MIRRORED SYMBOLS, BIT SET -- THE THIRD SWAP, HALF TWO.
    -- The same seven labels and the same count; emitted shape `zsym^j, zsym^(d+1), t7,
    -- osym^(d+1), t6, osym^j`, which is `(blk [4, j, j+d+1]).reverse`.  The `i < j` arm
    -- reaches it through the `lXA` seam and the guard.
    (hE2T : ∀ (j d : ℕ) (rest : List (Γ kidx)) (v : σ) (S : ∀ k, List (Γ k)),
        dir v = true →
        S kidx = List.replicate j (ei true)
            ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: rest))) →
        S kscA = [] → S kscB = [] →
        ∃ (u : σ) (T : ∀ k, List (Γ k)),
          (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[2 * j + 2 * (d + 1) + 6]
              (Option.some (⟨Option.some lQ1, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
        ∧ T kidx = rest ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = List.replicate j zsym ++ (List.replicate (d + 1) zsym
            ++ (t7 :: (List.replicate (d + 1) osym
              ++ (t6 :: (List.replicate j osym ++ S kopc)))))
        ∧ (∀ k, k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k)) :
    -- (1) THE MIRRORED GATE LOOP END TO END.  On a token stream that is the concatenation of
    -- the encodings of a list of WELL-FORMED gate records -- each either a one-index record
    -- with a tag below four or a two-index record with the tag four -- the loop runs from its
    -- head to the back end's entry label within `9 * |token stream| + 26 * |records| + 2`
    -- steps, AFFINE in both input measures, leaving the opcode port carrying each record's
    -- rendered block REVERSED, in reverse record order -- which on a port whose list order is
    -- reversed once at the end of the run is the FORWARD block slot in the forward order --
    -- and the token, index and both scratch ports empty.  The diagonal records contribute
    -- NOTHING, which is the renderer's demand and the guard's whole purpose.
    (∀ (recs : List (List ℕ)) (v : σ) (S : ∀ k, List (Γ k)),
        (∀ r ∈ recs, (∃ t i : ℕ, ¬ t = 4 ∧ r = [t, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
        S ktok = (recs.map enc).flatten →
        S kidx = [] → S kscA = [] → S kscB = [] →
        ∃ (N : ℕ) (u : σ) (T : ∀ k, List (Γ k)),
          N ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length + 2
        ∧ (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[N]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lG, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = [] ∧ T kidx = [] ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = ((recs.reverse.map (fun r => (blk r).reverse)).flatten ++ S kopc)
        ∧ (∀ k, k ≠ ktok → k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k))
    -- (2) THE REJECT PATH, required and not optional.  The token stream ends in a TRUNCATED
    -- tag field: unary marks with no terminator, the bit-level failure no parser clause
    -- covers.  The loop does NOT hang and does NOT dispatch on the truncated tag: it renders
    -- the complete records exactly as in (1) and then leaves for the back end, within the
    -- same affine bound widened by the truncation, with every working port empty -- AND WITH
    -- THE FRAME CLAUSE, which the unmirrored statement of this conjunct omits.
  ∧ (∀ (recs : List (List ℕ)) (t : ℕ) (v : σ) (S : ∀ k, List (Γ k)),
        (∀ r ∈ recs, (∃ a i : ℕ, ¬ a = 4 ∧ r = [a, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
        S ktok = (recs.map enc).flatten ++ List.replicate t (eo true) →
        S kidx = [] → S kscA = [] → S kscB = [] →
        ∃ (N : ℕ) (u : σ) (T : ∀ k, List (Γ k)),
          N ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length + t + 2
        ∧ (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[N]
              (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
            = Option.some (⟨Option.some lG, u, T⟩ : Cfg Γ Λ σ)
        ∧ T ktok = [] ∧ T kidx = [] ∧ T kscA = [] ∧ T kscB = []
        ∧ T kopc = ((recs.reverse.map (fun r => (blk r).reverse)).flatten ++ S kopc)
        ∧ (∀ k, k ≠ ktok → k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k))
    -- (3) THE BOUND IS AFFINE AND NEVER THE CONSTANT ZERO: it is at least two on every
    -- input, which is the cost of observing an exhausted token port.
  ∧ (∀ L R : ℕ, 2 ≤ 9 * L + 26 * R + 2)
    -- (4) NON-VACUITY OF THE BOUND on a concrete non-degenerate profile: three records and a
    -- twenty-four-symbol token stream fit in two hundred and ninety-six steps, and the bound
    -- really does grow with both measures, so conjunct (1) is not an empty-input statement.
  ∧ (∃ L R : ℕ, ¬ L = 0 ∧ ¬ R = 0 ∧ 9 * L + 26 * R + 2 = 296
      ∧ ¬ (9 * L + 26 * R + 2 = 9 * (L + 1) + 26 * R + 2)
      ∧ ¬ (9 * L + 26 * R + 2 = 9 * L + 26 * (R + 1) + 2))
    -- (5) THE PARSER ROUND TRIP AT THE WEAKENED PREDICATE -- A REPAIR OF AN ACCEPTED
    -- CONJUNCT, CARRIED HERE BECAUSE IT IS FREE AND BECAUSE THE ACCEPTED FORM IS UNUSABLE
    -- FOR EXACTLY THE RECORD CLASS THIS FILE IS ABOUT.  Accepted `FLAT-1b`'s conjunct (5)
    -- states this at `t < 4`.  Its own private proof uses that hypothesis in exactly ONE
    -- place -- to feed the two-field parser equation, whose guard is `¬ t = 4` -- so the
    -- SAME proof gives the SAME conclusion at `¬ t = 4`, with the hypothesis passed
    -- straight through instead of weakened by `omega`.  Everything is quantified here,
    -- INCLUDING the parser, so this conjunct is independent of the loop above it and of
    -- any particular parser: a consumer supplies the three defining equations it already
    -- has and reads off the round trip.  The three equations are `PARSE-TOT`'s, verbatim.
  ∧ (∀ pg : ℕ → List ℕ → List (List ℕ) × List ℕ,
        (∀ ts : List ℕ, pg 0 ts = ([], ts)) →
        (∀ (t i k : ℕ) (rest : List ℕ), ¬ t = 4 →
          pg (k + 1) (t :: i :: rest) = ([t, i] :: (pg k rest).1, (pg k rest).2)) →
        (∀ (i j k : ℕ) (rest : List ℕ),
          pg (k + 1) (4 :: i :: j :: rest)
            = ([4, i, j] :: (pg k rest).1, (pg k rest).2)) →
      ∀ (recs : List (List ℕ)) (r : List ℕ),
        (∀ rec ∈ recs, (∃ t i : ℕ, ¬ t = 4 ∧ rec = [t, i])
            ∨ (∃ i j : ℕ, rec = [4, i, j])) →
        pg recs.length (recs.flatten ++ r) = (recs, r)) := by
  have nba := nab.symm
  have nca := nac.symm
  have nda := nad.symm
  have nea := nae.symm
  have ncb := nbc.symm
  have ndb := nbd.symm
  have neb := nbe.symm
  have ndc := ncd.symm
  have nec := nce.symm
  have ned := nde.symm
  -- THE FOUR REVERSED BLOCKS, read off the four unmirrored renderer equations once.  These
  -- are the shapes the mirrored emitters above actually produce, and the exchange of the two
  -- CNOT shapes under reversal is visible here: `hrA`'s right-hand side has the emitted
  -- shape of (XIV) and `hrB`'s that of (XIII).
  have hr1 : ∀ t i : ℕ, t < 4 → (blk [t, i]).reverse = List.replicate i zsym
      ++ (List.replicate (rp t + 1) (oc t) ++ List.replicate i osym) := by
    intro t i ht
    rw [hblk1 t i ht]
    simp [List.reverse_append, List.reverse_replicate, List.append_assoc]
  have hrA : ∀ i d : ℕ, (blk [4, i, i + d + 1]).reverse = List.replicate i zsym
      ++ (List.replicate (d + 1) zsym
        ++ (t7 :: (List.replicate (d + 1) osym ++ (t6 :: List.replicate i osym)))) := by
    intro i d
    rw [hblkA i d]
    -- `simp only`, not `simp`: the reversed `i < j` block is the ONE shape whose two
    -- leading runs carry the SAME nibble, and the default set merges them into a single
    -- `replicate (d + 1 + i)` that no emitter produces
    simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  have hrB : ∀ j d : ℕ, (blk [4, j + d + 1, j]).reverse = List.replicate j zsym
      ++ (t7 :: (List.replicate (d + 1) zsym
        ++ (t6 :: (List.replicate (d + 1) osym ++ List.replicate j osym)))) := by
    intro j d
    rw [hblkB j d]
    simp [List.reverse_append, List.reverse_replicate, List.append_assoc]
  have hrD : ∀ i : ℕ, (blk [4, i, i]).reverse = [] := by
    intro i
    rw [hblkD i]
    rfl
  -- THE FIFTH ARM'S REVERSED BLOCK.  The empty list is its own reverse, so mirroring has
  -- nothing to do here -- which is precisely why one skip arm serves both sweeps.
  have hrS : ∀ t i : ℕ, 5 ≤ t → (blk [t, i]).reverse = [] := by
    intro t i ht
    rw [hblkS t i ht]
    rfl
  -- the cons law for the reversed-block word, stated with the application already reduced so
  -- that a rewrite by it exposes `blk q` literally
  have hrvC : ∀ (q : List ℕ) (l : List (List ℕ)),
      ((q :: l).reverse.map (fun x => (blk x).reverse)).flatten
        = (l.reverse.map (fun x => (blk x).reverse)).flatten ++ (blk q).reverse :=
    fun q l => revCons (fun x => (blk x).reverse) q l
  -- THE INDUCTION.  One pass of the loop per record, leaving the token port at the given
  -- tail and control back at the loop head, within `9 * |stream| + 26 * |records|` steps.
  have hLoop : ∀ (recs : List (List ℕ)) (tail : List (Γ ktok)) (v : σ)
      (S : ∀ k, List (Γ k)),
      (∀ r ∈ recs, (∃ t i : ℕ, ¬ t = 4 ∧ r = [t, i]) ∨ (∃ i j : ℕ, r = [4, i, j])) →
      S ktok = (recs.map enc).flatten ++ tail →
      S kidx = [] → S kscA = [] → S kscB = [] →
      ∃ (N : ℕ) (u : σ) (T : ∀ k, List (Γ k)),
        N ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length
      ∧ (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[N]
            (Option.some (⟨Option.some lGT, v, S⟩ : Cfg Γ Λ σ))
          = Option.some (⟨Option.some lGT, u, T⟩ : Cfg Γ Λ σ)
      ∧ T ktok = tail ∧ T kidx = [] ∧ T kscA = [] ∧ T kscB = []
      ∧ T kopc = ((recs.reverse.map (fun r => (blk r).reverse)).flatten ++ S kopc)
      ∧ (∀ k, k ≠ ktok → k ≠ kidx → k ≠ kscA → k ≠ kscB → k ≠ kopc → T k = S k) := by
    intro recs
    induction recs with
    | nil =>
        intro tail v S _ hS hI hA hB
        exact ⟨0, v, S, Nat.zero_le _, rfl, hS, hI, hA, hB, rfl,
          fun k _ _ _ _ _ => rfl⟩
    | cons r rs ih =>
        intro tail v S hwf hS hI hA hB
        have hrs : ∀ q ∈ rs, (∃ t i : ℕ, ¬ t = 4 ∧ q = [t, i]) ∨ (∃ i j : ℕ, q = [4, i, j]) :=
          fun q hq => hwf q (List.mem_cons_of_mem r hq)
        have hlenc : (((r :: rs).map enc).flatten).length
            = (enc r).length + (((rs.map enc)).flatten).length := by
          rw [encCons, List.length_append]
        have hlenr : (r :: rs).length = rs.length + 1 := List.length_cons
        have hX : S ktok = enc r ++ ((rs.map enc).flatten ++ tail) := by
          rw [hS, encCons, List.append_assoc]
        rcases hwf r (by simp) with ⟨t, i, ht4, hr⟩ | ⟨i, j, hr⟩
        · -- ONE-INDEX RECORD.  The tag is only known to be OTHER THAN FOUR, so this case
          -- now SPLITS: below four it is the mirrored one-index emitter as before, at five
          -- or more it is the new skip arm.  Everything down to the tag read is shared,
          -- because the token shape and the field length do not depend on which arm runs.
          subst hr
          have hS1 : S ktok = List.replicate t (eo true)
              ++ (eo false :: (List.replicate i (eo true)
                ++ (eo false :: ((rs.map enc).flatten ++ tail)))) := by
            rw [hX, henc1 t i ht4]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          have hE : (enc [t, i]).length = t + i + 2 := by
            have hq := congrArg List.length (henc1 t i ht4)
            simp only [List.length_append, List.length_replicate, List.length_cons,
              List.length_nil] at hq
            omega
          obtain ⟨u1, T1, r1, htc1, htcS, htk1, hf1⟩ := hTAG t
            (List.replicate i (eo true) ++ (eo false :: ((rs.map enc).flatten ++ tail)))
            v S hS1
          have h1A : T1 kscA = [] := by rw [hf1 kscA nca, hA]
          have h1I : T1 kidx = [] := by rw [hf1 kidx nba, hI]
          have h1B : T1 kscB = [] := by rw [hf1 kscB nda, hB]
          have h1O : T1 kopc = S kopc := hf1 kopc nea
          rcases Nat.lt_or_ge t 4 with ht | hge
          · -- ARM ONE, TAG BELOW FOUR: the mirrored one-index emitter, swap one.  Verbatim
            -- the predecessor's arm, with the record's tag hypothesis now `ht` rather than
            -- the case split's own `ht4`.
            have htc1' : tc u1 = t := htc1 (by omega)
            have hlt : tc u1 < 4 := by rw [htc1']; exact ht
            rw [hdN u1 hlt] at r1
            have hcn : cnt u1 = rp t + 1 := (hreg u1 t htc1' ht).1
            have hop : op u1 = oc t := (hreg u1 t htc1' ht).2
            obtain ⟨u2, T2, r2, htk2, ha2, ho2, hf2⟩ := hE1 i (rp t)
              ((rs.map enc).flatten ++ tail) u1 T1 htk1 h1A hcn
            have h2I : T2 kidx = [] := by rw [hf2 kidx nba nbc nbe, h1I]
            have h2B : T2 kscB = [] := by rw [hf2 kscB nda ndc nde, h1B]
            obtain ⟨N3, u3, T3, hbd3, r3, htk3, h3I, h3A, h3B, h3O, hf3⟩ :=
              ih tail u2 T2 hrs htk2 h2I ha2 h2B
            refine ⟨(t + 2) + (2 * i + rp t + 3) + N3, u3, T3, ?_, ?_, htk3, h3I, h3A, h3B,
              ?_, ?_⟩
            · have := hrp t
              rw [hlenc, hlenr, hE]
              omega
            · exact chainN rfl (chainN rfl r1 r2) r3
            · rw [h3O, ho2, hop, h1O, hrvC, hr1 t i ht]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            · intro k hk1 hk2 hk3 hk4 hk5
              rw [hf3 k hk1 hk2 hk3 hk4 hk5, hf2 k hk1 hk3 hk5, hf1 k hk1]
          · -- ARM FIVE, THE TAG SKIP -- THE WHOLE OF THE NEW CONTENT.  `4 ≤ t` and
            -- `¬ t = 4` give `5 ≤ t`; the counter reads `t` below the cap and is at least
            -- five above it, so in BOTH ranges the dispatch is the skip label.  The arm
            -- consumes the index field and pushes nothing, so the opcode port is carried
            -- through unchanged and the record contributes the EMPTY reversed block --
            -- which is what `hblkS` says it must.
            have h5 : 5 ≤ t := by omega
            have htc5 : 5 ≤ tc u1 := by
              rcases Nat.lt_or_ge t 8 with h8 | h8
              · rw [htc1 h8]
                exact h5
              · exact htcS h8
            rw [hdS u1 htc5] at r1
            obtain ⟨u2, T2, r2, htk2, hf2⟩ := hSKP i
              ((rs.map enc).flatten ++ tail) u1 T1 htk1
            have h2I : T2 kidx = [] := by rw [hf2 kidx nba, h1I]
            have h2A : T2 kscA = [] := by rw [hf2 kscA nca, h1A]
            have h2B : T2 kscB = [] := by rw [hf2 kscB nda, h1B]
            have h2O : T2 kopc = S kopc := by rw [hf2 kopc nea, h1O]
            obtain ⟨N3, u3, T3, hbd3, r3, htk3, h3I, h3A, h3B, h3O, hf3⟩ :=
              ih tail u2 T2 hrs htk2 h2I h2A h2B
            refine ⟨(t + 2) + (i + 1) + N3, u3, T3, ?_, ?_, htk3, h3I, h3A, h3B, ?_, ?_⟩
            · rw [hlenc, hlenr, hE]
              omega
            · exact chainN rfl (chainN rfl r1 r2) r3
            · rw [h3O, h2O, hrvC, hrS t i h5]
              simp only [List.append_nil]
            · intro k hk1 hk2 hk3 hk4 hk5
              rw [hf3 k hk1 hk2 hk3 hk4 hk5, hf2 k hk1, hf1 k hk1]
        · -- TWO-INDEX RECORD
          subst hr
          have hS1 : S ktok = List.replicate 4 (eo true)
              ++ (eo false :: (List.replicate i (eo true)
                ++ (eo false :: (List.replicate j (eo true)
                  ++ (eo false :: ((rs.map enc).flatten ++ tail)))))) := by
            rw [hX, henc2 i j]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          have hE : (enc [4, i, j]).length = i + j + 7 := by
            have hq := congrArg List.length (henc2 i j)
            simp only [List.length_append, List.length_replicate, List.length_cons,
              List.length_nil] at hq
            omega
          obtain ⟨u1, T1, r1, htc1, _, htk1, hf1⟩ := hTAG 4
            (List.replicate i (eo true) ++ (eo false :: (List.replicate j (eo true)
              ++ (eo false :: ((rs.map enc).flatten ++ tail))))) v S hS1
          have htc1' : tc u1 = 4 := htc1 (by omega)
          rw [hdA u1 htc1'] at r1
          have h1A : T1 kscA = [] := by rw [hf1 kscA nca, hA]
          have h1I : T1 kidx = [] := by rw [hf1 kidx nba, hI]
          have h1B : T1 kscB = [] := by rw [hf1 kscB nda, hB]
          have h1O : T1 kopc = S kopc := hf1 kopc nea
          rcases lt_trichotomy i j with hij | hij | hij
          · -- CONTROL BELOW TARGET.  The `lXA` seam now SETS the bit (swap two), the guard
            -- confirms the indices differ and carries the bit, and the BIT-SET emitter
            -- renders `(blk [4, i, j]).reverse`.
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
            subst hd
            obtain ⟨u2, T2, r2, htk2, h2A, h2B, h2I, hf2⟩ := hMMA i (d + 1)
              ((rs.map enc).flatten ++ tail) u1 T1 htk1 h1A h1B
            have h2O : T2 kopc = S kopc := by rw [hf2 kopc nea nec ned neb, h1O]
            have h2I' : T2 kidx = List.replicate i (ei true)
                ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: []))) := by
              rw [h2I, h1I]
            obtain ⟨u3, T3, r3, h3I, h3A, h3d, hf3⟩ := hGND i d [] (sdt u2) T2 h2I' h2A
            have h3B : T3 kscB = [] := by rw [hf3 kscB ndb ndc, h2B]
            have h3O : T3 kopc = S kopc := by rw [hf3 kopc neb nec, h2O]
            have h3K : T3 ktok = (rs.map enc).flatten ++ tail := by
              rw [hf3 ktok nab nac, htk2]
            have h3dir : dir u3 = true := by rw [h3d]; exact (hXAs u2 T2).2
            have h3I' : T3 kidx = List.replicate i (ei true)
                ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: []))) := by
              rw [h3I, h2I']
            obtain ⟨u4, T4, r4, h4I, h4A, h4B, h4O, hf4⟩ :=
              hE2T i d [] u3 T3 h3dir h3I' h3A h3B
            have h4K : T4 ktok = (rs.map enc).flatten ++ tail := by
              rw [hf4 ktok nab nac nad nae, h3K]
            obtain ⟨N5, u5, T5, hbd5, r5, htk5, h5I, h5A, h5B, h5O, hf5⟩ :=
              ih tail u4 T4 hrs h4K h4I h4A h4B
            refine ⟨6 + (5 * i + 2 * (d + 1) + 8) + 1 + (2 * i + 4)
              + (2 * i + 2 * (d + 1) + 6) + N5, u5, T5, ?_, ?_, htk5, h5I, h5A, h5B, ?_, ?_⟩
            · rw [hlenc, hlenr, hE]
              omega
            · exact chainN rfl (chainN rfl (chainN rfl (chainN rfl
                (chainN rfl r1 r2) (hXAs u2 T2).1) r3) r4) r5
            · rw [h5O, h4O, h3O, hrvC, hrA i d]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            · intro k hk1 hk2 hk3 hk4 hk5
              rw [hf5 k hk1 hk2 hk3 hk4 hk5, hf4 k hk2 hk3 hk4 hk5, hf3 k hk2 hk3,
                hf2 k hk1 hk3 hk4 hk2, hf1 k hk1]
          · -- THE DIAGONAL: the guard fires BEFORE the emitter and emits nothing, and the
            -- empty block is its own reverse
            subst hij
            obtain ⟨u2, T2, r2, htk2, h2A, h2B, h2I, hf2⟩ := hMMA i 0
              ((rs.map enc).flatten ++ tail) u1 T1 htk1 h1A h1B
            have h2O : T2 kopc = S kopc := by rw [hf2 kopc nea nec ned neb, h1O]
            have h2I' : T2 kidx = List.replicate i (ei true)
                ++ (ei false :: (ei false :: [])) := by
              simp [h2I, h1I]
            obtain ⟨u3, T3, r3, h3I, h3A, h3O, hf3⟩ := hGDG i [] (sdt u2) T2 h2I' h2A
            have h3B : T3 kscB = [] := by rw [hf3 kscB ndb ndc, h2B]
            have h3K : T3 ktok = (rs.map enc).flatten ++ tail := by
              rw [hf3 ktok nab nac, htk2]
            have h3O' : T3 kopc = S kopc := by rw [h3O, h2O]
            obtain ⟨N5, u5, T5, hbd5, r5, htk5, h5I, h5A, h5B, h5O, hf5⟩ :=
              ih tail u3 T3 hrs h3K h3I h3A h3B
            refine ⟨6 + (5 * i + 2 * 0 + 8) + 1 + (3 * i + 0 + 7) + N5, u5, T5, ?_, ?_,
              htk5, h5I, h5A, h5B, ?_, ?_⟩
            · rw [hlenc, hlenr, hE]
              omega
            · exact chainN rfl (chainN rfl (chainN rfl
                (chainN rfl r1 r2) (hXAs u2 T2).1) r3) r5
            · rw [h5O, h3O', hrvC, hrD i]
              simp only [List.append_nil]
            · intro k hk1 hk2 hk3 hk4 hk5
              rw [hf5 k hk1 hk2 hk3 hk4 hk5, hf3 k hk2 hk3, hf2 k hk1 hk3 hk4 hk2,
                hf1 k hk1]
          · -- CONTROL ABOVE TARGET.  The `lXB` seam now CLEARS the bit (swap two) and goes
            -- straight to the BIT-CLEAR emitter, whose mirrored shape is
            -- `(blk [4, i, j]).reverse` at the larger difference.
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
            subst hd
            obtain ⟨u2, T2, r2, htk2, h2A, h2B, h2I, hf2⟩ := hMMB j d
              ((rs.map enc).flatten ++ tail) u1 T1 htk1 h1A h1B
            have h2O : T2 kopc = S kopc := by rw [hf2 kopc nea nec ned neb, h1O]
            have h2I' : T2 kidx = List.replicate j (ei true)
                ++ (ei false :: (List.replicate (d + 1) (ei true) ++ (ei false :: []))) := by
              rw [h2I, h1I]
            obtain ⟨u4, T4, r4, h4I, h4A, h4B, h4O, hf4⟩ :=
              hE2F j (d + 1) [] (sdf u2) T2 (hXBs u2 T2).2 h2I' h2A h2B
            have h4K : T4 ktok = (rs.map enc).flatten ++ tail := by
              rw [hf4 ktok nab nac nad nae, htk2]
            obtain ⟨N5, u5, T5, hbd5, r5, htk5, h5I, h5A, h5B, h5O, hf5⟩ :=
              ih tail u4 T4 hrs h4K h4I h4A h4B
            refine ⟨6 + (5 * j + 2 * d + 11) + 1 + (2 * j + 2 * (d + 1) + 6) + N5, u5, T5,
              ?_, ?_, htk5, h5I, h5A, h5B, ?_, ?_⟩
            · rw [hlenc, hlenr, hE]
              omega
            · exact chainN rfl (chainN rfl (chainN rfl
                (chainN rfl r1 r2) (hXBs u2 T2).1) r4) r5
            · rw [h5O, h4O, h2O, hrvC, hrB j d]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            · intro k hk1 hk2 hk3 hk4 hk5
              rw [hf5 k hk1 hk2 hk3 hk4 hk5, hf4 k hk2 hk3 hk4 hk5,
                hf2 k hk1 hk3 hk4 hk2, hf1 k hk1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro recs v S hwf hS hI hA hB
    have hS' : S ktok = (recs.map enc).flatten ++ [] := by
      rw [hS, List.append_nil]
    obtain ⟨N, u, T, hbd, r1, htk, hTI, hTA, hTB, hTO, hf⟩ :=
      hLoop recs [] v S hwf hS' hI hA hB
    obtain ⟨u2, r2⟩ := hEXIT u T htk
    have hbt : N + 2 ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length + 2 := by
      omega
    exact ⟨N + 2, u2, T, hbt, chainN rfl r1 r2, htk, hTI, hTA, hTB, hTO, hf⟩
  · intro recs t v S hwf hS hI hA hB
    obtain ⟨N, u, T, hbd, r1, htk, hTI, hTA, hTB, hTO, hf⟩ :=
      hLoop recs (List.replicate t (eo true)) v S hwf hS hI hA hB
    obtain ⟨u2, T2, r2, htk2, hf2⟩ := hTRUNC t u T htk
    have hbt : N + (t + 2)
        ≤ 9 * ((recs.map enc).flatten).length + 26 * recs.length + t + 2 := by omega
    refine ⟨N + (t + 2), u2, T2, hbt, ?_, htk2, ?_, ?_, ?_, ?_, ?_⟩
    · exact chainN rfl r1 r2
    · rw [hf2 kidx nba, hTI]
    · rw [hf2 kscA nca, hTA]
    · rw [hf2 kscB nda, hTB]
    · rw [hf2 kopc nea, hTO]
    · intro k hk1 hk2 hk3 hk4 hk5
      rw [hf2 k hk1, hf k hk1 hk2 hk3 hk4 hk5]
  · intro L R
    omega
  · have h1 : ¬ (24 : ℕ) = 0 := by decide
    have h2 : ¬ (3 : ℕ) = 0 := by decide
    have h3 : 9 * 24 + 26 * 3 + 2 = 296 := by decide
    have h4 : ¬ (9 * 24 + 26 * 3 + 2 = 9 * (24 + 1) + 26 * 3 + 2) := by decide
    have h5 : ¬ (9 * 24 + 26 * 3 + 2 = 9 * 24 + 26 * (3 + 1) + 2) := by decide
    exact ⟨24, 3, h1, h2, h3, h4, h5⟩
  · -- THE ROUND TRIP.  `FLAT-1b`'s induction, with its ONE use of the strong hypothesis --
    -- the `by omega` that turned `t < 4` into the parser equation's `¬ t = 4` -- replaced
    -- by the weak hypothesis itself.  Nothing else in the argument changes, which is the
    -- whole content of the claim that the accepted conjunct was understated.
    intro pg pg0 pg4 pg5 recs
    induction recs with
    | nil =>
        intro r _
        simp only [List.length_nil, List.flatten_nil, List.nil_append]
        rw [pg0]
    | cons rec rs ih =>
        intro r hwf
        have hrest : ∀ q ∈ rs, (∃ t i : ℕ, ¬ t = 4 ∧ q = [t, i])
            ∨ (∃ i j : ℕ, q = [4, i, j]) :=
          fun q hq => hwf q (List.mem_cons.mpr (Or.inr hq))
        have hih := ih r hrest
        have hlen : (rec :: rs).length = rs.length + 1 := List.length_cons
        rcases hwf rec (List.mem_cons.mpr (Or.inl rfl)) with ⟨t, i, hti, hrec⟩ | ⟨i, j, hrec⟩
        · subst hrec
          have hfl : (([t, i] : List ℕ) :: rs).flatten ++ r
              = t :: i :: (rs.flatten ++ r) := by
            simp only [List.flatten_cons, List.cons_append, List.nil_append]
          rw [hlen, hfl, pg4 t i rs.length (rs.flatten ++ r) hti, hih]
        · subst hrec
          have hfl : (([4, i, j] : List ℕ) :: rs).flatten ++ r
              = 4 :: i :: j :: (rs.flatten ++ r) := by
            simp only [List.flatten_cons, List.cons_append, List.nil_append]
          rw [hlen, hfl, pg5 i j rs.length (rs.flatten ++ r), hih]

end BQPReferenceValidation.Source45

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate45
    let target ← getConstInfo ``ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate45
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts; axioms {axioms}"
