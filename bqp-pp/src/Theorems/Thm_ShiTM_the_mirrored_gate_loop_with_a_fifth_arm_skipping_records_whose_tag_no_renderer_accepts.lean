-- Isolated target snapshot from saved campaign metadata; NOT a proof.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

namespace ShiTM

theorem the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts
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
  sorry

end ShiTM

