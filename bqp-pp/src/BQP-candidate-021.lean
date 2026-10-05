import Definitions.Def_ShiBQP_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities

namespace BQPReferenceValidation.Source21
/-
COMPILE-FLATb.  THE STRING-LEVEL COMPILER, CHARACTERISED OVER THE *FLAT* ENCODING.

This is the route (b) analogue of `COMPILE-STRcb`.  `COMPILE-STRcb` is ACCEPTED and SOUND and
is NOT modified here; every statement below is new.

WHY A NEW STATEMENT IS NEEDED RATHER THAN AN INSTANTIATION.  `COMPILE-STRcb` quantifies over a
parser `pl` and constrains it ONLY through its hypothesis `hpar`,

  pl (F.circ n).length ((unpack (encFamilyAt F n)).drop 3)
    = ((F.circ n).flatten.map (tk ...), [])

so one cannot instantiate `pl := pg`: the same instantiation must discharge `hpar`, and that
statement is FALSE for `pg` (RESUME 492 -- `pl` counts LAYERS and eats the per-layer length
token, `pg` counts GATES and eats nothing).  What CAN be reused verbatim is `COMPILE-STRcb`
conjunct (2), the padding clause, which mentions no parser at all; it is therefore NOT
restated here.

WHAT IS NEW, AND WHERE IT COMES FROM.

* (1) THE FLAT DECODE.  `COMPILE-STR` (2) and (8) are stream-position-agnostic: they say
  `unpack (encNat k ++ r) = k :: unpack r` and `unpack (encInstr g ++ r) = tk m g ++ unpack r`
  for ANY suffix `r`.  Neither mentions layers, so both apply unchanged to a flat body.  Three
  applications of (2) split the header; an induction on the gate list over (8) converts the
  body.  Nothing about `encFamilyAt` is used.

* (2) THE PARSER CONSUMES THE WHOLE BODY.  Here the route (b) payoff is visible: the needed
  fact is `COMPILE-STR` (16),
  `pg l.length ((l.map (tk m)).flatten ++ r) = (l.map (tk m), r)`, at `l := gate list` and
  `r := []`.  That is ALREADY ACCEPTED.  `FLAT-1b` (5) proves the same round trip from `pg`'s
  defining equations under an explicit well-formedness side condition, which would then have
  to be discharged by a five-constructor case split on `Instr`; (16) is stated directly over
  `tk`-images and so carries that case split already.  `FLAT-1b` (3) (prefix consumption) is
  likewise not needed at this slice -- it is what makes the SEAM work on an arbitrary string,
  whereas here the string is canonical by construction.

* (3) AGREEMENT.  The same assembly as `COMPILE-STRcb` (1), with `(pl nl rest).1` replaced by
  `(pg ng rest).1` throughout, `nl` (the layer count) replaced by `ng` (the gate count), and
  the composite parser fact supplied by (2) instead of by `hpar`.

* (4) STRUCTURE, over `(pg ng rest).1`.  This is the whole point of the slice: the compiled
  program is built from the gate records the GATE parser returns, so no layer-length token is
  ever read and none is ever written.  The three totality clauses are transcribed unchanged --
  a decode with fewer than three fields compiles to the empty program (gotcha 223).

THE `encFlat` CONTRACT IS TAKEN VERBATIM from `wave30 ENCFLAT_CONTRACT.md`, as a BINDER with
its defining equation as a hypothesis, character for character, so that this slice welds with
the transducer slice built against the same contract.  Nothing here defines `encFlat`, and
nothing here produces the transducer `encFamilyAt F n` to `encFlat F n`; that remains
mandatory and is not claimed.

REFUTATION-FIRST CHECK (RESUME 498), CARRIED IN THE STATEMENT RATHER THAN IN A COMMENT.
Conjunct (NVa) computes the contract's right-hand side, against the REAL `encNat` and
`encInstr`, at the smallest non-degenerate witness -- ancilla count `0`, output wire `0`, one
`H` gate on wire `0` -- and gets `[false, false, true, false, false, false]`.  Decoding that
gives `0 :: 0 :: 1 :: [0, 0]`, the third field EQUALS the gate count, and `pg 1 [0, 0]`
returns one record (`FLAT-1b` (8)).  The witness class that killed `hSHAPE` three times is one
empty LAYER; under the flat encoding an empty circuit carries no layer token at all, and
conjuncts (NVb) and (NVc) state exactly that: empty body, third field `0`, whole string
`[false, false, false]` when the ancilla count and the output index are `0`.  Had the contract
been wrong about field order or about the third field, (NVa) would fail as a computation.

A NEW LEAN TRAP, WORTH RECORDING.  `++` is LEFT associative, so the contract's right-hand side
parses as `((encNat anc ++ encNat out) ++ encNat ng) ++ body`, and the one-field decoder
equation `unpack (encNat k ++ r) = k :: unpack r` does NOT match it -- `rw` reports "did not
find an occurrence" with a goal that LOOKS like a match.  A `simp only [List.append_assoc]`
must come first.  This bites every consumer of the contract, including the parallel transducer
slice, and it is the same family as the `simp [encFamilyAt, List.append_assoc]` step that
`COMPILE-STR` needed for the layered encoding.

No `namespace` (gotcha 468).  `::` parenthesised against `+` (gotcha 494).  No abbreviation is
joined by a slash to a hyphenated name anywhere in this file (gotcha 499a).

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow ShiClass ShiBQP

/-- The flat-encoding string compiler: header fields plus the GATE parser's records.  Total on
every string (gotcha 223). -/
private def ecF (enc : List ℕ → PvsNP.Str) (unpack : PvsNP.Str → List ℕ)
    (pg : ℕ → List ℕ → List (List ℕ) × List ℕ) (blk blkA : List ℕ → List ℕ)
    (L E : List Bool → List ℕ) : PvsNP.Str → PvsNP.Str → PvsNP.Str := fun s x =>
  match unpack s with
  | anc :: out :: ng :: rest =>
      enc (L (x ++ List.replicate (anc + 1) false)
        ++ (List.replicate (x.length + (anc + 1)) 0
        ++ ((((pg ng rest).1).map blk).flatten
        ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
        ++ (((((pg ng rest).1).reverse).map blkA).flatten
        ++ (E (x ++ List.replicate (anc + 1) false)
          ++ List.replicate (x.length + (anc + 1)) 0))))))
  | _ => []

/-- `BRIDGE-C2c`'s padded input is a plain string concatenation.  Identical to the step inside
`COMPILE-STRcb`; reproved here because that file exports it only as a conjunct. -/
private lemma fc_ofFn_pad (x : PvsNP.Str) (m' : ℕ) :
    List.ofFn (fun k : Fin (x.length + m') =>
        if h : (k : ℕ) < x.length then (toBits x) ⟨(k : ℕ), h⟩ else false)
      = x ++ List.replicate m' false := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases hi : i < x.length
    · rw [dif_pos hi]
      simp [toBits, hi, List.get_eq_getElem]
    · rw [dif_neg hi]
      simp [List.getElem_append, hi]

/-- The decoder is compositional along a FLAT gate stream.  This is `COMPILE-STR` (8) iterated;
it holds for any suffix `r`, which is precisely why the layered structure is irrelevant. -/
private lemma fc_unpack_body (unpack : PvsNP.Str → List ℕ) (tk : ∀ m : ℕ, Instr m → List ℕ)
    (hinstr : ∀ (m : ℕ) (g : Instr m) (r : PvsNP.Str),
      unpack (encInstr g ++ r) = tk m g ++ unpack r) :
    ∀ (m : ℕ) (gs : List (Instr m)) (r : PvsNP.Str),
      unpack ((gs.map encInstr).flatten ++ r) = (gs.map (tk m)).flatten ++ unpack r := by
  intro m gs
  induction gs with
  | nil => intro r; simp
  | cons g gs ih =>
      intro r
      have h : (((g :: gs).map encInstr).flatten ++ r)
          = encInstr g ++ ((gs.map encInstr).flatten ++ r) := by
        simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      rw [h, hinstr m g, ih r]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]

theorem _root_.BQPReferenceValidation.candidate21 :
    ∀ (enc : List ℕ → PvsNP.Str) (unpack : PvsNP.Str → List ℕ)
      (tk : ∀ m : ℕ, Instr m → List ℕ)
      (pg : ℕ → List ℕ → List (List ℕ) × List ℕ) (blk blkA : List ℕ → List ℕ)
      (L E : List Bool → List ℕ) (T : ∀ n m' : ℕ, Bits n → List Bool)
      (D DA : ∀ m : ℕ, List (Instr m) → List ℕ)
      (C : ∀ n m' : ℕ, List (Instr (n + m')) → Bits n → Fin (n + m') → List ℕ)
      (encFlat : Family → ℕ → PvsNP.Str),
      -- THE `encFlat` CONTRACT, verbatim
      (∀ (F : Family) (n : ℕ),
        encFlat F n
          = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
            ++ encNat (((F.circ n).flatten).length)
            ++ ((((F.circ n).flatten).map encInstr).flatten)) →
      -- COMPILE-STR (1)-(2): the decoder, one unary-terminated field at a time
      unpack [] = [] →
      (∀ (k : ℕ) (r : PvsNP.Str), unpack (encNat k ++ r) = k :: unpack r) →
      -- COMPILE-STR (8): decoding is compositional over instruction codes
      (∀ (m : ℕ) (g : Instr m) (r : PvsNP.Str),
        unpack (encInstr g ++ r) = tk m g ++ unpack r) →
      -- COMPILE-STR (16): the GATE parser's round trip on a token stream
      (∀ (m : ℕ) (l : List (Instr m)) (r : List ℕ),
        pg l.length ((l.map (tk m)).flatten ++ r) = (l.map (tk m), r)) →
      -- COMPILE-STRb (8)-(9): rendering reproduces the forward and adjoint sweeps
      (∀ (m : ℕ) (gs : List (Instr m)), ((gs.map (tk m)).map blk).flatten = D m gs) →
      (∀ (m : ℕ) (gs : List (Instr m)),
        (((gs.map (tk m)).reverse).map blkA).flatten = DA m gs) →
      -- BRIDGE-C2c: the padded input and the whole route-(A) program
      (∀ (n m' : ℕ) (x : Bits n), T n m' x
        = List.ofFn (fun k : Fin (n + m') =>
            if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false)) →
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
        C n m' gs x out
          = L (T n m' x) ++ (List.replicate (n + m') 0 ++ (D (n + m') gs
              ++ ((List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0))
                ++ (DA (n + m') gs
                  ++ (E (T n m' x) ++ List.replicate (n + m') 0)))))) →
      -- (1) THE FLAT DECODE: the flat encoding is a three-field header followed by the flat
      -- gate-token stream.  No layer-length token appears anywhere, so the third field is the
      -- GATE count and the body is a single run of records.
      ((∀ (F : Family) (n : ℕ),
        unpack (encFlat F n)
          = F.anc n :: ((F.out n : ℕ)) :: (((F.circ n).flatten).length)
            :: ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))).flatten))
      -- (2) THE GATE PARSER CONSUMES THE WHOLE BODY AND RETURNS EXACTLY THE GATE RECORDS.
      -- Compare `COMPILE-STRcb`'s `hpar`, which is the same shape with the LAYER parser and
      -- the LAYER count; that statement is false of `pg`, and this one is false of `pl`.
      ∧ (∀ (F : Family) (n : ℕ),
          pg (((F.circ n).flatten).length) ((unpack (encFlat F n)).drop 3)
            = ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))), []))
      -- (NVa) THE REFUTATION-FIRST WITNESS, COMPUTED.  The contract's right-hand side at
      -- ancilla count `0`, output wire `0` and the one-gate circuit `[H 0]`.  This pins the
      -- field order and, in particular, that the third field is the gate count.
      ∧ (encNat 0 ++ encNat 0 ++ encNat (([Instr.h (0 : Fin 1)]).length)
            ++ (([Instr.h (0 : Fin 1)]).map encInstr).flatten
          = [false, false, true, false, false, false])
      -- (NVb) THE DEGENERATE WITNESS.  An empty circuit carries NO layer token under the flat
      -- encoding: the third field is `0` and the body is empty, full stop.  This is the
      -- witness class on which `hSHAPE` was refuted -- RESUME 492 used ONE EMPTY LAYER, which
      -- under `encFamilyAt` decodes to `0 :: 0 :: 1 :: [0]`, the third field disagreeing with
      -- the gate count.  Taken with (NVc) at `anc = out = 0` the encoding is `[F, F, F]`.
      ∧ (∀ (F : Family) (n : ℕ), (F.circ n).flatten = [] →
          encFlat F n = encNat (F.anc n) ++ encNat ((F.out n : ℕ)) ++ encNat 0)
      -- (NVc) the three empty unary fields, computed.
      ∧ (encNat 0 ++ encNat 0 ++ encNat 0 = [false, false, false])
      ∧ ∃ encCompileF : PvsNP.Str → PvsNP.Str → PvsNP.Str,
          -- (3) AGREEMENT with the route-(A) syntactic compiler `C`, at the FLAT encoding.
          -- The analogue of `COMPILE-STRcb` (1); the compiled program is identical, since the
          -- flat encoding differs from the layered one only in tokens the compiler discards.
          (∀ (F : Family) (x : PvsNP.Str),
            encCompileF (encFlat F x.length) x
              = enc (C x.length (F.anc x.length + 1) ((F.circ x.length).flatten)
                  (toBits x) (F.out x.length)))
          -- (4) STRUCTURE, over `(pg ng rest).1` and NOT over any layer parser.
          ∧ (∀ (s x : PvsNP.Str) (anc out ng : ℕ) (rest : List ℕ),
              unpack s = anc :: out :: ng :: rest →
              encCompileF s x
                = enc (L (x ++ List.replicate (anc + 1) false)
                    ++ (List.replicate (x.length + (anc + 1)) 0
                    ++ ((((pg ng rest).1).map blk).flatten
                    ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
                    ++ (((((pg ng rest).1).reverse).map blkA).flatten
                    ++ (E (x ++ List.replicate (anc + 1) false)
                      ++ List.replicate (x.length + (anc + 1)) 0)))))))
          -- (5)-(7) TOTALITY: a decode with fewer than three fields compiles to the empty
          -- string, so the numeric-predicate side condition of the weld is unchanged.
          ∧ (∀ (s x : PvsNP.Str), unpack s = [] → encCompileF s x = [])
          ∧ (∀ (s x : PvsNP.Str) (a : ℕ), unpack s = [a] → encCompileF s x = [])
          ∧ (∀ (s x : PvsNP.Str) (a b : ℕ), unpack s = [a, b] → encCompileF s x = [])) := by
  intro enc unpack tk pg blk blkA L E T D DA C encFlat hFlat hnil hnat hinstr hpg hfwd hadj
  intro hT hC
  have hbody := fc_unpack_body unpack tk hinstr
  have hbody0 : ∀ (m : ℕ) (gs : List (Instr m)),
      unpack ((gs.map encInstr).flatten) = (gs.map (tk m)).flatten := by
    intro m gs
    have h := hbody m gs []
    rw [List.append_nil, hnil, List.append_nil] at h
    exact h
  -- (1)
  have hdec : ∀ (F : Family) (n : ℕ),
      unpack (encFlat F n)
        = F.anc n :: ((F.out n : ℕ)) :: (((F.circ n).flatten).length)
          :: ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))).flatten) := by
    intro F n
    rw [hFlat F n]
    -- `++` is LEFT associative, so the contract's right-hand side must be reassociated
    -- before the one-field decoder equation can fire.
    simp only [List.append_assoc]
    rw [hnat, hnat, hnat, hbody0]
  -- the parser fact, from COMPILE-STR (16) at `r := []`
  have hpg0 : ∀ (m : ℕ) (l : List (Instr m)),
      pg l.length ((l.map (tk m)).flatten) = (l.map (tk m), []) := by
    intro m l
    have h := hpg m l []
    rw [List.append_nil] at h
    exact h
  have hpg1 : ∀ (m : ℕ) (l : List (Instr m)),
      (pg l.length ((l.map (tk m)).flatten)).1 = l.map (tk m) := by
    intro m l
    rw [hpg0 m l]
  -- (2)
  have hpar : ∀ (F : Family) (n : ℕ),
      pg (((F.circ n).flatten).length) ((unpack (encFlat F n)).drop 3)
        = ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))), []) := by
    intro F n
    have hd : ((unpack (encFlat F n)).drop 3)
        = ((((F.circ n).flatten).map (tk (n + (F.anc n + 1)))).flatten) := by
      rw [hdec F n]
      rfl
    rw [hd]
    exact hpg0 (n + (F.anc n + 1)) ((F.circ n).flatten)
  -- (NVb)
  have hnvb : ∀ (F : Family) (n : ℕ), (F.circ n).flatten = [] →
      encFlat F n = encNat (F.anc n) ++ encNat ((F.out n : ℕ)) ++ encNat 0 := by
    intro F n hc
    rw [hFlat F n, hc]
    simp
  -- the compiler
  have hkey : ∀ (s x : PvsNP.Str) (anc out ng : ℕ) (rest : List ℕ),
      unpack s = anc :: out :: ng :: rest →
      ecF enc unpack pg blk blkA L E s x
        = enc (L (x ++ List.replicate (anc + 1) false)
            ++ (List.replicate (x.length + (anc + 1)) 0
            ++ ((((pg ng rest).1).map blk).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pg ng rest).1).reverse).map blkA).flatten
            ++ (E (x ++ List.replicate (anc + 1) false)
              ++ List.replicate (x.length + (anc + 1)) 0)))))) := by
    intro s x anc out ng rest hs
    show (match unpack s with
          | anc :: out :: ng :: rest => _
          | _ => []) = _
    rw [hs]
  have hpad : ∀ (x : PvsNP.Str) (m' : ℕ),
      T x.length m' (toBits x) = x ++ List.replicate m' false := by
    intro x m'
    rw [hT]
    exact fc_ofFn_pad x m'
  refine ⟨hdec, hpar, by decide, hnvb, by decide,
    ecF enc unpack pg blk blkA L E, ?_, hkey, ?_, ?_, ?_⟩
  · intro F x
    rw [hkey (encFlat F x.length) x (F.anc x.length) ((F.out x.length : ℕ))
      (((F.circ x.length).flatten).length)
      ((((F.circ x.length).flatten).map
        (tk (x.length + (F.anc x.length + 1)))).flatten) (hdec F x.length)]
    rw [hC x.length (F.anc x.length + 1) ((F.circ x.length).flatten) (toBits x)
      (F.out x.length)]
    rw [hpg1 (x.length + (F.anc x.length + 1)) ((F.circ x.length).flatten)]
    rw [hfwd, hadj, hpad x (F.anc x.length + 1)]
  · intro s x hs
    show (match unpack s with
          | anc :: out :: ng :: rest => _
          | _ => []) = _
    rw [hs]
  · intro s x a hs
    show (match unpack s with
          | anc :: out :: ng :: rest => _
          | _ => []) = _
    rw [hs]
  · intro s x a b hs
    show (match unpack s with
          | anc :: out :: ng :: rest => _
          | _ => []) = _
    rw [hs]

end BQPReferenceValidation.Source21

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate21
    let target ← getConstInfo ``ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate21
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities; axioms {axioms}"
