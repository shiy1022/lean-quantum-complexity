-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open ShiShallow ShiClass ShiBQP

namespace ShiBQP

theorem the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities :
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
  sorry

end ShiBQP
