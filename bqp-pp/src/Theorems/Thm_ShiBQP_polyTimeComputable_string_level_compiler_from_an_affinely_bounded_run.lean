-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run`. The real proof is on prove2.me.
import Definitions.Def_PvsNP

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run :
    -- (1) THE OUTPUT BUDGET ON EVERY PAIR OF STRINGS, ∀-QUANTIFIED IN ALL EIGHT FUNCTIONS.
    -- `PAIRDECd` (1) bounds the compiled program only where the decode has at least three
    -- fields; `COMPILE-STRcb` (4)'s three totality clauses cover the rest, so the budget
    -- `PAIRDECc` (3) demands holds at garbage too.  No existential, no well-formedness.
    (∀ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
        (blk blkA : List ℕ → List ℕ) (L E : List Bool → List ℕ)
        (enc : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool),
      (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length) →
      (∀ (k : ℕ) (ts : List ℕ),
        ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
          ≤ ts.sum + ts.length) →
      (∀ P : List ℕ, (enc P).length = 4 * P.length) →
      (∀ l : List Bool, (L l).length ≤ 2 * l.length) →
      (∀ l : List Bool, (E l).length ≤ 4 * l.length) →
      (∀ d : List ℕ, (blk d).length ≤ 2 * (d.sum + d.length)) →
      (∀ d : List ℕ, (blkA d).length ≤ 2 * (d.sum + d.length)) →
      (∀ (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
        unpack s = anc :: out :: nl :: rest →
        encCompile s x
          = enc (L (x ++ List.replicate (anc + 1) false)
              ++ (List.replicate (x.length + (anc + 1)) 0
              ++ ((((pl nl rest).1).map blk).flatten
              ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
              ++ (((((pl nl rest).1).reverse).map blkA).flatten
              ++ (E (x ++ List.replicate (anc + 1) false)
                ++ List.replicate (x.length + (anc + 1)) 0))))))) →
      (∀ s x : List Bool, unpack s = [] → encCompile s x = []) →
      (∀ (s x : List Bool) (a : ℕ), unpack s = [a] → encCompile s x = []) →
      (∀ (s x : List Bool) (a b : ℕ), unpack s = [a, b] → encCompile s x = []) →
      ∀ s x : List Bool, (encCompile s x).length ≤ 56 * (s.length + x.length + 1))
    -- (2) THE ENDPOINT.  Given a machine whose EXACT step count `f` is bounded by ANY
    -- affine function of (input length + output length), the string-level compiler paired
    -- along the tagged decoders is polynomial-time computable.  `f`, `p`, `q`, `c`, the
    -- machine, both alphabet identifications, and all eight compiler-side functions are
    -- universally quantified; the eight decoder equations are `rfl`s for a consumer.  This
    -- is `PAIRDECc` (3) at `gc := encCompile`, with `PAIRDECd` (1) supplying the budget.
    ∧ (∀ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
        (blk blkA : List ℕ → List ℕ) (L E : List Bool → List ℕ)
        (enc : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool)
        (unL unR : List Bool → List Bool) (tm : Turing.FinTM2)
        (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
        (f : List Bool → ℕ) (p q c : ℕ),
      (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length) →
      (∀ (k : ℕ) (ts : List ℕ),
        ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
          ≤ ts.sum + ts.length) →
      (∀ P : List ℕ, (enc P).length = 4 * P.length) →
      (∀ l : List Bool, (L l).length ≤ 2 * l.length) →
      (∀ l : List Bool, (E l).length ≤ 4 * l.length) →
      (∀ d : List ℕ, (blk d).length ≤ 2 * (d.sum + d.length)) →
      (∀ d : List ℕ, (blkA d).length ≤ 2 * (d.sum + d.length)) →
      (∀ (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
        unpack s = anc :: out :: nl :: rest →
        encCompile s x
          = enc (L (x ++ List.replicate (anc + 1) false)
              ++ (List.replicate (x.length + (anc + 1)) 0
              ++ ((((pl nl rest).1).map blk).flatten
              ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
              ++ (((((pl nl rest).1).reverse).map blkA).flatten
              ++ (E (x ++ List.replicate (anc + 1) false)
                ++ List.replicate (x.length + (anc + 1)) 0))))))) →
      (∀ s x : List Bool, unpack s = [] → encCompile s x = []) →
      (∀ (s x : List Bool) (a : ℕ), unpack s = [a] → encCompile s x = []) →
      (∀ (s x : List Bool) (a b : ℕ), unpack s = [a, b] → encCompile s x = []) →
      unL [] = [] → (∀ b : Bool, unL [b] = []) →
      (∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t) →
      (∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = []) →
      unR [] = [] → (∀ b : Bool, unR [b] = []) →
      (∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t) →
      (∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
        (f w))) →
      (∀ w : List Bool,
        f w ≤ p * w.length + q * (encCompile (unL w) (unR w)).length + c) →
      PvsNP.PolyTimeComputable (fun w => encCompile (unL w) (unR w)))
    -- (3) NON-VACUITY, AS A CONJUNCT.  Eight concrete functions satisfy every
    -- function-level hypothesis of (1) and (2) with a compiler that is NOT the
    -- constant-empty one: it depends on its second argument, and both output lengths are
    -- pinned.  So the hypothesis block is consistent and does not collapse to `[]`.
    ∧ (∃ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (blk blkA : List ℕ → List ℕ) (L E : List Bool → List ℕ)
          (enc : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool),
        (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
      ∧ (∀ (k : ℕ) (ts : List ℕ),
          ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
            ≤ ts.sum + ts.length)
      ∧ (∀ P : List ℕ, (enc P).length = 4 * P.length)
      ∧ (∀ l : List Bool, (L l).length ≤ 2 * l.length)
      ∧ (∀ l : List Bool, (E l).length ≤ 4 * l.length)
      ∧ (∀ d : List ℕ, (blk d).length ≤ 2 * (d.sum + d.length))
      ∧ (∀ d : List ℕ, (blkA d).length ≤ 2 * (d.sum + d.length))
      ∧ (∀ (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
          unpack s = anc :: out :: nl :: rest →
          encCompile s x
            = enc (L (x ++ List.replicate (anc + 1) false)
                ++ (List.replicate (x.length + (anc + 1)) 0
                ++ ((((pl nl rest).1).map blk).flatten
                ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
                ++ (((((pl nl rest).1).reverse).map blkA).flatten
                ++ (E (x ++ List.replicate (anc + 1) false)
                  ++ List.replicate (x.length + (anc + 1)) 0)))))))
      ∧ (∀ s x : List Bool, unpack s = [] → encCompile s x = [])
      ∧ (∀ (s x : List Bool) (a : ℕ), unpack s = [a] → encCompile s x = [])
      ∧ (∀ (s x : List Bool) (a b : ℕ), unpack s = [a, b] → encCompile s x = [])
      ∧ unpack [false, false, false] = [0, 0, 0]
      ∧ (encCompile [false, false, false] []).length = 20
      ∧ (encCompile [false, false, false] [false]).length = 36
      ∧ encCompile [false, false, false] []
          ≠ encCompile [false, false, false] [false]
      ∧ (∀ s x : List Bool, (encCompile s x).length ≤ 56 * (s.length + x.length + 1)))
    -- (4) THE MONOTONICITY STEP, EXPORTED.  `TM2OutputsInTime` is an upper bound, so a
    -- machine slice may hand (2) its exact step count and let (2) do the weakening; this
    -- conjunct lets a machine slice do the weakening itself instead.
    ∧ (∀ (tm : Turing.FinTM2) (u : List (tm.Γ tm.k₀)) (o : Option (List (tm.Γ tm.k₁)))
        (m m' : ℕ), m ≤ m' →
        Nonempty (Turing.TM2OutputsInTime tm u o m) →
        Nonempty (Turing.TM2OutputsInTime tm u o m')) := by
  sorry

end ShiBQP
