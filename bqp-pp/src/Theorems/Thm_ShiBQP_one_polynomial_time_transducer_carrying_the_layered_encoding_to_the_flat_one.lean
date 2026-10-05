-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open ShiShallow ShiClass ShiBQP

namespace ShiBQP

theorem one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one :
    ∀ (encFlat : Family → ℕ → PvsNP.Str),
      -- the `encFlat` contract, character for character
      (∀ (F : Family) (n : ℕ),
        encFlat F n
          = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
            ++ encNat (((F.circ n).flatten).length)
            ++ ((((F.circ n).flatten).map encInstr).flatten)) →
      -- `PHI-Ac` conjunct (A): the pinned-binder transducer laws
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
                  + 2 * c.length))) →
      -- `PHI-Ac` conjunct (5): closed functions satisfying every one of the nineteen equations
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
        ∧ (E [0, 0, 3, 0, 0, 1, 1, 4, 0, 1]).length = 20) →
      -- `PHI-B` conjunct (1): the lift to the real encodings
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
              = (encFlat' F n).length + 2 * (F.circ n).length) →
      -- `PHI-M3` conjunct (6) composed with `PHI-M4` conjunct (1): the machine, packaged
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
        PvsNP.PolyTimeComputable Φ) →
      -- THE TARGET.  ONE transducer, carrying BOTH properties.
      ∃ Φ : PvsNP.Str → PvsNP.Str,
        (∀ (F : Family) (n : ℕ), Φ (encFamilyAt F n) = encFlat F n)
        ∧ PvsNP.PolyTimeComputable Φ := by
  sorry

end ShiBQP
