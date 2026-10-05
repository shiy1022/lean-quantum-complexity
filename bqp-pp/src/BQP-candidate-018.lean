import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_polyTimeComputable_bridge_for_generic_pairing_decoders
import Theorems.Thm_ShiBQP_polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run
import Theorems.Thm_ShiBQP_string_level_compiler_output_budget_for_any_parser_pair

namespace BQPReferenceValidation.Source18
/-
WELD-E.  `PolyTimeComputable encCompile`, THE LAST NAMED OBLIGATION BEFORE THE HEADLINE.

`WELD-C` instantiated `PAIRDECc` (3) at a concrete machine with `gc := (· ++ ·)`.  This slice
is the same instantiation with `gc := encCompile`, the route-(A) string-level compiler.

THE RUN THEOREM IS TAKEN AS A HYPOTHESIS.  `MACH-B` did not close (gotcha 407): `MACH-A` has
three verified defects and only the front-end phase `MACH-B1` landed.  So, exactly as
`WELD-C`, `ASM-CONS` and every `BRIDGE-SIM` slice did, the end-to-end run is a HYPOTHESIS
here, in the weakest structural form we could find:

    (hf)  ∀ w, Nonempty (TM2OutputsInTime tm (map ea.invFun w)
                (some (map eb.invFun (encCompile (unL w) (unR w)))) (f w))
    (hbd) ∀ w, f w ≤ p * |w| + q * |encCompile (unL w) (unR w)| + c

with `f : List Bool → ℕ` and `p q c : ℕ` ALL universally quantified.  `f` is the machine's
EXACT step count, whatever shape `MACH-B2`/`MACH-B3` deliver it in -- it may mention
`|unL w|`, `|unR w|`, `|recs|`, anything -- and `hbd` is the only thing asked of it.  Nothing
here fixes the coefficients, so `MACH-B1`'s composed cost
`|w|/2 + 3|unL w| + 3|unR w| + 10` fits at `p = 7, q = 0, c = 10`, and so does any other
affine-in-(input + output) bound.

∀-QUANTIFICATION (gotcha 371).  `unpack, pl, blk, blkA, L, E, enc, encCompile` are all
universally quantified under their characterising equations -- `encCompile` is existentially
bound inside `COMPILE-STRcb`, so a theorem stated at a concrete `encCompile` could not
discharge it.  The parser/decoder/renderer equations come from `PARSE-TOT` and `RENDER-TOTb`
in the only form `PAIRDECc` (3) can use: budgets valid on EVERY string, plus `COMPILE-STRcb`
(3) and its three TOTALITY clauses (4), which is what makes conjunct (1) hold at garbage.

WHAT IS CONSUMED.  `PAIRDECc` (3) and `PAIRDECd` (1) -- never `COMPMACHe` (15) or
`COMPILE-STRd` (7), both of which are stated over functions bound in the same `∃` as the
conjunct and cannot be instantiated at a concrete machine (gotchas 330/340).

NON-VACUITY IS A CONJUNCT, NOT PROSE (gotcha 277).  Conjunct (3) exhibits eight concrete
functions satisfying all eleven function-level hypotheses of (1)/(2) whose compiler is NOT
the constant-empty one: it depends on its second argument, with both output lengths pinned.
The degenerate reading of the hypothesis block -- `encCompile ≡ []` -- is therefore refuted
inside the theorem and cannot be skipped.

This is the only slice of the weld that imports `Def_PvsNP`; it necessarily pays the ~300s
band (gotcha 332).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `TM2OutputsInTime` is an upper bound, so it is monotone in the budget. -/
private lemma bumpTime {tm : Turing.FinTM2} {u : List (tm.Γ tm.k₀)}
    {o : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (hm : m ≤ m')
    (h : Nonempty (Turing.TM2OutputsInTime tm u o m)) :
    Nonempty (Turing.TM2OutputsInTime tm u o m') := by
  obtain ⟨hi⟩ := h
  obtain ⟨he, hle⟩ := hi
  exact ⟨⟨he, Nat.le_trans hle hm⟩⟩

/-- A three-coefficient affine bound collapses into `PAIRDECc` (3)'s single-constant shape. -/
private lemma affBound (p q c W O : ℕ) :
    p * W + q * O + c ≤ (p + q + c) * (W + O) + (p + q + c) := by
  calc p * W + q * O + c
      ≤ (p * W + q * O + c) + (p * O + q * W + c * W + c * O + p + q) :=
        Nat.le_add_right _ _
    _ = (p + q + c) * (W + O) + (p + q + c) := by ring

/-- `PAIRDECd` (1) plus the three totality clauses give the budget on EVERY pair of strings,
garbage included -- which is what `PAIRDECc` (3) needs, since it quantifies over all `w`. -/
private lemma outBudget
    (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
    (blk blkA : List ℕ → List ℕ) (L E : List Bool → List ℕ)
    (enc : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool)
    (hu : ∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
    (hp : ∀ (k : ℕ) (ts : List ℕ),
      ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
        ≤ ts.sum + ts.length)
    (he : ∀ P : List ℕ, (enc P).length = 4 * P.length)
    (hL : ∀ l : List Bool, (L l).length ≤ 2 * l.length)
    (hE : ∀ l : List Bool, (E l).length ≤ 4 * l.length)
    (hb : ∀ d : List ℕ, (blk d).length ≤ 2 * (d.sum + d.length))
    (hbA : ∀ d : List ℕ, (blkA d).length ≤ 2 * (d.sum + d.length))
    (h3 : ∀ (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
      unpack s = anc :: out :: nl :: rest →
      encCompile s x
        = enc (L (x ++ List.replicate (anc + 1) false)
            ++ (List.replicate (x.length + (anc + 1)) 0
            ++ ((((pl nl rest).1).map blk).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pl nl rest).1).reverse).map blkA).flatten
            ++ (E (x ++ List.replicate (anc + 1) false)
              ++ List.replicate (x.length + (anc + 1)) 0)))))))
    (h0 : ∀ s x : List Bool, unpack s = [] → encCompile s x = [])
    (h1 : ∀ (s x : List Bool) (a : ℕ), unpack s = [a] → encCompile s x = [])
    (h2 : ∀ (s x : List Bool) (a b : ℕ), unpack s = [a, b] → encCompile s x = []) :
    ∀ s x : List Bool, (encCompile s x).length ≤ 56 * (s.length + x.length + 1) := by
  intro s x
  rcases hs : unpack s with _ | ⟨a, t⟩
  · rw [h0 s x hs]
    simp
  · rcases t with _ | ⟨b, u⟩
    · rw [h1 s x a hs]
      simp
    · rcases u with _ | ⟨n, r⟩
      · rw [h2 s x a b hs]
        simp
      · rw [h3 s x a b n r hs]
        exact ShiBQP.string_level_compiler_output_budget_for_any_parser_pair.1
          unpack pl enc L E blk blkA s x a b n r hu hp he hL hE hb hbA hs

/-- The instantiation of `PAIRDECc` (3) at `gc := encCompile`. -/
private lemma mainBridge
    (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
    (blk blkA : List ℕ → List ℕ) (L E : List Bool → List ℕ)
    (enc : List ℕ → List Bool) (encCompile : List Bool → List Bool → List Bool)
    (unL unR : List Bool → List Bool) (tm : Turing.FinTM2)
    (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (f : List Bool → ℕ) (p q c : ℕ)
    (hu : ∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
    (hp : ∀ (k : ℕ) (ts : List ℕ),
      ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
        ≤ ts.sum + ts.length)
    (he : ∀ P : List ℕ, (enc P).length = 4 * P.length)
    (hL : ∀ l : List Bool, (L l).length ≤ 2 * l.length)
    (hE : ∀ l : List Bool, (E l).length ≤ 4 * l.length)
    (hb : ∀ d : List ℕ, (blk d).length ≤ 2 * (d.sum + d.length))
    (hbA : ∀ d : List ℕ, (blkA d).length ≤ 2 * (d.sum + d.length))
    (h3 : ∀ (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
      unpack s = anc :: out :: nl :: rest →
      encCompile s x
        = enc (L (x ++ List.replicate (anc + 1) false)
            ++ (List.replicate (x.length + (anc + 1)) 0
            ++ ((((pl nl rest).1).map blk).flatten
            ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
            ++ (((((pl nl rest).1).reverse).map blkA).flatten
            ++ (E (x ++ List.replicate (anc + 1) false)
              ++ List.replicate (x.length + (anc + 1)) 0)))))))
    (h0 : ∀ s x : List Bool, unpack s = [] → encCompile s x = [])
    (h1 : ∀ (s x : List Bool) (a : ℕ), unpack s = [a] → encCompile s x = [])
    (h2 : ∀ (s x : List Bool) (a b : ℕ), unpack s = [a, b] → encCompile s x = [])
    (l0 : unL [] = []) (l1 : ∀ b : Bool, unL [b] = [])
    (lf : ∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t)
    (lt : ∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = [])
    (r0 : unR [] = []) (r1 : ∀ b : Bool, unR [b] = [])
    (rf : ∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t)
    (rt : ∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t)
    (hf : ∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun w)
      (Option.some (List.map eb.invFun (encCompile (unL w) (unR w))))
      (f w)))
    (hbd : ∀ w : List Bool,
      f w ≤ p * w.length + q * (encCompile (unL w) (unR w)).length + c) :
    PvsNP.PolyTimeComputable (fun w => encCompile (unL w) (unR w)) := by
  refine (ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders).2.2.1
    unL unR encCompile tm ea eb (p + q + c) l0 l1 lf lt r0 r1 rf rt
    (outBudget unpack pl blk blkA L E enc encCompile hu hp he hL hE hb hbA h3 h0 h1 h2) ?_
  intro w
  exact bumpTime (Nat.le_trans (hbd w) (affBound p q c _ _)) (hf w)

/-- Witness decoder: `|s|` zero fields, so `sum + length = |s|` and the budget is tight. -/
private def upv (w : List Bool) : List ℕ := List.replicate w.length 0

/-- Witness gate parser: empty group list, empty remainder. -/
private def plv (_ : ℕ) (_ : List ℕ) : List (List ℕ) × List ℕ := ([], [])

/-- Witness block renderer, used for both the forward and the adjoint sweep. -/
private def blkv (_ : List ℕ) : List ℕ := []

/-- Witness loading sweep: one opcode per padded input bit. -/
private def Lv (l : List Bool) : List ℕ := l.map (fun _ => 1)

/-- Witness unloading sweep: one opcode per padded input bit. -/
private def Ev (l : List Bool) : List ℕ := l.map (fun _ => 0)

/-- Witness opcode encoder: four bits per opcode, on the nose. -/
private def encv (P : List ℕ) : List Bool := List.replicate (4 * P.length) false

/-- The compiled program, as a function of the decoded field list alone. -/
private def bodyv (d : List ℕ) (x : List Bool) : List Bool :=
  encv (Lv (x ++ List.replicate (d.headI + 1) false)
    ++ (List.replicate (x.length + (d.headI + 1)) 0
    ++ (((plv (d.getD 2 0) (d.drop 3)).1.map blkv).flatten
    ++ ((List.replicate (d.getD 1 0) 1 ++ ([8] ++ List.replicate (d.getD 1 0) 0))
    ++ (((plv (d.getD 2 0) (d.drop 3)).1.reverse.map blkv).flatten
    ++ (Ev (x ++ List.replicate (d.headI + 1) false)
      ++ List.replicate (x.length + (d.headI + 1)) 0))))))

/-- Witness string-level compiler: total, empty on a decode with fewer than three fields. -/
private def ecompv (s x : List Bool) : List Bool :=
  if 3 ≤ (upv s).length then bodyv (upv s) x else []

theorem _root_.BQPReferenceValidation.candidate18 :
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
  refine ⟨fun unpack pl blk blkA L E enc encCompile hu hp he hL hE hb hbA h3 h0 h1 h2 =>
      outBudget unpack pl blk blkA L E enc encCompile hu hp he hL hE hb hbA h3 h0 h1 h2,
    fun unpack pl blk blkA L E enc encCompile unL unR tm ea eb f p q c
        hu hp he hL hE hb hbA h3 h0 h1 h2 l0 l1 lf lt r0 r1 rf rt hf hbd =>
      mainBridge unpack pl blk blkA L E enc encCompile unL unR tm ea eb f p q c
        hu hp he hL hE hb hbA h3 h0 h1 h2 l0 l1 lf lt r0 r1 rf rt hf hbd,
    ⟨upv, plv, blkv, blkv, Lv, Ev, encv, ecompv, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun tm u o m m' hm h => bumpTime hm h⟩
  · intro w
    simp [upv]
  · intro k ts
    simp [plv]
  · intro P
    simp [encv]
  · intro l
    simp only [Lv, List.length_map]
    omega
  · intro l
    simp only [Ev, List.length_map]
    omega
  · intro d
    simp [blkv]
  · intro d
    simp [blkv]
  · intro s x anc out nl rest hs
    have hlen : 3 ≤ (upv s).length := by rw [hs]; simp
    show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = _
    rw [if_pos hlen, hs]
    rfl
  · intro s x hs
    show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
    rw [hs]
    simp
  · intro s x a hs
    show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
    rw [hs]
    simp
  · intro s x a b hs
    show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
    rw [hs]
    simp
  · rfl
  · rfl
  · rfl
  · intro hEq
    have h20 : (ecompv [false, false, false] []).length = 20 := rfl
    have h36 : (ecompv [false, false, false] [false]).length = 36 := rfl
    rw [hEq] at h20
    omega
  · refine outBudget upv plv blkv blkv Lv Ev encv ecompv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro w
      simp [upv]
    · intro k ts
      simp [plv]
    · intro P
      simp [encv]
    · intro l
      simp only [Lv, List.length_map]
      omega
    · intro l
      simp only [Ev, List.length_map]
      omega
    · intro d
      simp [blkv]
    · intro d
      simp [blkv]
    · intro s x anc out nl rest hs
      have hlen : 3 ≤ (upv s).length := by rw [hs]; simp
      show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = _
      rw [if_pos hlen, hs]
      rfl
    · intro s x hs
      show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
      rw [hs]
      simp
    · intro s x a hs
      show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
      rw [hs]
      simp
    · intro s x a b hs
      show (if 3 ≤ (upv s).length then bodyv (upv s) x else []) = []
      rw [hs]
      simp

end BQPReferenceValidation.Source18

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate18
    let target ← getConstInfo ``ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate18
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run; axioms {axioms}"
