-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance`. The real proof is on prove2.me.
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Finset

namespace ShiBQP

theorem doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance :
    (∀ (S : Type) [DecidableEq S] (G : Type) [AddCommGroup G] [DecidableEq G]
      (Nh : ℕ)
      (Fw : List Bool → S)
      (Bkk : List Bool → List Bool)
      (Pf : List Bool → G)
      (outb : S → Bool)
      (adj : S → List Bool → Bool)
      (Pa : S → List Bool → G)
      (J : S → List Bool → List Bool)
      (val : G → ℕ)
      (ev : List Bool → Option ℕ)
      (d : G),
      -- the evaluator reports the phase through an injection
      Function.Injective val →
      -- BRIDGE-SIMh: one destroyed bit per Hadamard
      (∀ w : List Bool, (Bkk w).length = Nh) →
      -- BRIDGE-SIMn: the reversed run on the reversed destroyed-bit list returns to the start
      (∀ w : List Bool, w.length = Nh → adj (Fw w) (Bkk w).reverse = true) →
      -- BRIDGE-SIMo: the adjoint pass pays the negated phase
      (∀ w : List Bool, w.length = Nh → Pa (Fw w) (Bkk w).reverse + Pf w = 0) →
      -- BRIDGE-SIMh: the reindexing `w ↦ (Fw w, Bkk w)` is injective
      (∀ w1 w2 : List Bool, w1.length = Nh → w2.length = Nh →
          Fw w1 = Fw w2 → Bkk w1 = Bkk w2 → w1 = w2) →
      -- BRIDGE-SIMn at the REVERSED gate list: the reindexing is onto the surviving pass
      (∀ (y : S) (v : List Bool), (J y v).length = Nh) →
      (∀ (y : S) (v : List Bool), v.length = Nh → adj y v = true →
          Fw (J y v) = y ∧ Bkk (J y v) = v.reverse) →
      -- the doubled program on a split witness: it accepts exactly the surviving branches,
      -- and reports the sum of the two passes' phases
      (∀ u v : List Bool, u.length = Nh → v.length = Nh →
          ev (u ++ v)
            = (if outb (Fw u) = true ∧ adj (Fw u) v = true
                then some (val (Pf u + Pa (Fw u) v)) else none)) →
      -- `C d = N d`
      (Finset.univ.filter (fun q : (Fin Nh → Bool) × (Fin Nh → Bool) =>
          outb (Fw (List.ofFn q.1)) = true
            ∧ Fw (List.ofFn q.1) = Fw (List.ofFn q.2)
            ∧ Pf (List.ofFn q.1) - Pf (List.ofFn q.2) = d)).card
        = (Finset.univ.filter (fun b : Fin (Nh + Nh) → Bool =>
            ev (List.ofFn b) = some (val d))).card)
    -- NON-VACUITY: one wire, one Hadamard, `Nh = 1`, `d = 0` -- every hypothesis holds and
    -- BOTH counts are `1`
    ∧ (∃ (Fw : List Bool → Bool) (Bkk : List Bool → List Bool) (Pf : List Bool → ZMod 8)
        (outb : Bool → Bool) (adj : Bool → List Bool → Bool)
        (Pa : Bool → List Bool → ZMod 8) (J : Bool → List Bool → List Bool)
        (ev : List Bool → Option ℕ),
        Function.Injective (ZMod.val : ZMod 8 → ℕ)
        ∧ (∀ w : List Bool, (Bkk w).length = 1)
        ∧ (∀ w : List Bool, w.length = 1 → adj (Fw w) (Bkk w).reverse = true)
        ∧ (∀ w : List Bool, w.length = 1 → Pa (Fw w) (Bkk w).reverse + Pf w = 0)
        ∧ (∀ w1 w2 : List Bool, w1.length = 1 → w2.length = 1 →
            Fw w1 = Fw w2 → Bkk w1 = Bkk w2 → w1 = w2)
        ∧ (∀ (y : Bool) (v : List Bool), (J y v).length = 1)
        ∧ (∀ (y : Bool) (v : List Bool), v.length = 1 → adj y v = true →
            Fw (J y v) = y ∧ Bkk (J y v) = v.reverse)
        ∧ (∀ u v : List Bool, u.length = 1 → v.length = 1 →
            ev (u ++ v)
              = (if outb (Fw u) = true ∧ adj (Fw u) v = true
                  then some (ZMod.val (Pf u + Pa (Fw u) v)) else none))
        ∧ (Finset.univ.filter (fun q : (Fin 1 → Bool) × (Fin 1 → Bool) =>
            outb (Fw (List.ofFn q.1)) = true
              ∧ Fw (List.ofFn q.1) = Fw (List.ofFn q.2)
              ∧ Pf (List.ofFn q.1) - Pf (List.ofFn q.2) = (0 : ZMod 8))).card = 1
        ∧ (Finset.univ.filter (fun b : Fin (1 + 1) → Bool =>
            ev (List.ofFn b) = some (ZMod.val (0 : ZMod 8)))).card = 1) := by
  sorry

end ShiBQP
