-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.acceptance_agreement_for_the_route_a_compiled_program`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_acceptance_agreement_for_the_route_a_compiled_program`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

namespace ShiBQP

theorem acceptance_agreement_for_the_route_a_compiled_program :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (hc : List ℕ → ℕ) (ev : List ℕ → List Bool → Option ℕ)
      (N : ∀ m : ℕ, List (Instr m) → ℕ) (B BA : ∀ m : ℕ, Instr m → List ℕ)
      (D DA : ∀ m : ℕ, List (Instr m) → List ℕ) (L E : List Bool → List ℕ)
      (T : ∀ n m' : ℕ, Bits n → List Bool)
      (Cp : ∀ n m' : ℕ, List (Instr (n + m')) → Bits n → Fin (n + m') → List ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (Phs : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Pf Pa : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → ZMod 8),
      -- CHECK-1f (II): the one-branch evaluator
      (∀ (Q : List ℕ) (bs : List Bool),
          ev Q bs = (match Q.foldl sTr (0, [], [], false, false, false, bs) with
                     | (p, _, _, _, de, bd, w) =>
                         if de || bd || !w.isEmpty then none else some p.val)) →
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- BRIDGE-SIMn: the Hadamard count is reversal-invariant
      (∀ (m : ℕ) (gs : List (Instr m)), N m gs.reverse = N m gs) →
      -- BRIDGE-SIMi/SIMm: the forward phase fold
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pf m [] z w = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pf m (Instr.h i :: gs) z w
            = Phs m (Instr.h i) w.headI z
                + Pf m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) →
          Pf m (g :: gs) z w = Phs m g false z + Pf m gs (fw m g false z) w) →
      -- BRIDGE-SIMo: the adjoint phase fold, at the empty gate list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pa m [] z w = 0) →
      -- BRIDGE-SIMf/SIMh: the forward state, at the empty gate list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z) →
      -- BRIDGE-SIMn: the forward state ignores witness bits past the ones it consumes
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w u : List Bool),
          w.length = N m gs → Fwd m gs z (w ++ u) = Fwd m gs z w) →
      -- BRIDGE-SIMm at the FORWARD blocks
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), N m gs ≤ w.length →
          ∃ ct' : Bool,
            ((gs.map (B m)).flatten).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
              = (p + Pf m gs z w, [], List.ofFn (Fwd m gs z w), ct', de, bd,
                  w.drop (N m gs))) →
      -- BRIDGE-SIMm at the ADJOINT blocks
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), N m gs ≤ w.length →
          ∃ ct' : Bool,
            ((gs.map (BA m)).flatten).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
              = (p + Pa m gs z w, [], List.ofFn (Fwd m gs z w), ct', de, bd,
                  w.drop (N m gs))) →
      -- BRIDGE-SIMk: the output-wire test block, on basis strings
      (∀ (m : ℕ) (out : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          (List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0)).foldl sTr
              (p, [], List.ofFn z, ct, de, bd, w)
            = (p, [], List.ofFn z, ct, de || !(z out), bd, w)) →
      -- BRIDGE-Dd: INPUT LOADING
      (∀ (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          (L l ++ List.replicate l.length 0).foldl sTr (p, [], [], ct, de, bd, w)
            = (p, [], l, ct, de, bd, w)) →
      -- BRIDGE-Dd: THE ENDPOINT TEST
      (∀ (l e : List Bool), l.length = e.length →
          ∀ (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
            (E l ++ List.replicate l.length 0).foldl sTr (p, [], e, ct, de, bd, w)
              = (p, [], e, ct, de || decide (e ≠ l), bd, w)) →
      -- BRIDGE-C2c: the gate list, forward and reversed
      (∀ m : ℕ, D m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), D m (g :: gs) = B m g ++ D m gs) →
      (∀ m : ℕ, DA m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
          DA m (g :: gs) = DA m gs ++ BA m g) →
      -- BRIDGE-C2c: the padded input tape
      (∀ (n m' : ℕ) (x : Bits n), T n m' x
          = List.ofFn (fun k : Fin (n + m') =>
              if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false)) →
      -- BRIDGE-C2c: the whole route-(A) program
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
          Cp n m' gs x out
            = L (T n m' x) ++ (List.replicate (n + m') 0 ++ (D (n + m') gs
                ++ ((List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0))
                  ++ (DA (n + m') gs
                    ++ (E (T n m' x) ++ List.replicate (n + m') 0)))))) →
      -- BRIDGE-C2c (1): the DOUBLED witness budget
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
          hc (Cp n m' gs x out) = N (n + m') gs + N (n + m') gs) →
      -- BRIDGE-C2c (3): every emitted opcode is legal and non-aborting
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (c : ℕ), c ∈ Cp n m' gs x out → c ≤ 8) →
      -- BRIDGE-SIMe: the tape of a basis string
      (∀ (m : ℕ) (z : Bits m), (List.ofFn z).length = m) →
      -- BRIDGE-Ad (d): every witness of the wrong length is rejected
      (∀ (P : List ℕ) (w : List Bool), (∀ c ∈ P, c % 16 ≤ 9) →
          w.length ≠ hc P → ev P w = none) →
      -- (6) ACCEPTANCE AGREEMENT: on a correctly budgeted witness, split one half per
      -- pass, `ev` fails EXACTLY on the branches the output-wire test or the endpoint
      -- test rejects
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (z : Bits (n + m')),
          (∀ k : Fin (n + m'), z k = if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) →
          ∀ w1 w2 : List Bool, w1.length = N (n + m') gs →
            w2.length = N (n + m') gs →
              (ev (Cp n m' gs x out) (w1 ++ w2) = none
                ↔ ¬(Fwd (n + m') gs z w1 out = true
                      ∧ Fwd (n + m') gs.reverse (Fwd (n + m') gs z w1) w2 = z)))
      -- (5') and on a surviving branch it returns the CONSTRUCTIVE `ZMod 8` fold: the
      -- forward phase of the first pass plus the adjoint phase of the second
      ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (z : Bits (n + m')),
          (∀ k : Fin (n + m'), z k = if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) →
          ∀ w1 w2 : List Bool, w1.length = N (n + m') gs →
            w2.length = N (n + m') gs →
              Fwd (n + m') gs z w1 out = true →
                Fwd (n + m') gs.reverse (Fwd (n + m') gs z w1) w2 = z →
                  ev (Cp n m' gs x out) (w1 ++ w2)
                    = some ((Pf (n + m') gs z w1
                        + Pa (n + m') gs.reverse (Fwd (n + m') gs z w1) w2).val))
      -- (7) every witness of the wrong length is rejected, at the DOUBLED budget
      ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (w : List Bool), w.length ≠ N (n + m') gs + N (n + m') gs →
            ev (Cp n m' gs x out) w = none)
      -- NON-VACUITY: the accepting branch is inhabited -- one wire, the empty circuit,
      -- classical input `1`, output wire `0`, empty witness, phase `0`
      ∧ ev (Cp 1 0 [] (fun _ => true) ⟨0, by omega⟩) [] = some 0 := by
  sorry

end ShiBQP
