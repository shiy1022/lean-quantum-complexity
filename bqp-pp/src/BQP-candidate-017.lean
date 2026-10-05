import Definitions.Def_PvsNP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_polyTimeComputable_bridge_for_generic_pairing_decoders
import Theorems.Thm_ShiTM_polyTimeComputable_of_machine_polybound

namespace BQPReferenceValidation.Source17
/-
PAIRDECc.  THE `PolyTimeComputable` BRIDGE FOR THE PAIRED COMPILER, ∀-GENERIC IN THE DECODERS.

WHAT THIS REPAIRS.  `COMPMACHe` (15) is the campaign's `PolyTimeComputable` reduction, but its
`unL`/`unR` are EXISTENTIALLY BOUND IN THE SAME `∃` as (15) and are pinned only on the image of
`pair` (conjuncts (2)-(3)), at six literal strings ((5)-(12)) and by a length budget ((13)).
On a string such as `[false, true, true, false, false, true]` -- tag order f,t,f, NOT in the
image of `pair` -- their values are unconstrained, while (15)'s machine hypothesis quantifies
over EVERY `w : List Bool`.  So (15) cannot be instantiated at any concrete machine.
NOTHING HERE CONSUMES `COMPMACHe` (15).  The bridge is restated ∀-QUANTIFIED IN THE DECODERS
under explicit hypotheses -- `COMPMACHf` (9)'s pattern -- and routed directly through the
published `ShiTM.polyTimeComputable_of_machine_polybound`, which is existential-free.

THE CONTENT.  (1) is the bridge at an ARBITRARY output constant `K`: for ANY pair of decoders
obeying only the global budget `|unL w| + |unR w| ≤ |w|` on every string, any machine whose step
count is affine in (input length + output length) -- the only form a stack-machine emitter bound
ever takes, since every emitted symbol costs a step -- computes `fun w => gc (unL w) (unR w)` in
polynomial time, with the degree-one polynomial `(K+1)*c*X + (K+1)*c`.  (2) is (1) at
`COMPILE-STRd`'s constant `K = 56`, giving `57*c*X + 57*c`.  (3) takes the DEFINING EQUATIONS of
the length-2 tagged decoders as hypotheses instead of the budget and derives the budget itself,
so a consumer holding a concrete decoder discharges eight `rfl`s and gets `PolyTimeComputable`
with no side conditions about well-formed inputs at all (gotcha 223: `PolyTimeComputable`
quantifies over ALL strings, garbage included).  (5) exhibits decoders satisfying those
equations, so (3) is not vacuous.

NOT CLAIMED: the compiler machine.  `gc` is arbitrary throughout, as in `COMPMACHe` (15).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

private def uL : List Bool → List Bool
  | [] => []
  | [_] => []
  | false :: b :: t => b :: uL t
  | true :: _ :: _ => []

private def uR : List Bool → List Bool
  | [] => []
  | [_] => []
  | false :: _ :: t => uR t
  | true :: b :: t => b :: uR t

private lemma budget (f g : List Bool → List Bool)
    (hf0 : f [] = []) (hf1 : ∀ b : Bool, f [b] = [])
    (hfF : ∀ (b : Bool) (t : List Bool), f (false :: b :: t) = b :: f t)
    (hfT : ∀ (a : Bool) (t : List Bool), f (true :: a :: t) = [])
    (hg0 : g [] = []) (hg1 : ∀ b : Bool, g [b] = [])
    (hgF : ∀ (a : Bool) (t : List Bool), g (false :: a :: t) = g t)
    (hgT : ∀ (b : Bool) (t : List Bool), g (true :: b :: t) = b :: g t) :
    ∀ w : List Bool, (f w).length + (g w).length ≤ w.length := by
  have key : ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
      (f w).length + (g w).length ≤ w.length := by
    intro n
    induction n with
    | zero =>
        intro w hw
        rcases w with _ | ⟨a, t⟩
        · rw [hf0, hg0]
          simp
        · simp only [List.length_cons] at hw
          omega
    | succ n ih =>
        intro w hw
        rcases w with _ | ⟨a, _ | ⟨b, t⟩⟩
        · rw [hf0, hg0]
          simp
        · rw [hf1, hg1]
          simp
        · have ht : t.length ≤ n := by
            simp only [List.length_cons] at hw
            omega
          have hrec := ih t ht
          cases a
          · rw [hfF, hgF]
            simp only [List.length_cons]
            omega
          · rw [hfT, hgT]
            simp only [List.length_nil, List.length_cons]
            omega
  intro w
  exact key w.length w (Nat.le_refl w.length)

private def outMono (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) {m m' : ℕ} (hm : m ≤ m')
    (h : Turing.TM2OutputsInTime tm l l' m) : Turing.TM2OutputsInTime tm l l' m' := by
  obtain ⟨he, hle⟩ := h
  exact ⟨he, le_trans hle hm⟩

private lemma bridgeK (unL unR : List Bool → List Bool)
    (gc : List Bool → List Bool → List Bool) (tm : Turing.FinTM2)
    (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (K c : ℕ)
    (hbud : ∀ w : List Bool, (unL w).length + (unR w).length ≤ w.length)
    (hlen : ∀ s x : List Bool, (gc s x).length ≤ K * (s.length + x.length + 1))
    (hrun : ∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun w)
      (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
      (c * (w.length + (gc (unL w) (unR w)).length) + c))) :
    PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)) := by
  refine ShiTM.polyTimeComputable_of_machine_polybound tm ea eb
    (fun w => gc (unL w) (unR w))
    (Polynomial.C ((K + 1) * c) * Polynomial.X + Polynomial.C ((K + 1) * c)) ?_
  intro s
  obtain ⟨h⟩ := hrun s
  have heval : (Polynomial.C ((K + 1) * c) * Polynomial.X
      + Polynomial.C ((K + 1) * c)).eval s.length
      = (K + 1) * c * s.length + (K + 1) * c := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h1 : (gc (unL s) (unR s)).length
      ≤ K * ((unL s).length + (unR s).length + 1) := hlen (unL s) (unR s)
  have h2 : (unL s).length + (unR s).length ≤ s.length := hbud s
  have h3 : K * ((unL s).length + (unR s).length + 1) ≤ K * (s.length + 1) :=
    Nat.mul_le_mul (le_refl K) (by omega)
  have h5 : K * (s.length + 1) = K * s.length + K := by ring
  have h4 : (gc (unL s) (unR s)).length ≤ K * s.length + K := by omega
  have hsum : s.length + (gc (unL s) (unR s)).length
      ≤ s.length + (K * s.length + K) := by omega
  have hstep : c * (s.length + (gc (unL s) (unR s)).length)
      ≤ c * (s.length + (K * s.length + K)) := Nat.mul_le_mul (le_refl c) hsum
  have heq : c * (s.length + (K * s.length + K))
      = (K + 1) * c * s.length + K * c := by ring
  rw [heq] at hstep
  have h6 : (K + 1) * c * s.length + K * c + c
      = (K + 1) * c * s.length + (K + 1) * c := by ring
  have h7 : c * (s.length + (gc (unL s) (unR s)).length) + c
      ≤ (K + 1) * c * s.length + (K + 1) * c :=
    le_trans (Nat.add_le_add_right hstep c) (le_of_eq h6)
  refine Nonempty.intro (outMono tm _ _ ?_ h)
  rw [heval]
  exact h7

theorem _root_.BQPReferenceValidation.candidate17 :
    -- (1) THE BRIDGE, ∀-QUANTIFIED IN THE DECODERS and in the output constant `K`.  The ONLY
    -- property of the decoders it uses is the global budget on EVERY string; they are not
    -- required to invert anything.  This is the conjunct `COMPMACHe` (15) should have been.
    (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (K c : ℕ),
      (∀ w : List Bool, (unL w).length + (unR w).length ≤ w.length) →
      (∀ s x : List Bool, (gc s x).length ≤ K * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (2) the same at `COMPILE-STRd` (7)'s output constant 56
    ∧ (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (c : ℕ),
      (∀ w : List Bool, (unL w).length + (unR w).length ≤ w.length) →
      (∀ s x : List Bool, (gc s x).length ≤ 56 * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (3) THE BRIDGE FROM THE DEFINING EQUATIONS OF THE LENGTH-2 TAGGED DECODERS ALONE: the
    -- global budget is DERIVED, not assumed, so a consumer holding concrete decoders discharges
    -- eight `rfl`s and needs no hypothesis about well-formed inputs.
    ∧ (∀ (unL unR : List Bool → List Bool) (gc : List Bool → List Bool → List Bool)
        (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) (c : ℕ),
      unL [] = [] → (∀ b : Bool, unL [b] = []) →
      (∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t) →
      (∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = []) →
      unR [] = [] → (∀ b : Bool, unR [b] = []) →
      (∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t) →
      (∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t) →
      (∀ s x : List Bool, (gc s x).length ≤ 56 * (s.length + x.length + 1)) →
      (∀ w : List Bool, Nonempty (Turing.TM2OutputsInTime tm
        (List.map ea.invFun w)
        (Option.some (List.map eb.invFun (gc (unL w) (unR w))))
        (c * (w.length + (gc (unL w) (unR w)).length) + c))) →
      PvsNP.PolyTimeComputable (fun w => gc (unL w) (unR w)))
    -- (4) the degree-one polynomials the bridge uses, named
    ∧ (∀ c : ℕ, ∃ p : Polynomial ℕ, ∀ n : ℕ, p.eval n = 57 * c * n + 57 * c)
    ∧ (∀ K c : ℕ, ∃ p : Polynomial ℕ,
        ∀ n : ℕ, p.eval n = (K + 1) * c * n + (K + 1) * c)
    -- (5) NON-VACUITY: decoders satisfying (3)'s eight equations exist, and the equations
    -- specify them on EVERY string -- including one outside the image of the pairing, where
    -- `COMPMACHe`'s existentially bound decoders are unconstrained.
    ∧ (∃ unL unR : List Bool → List Bool,
        (unL [] = []
          ∧ (∀ b : Bool, unL [b] = [])
          ∧ (∀ (b : Bool) (t : List Bool), unL (false :: b :: t) = b :: unL t)
          ∧ (∀ (a : Bool) (t : List Bool), unL (true :: a :: t) = []))
      ∧ (unR [] = []
          ∧ (∀ b : Bool, unR [b] = [])
          ∧ (∀ (a : Bool) (t : List Bool), unR (false :: a :: t) = unR t)
          ∧ (∀ (b : Bool) (t : List Bool), unR (true :: b :: t) = b :: unR t))
      ∧ unL [false, true, true, false, false, true] = [true]
      ∧ unR [false, true, true, false, false, true] = [false]) := by
  refine ⟨bridgeK, ?_, ?_, ?_, ?_, ?_⟩
  · intro unL unR gc tm ea eb c hbud hlen hrun
    exact bridgeK unL unR gc tm ea eb 56 c hbud hlen hrun
  · intro unL unR gc tm ea eb c hf0 hf1 hfF hfT hg0 hg1 hgF hgT hlen hrun
    exact bridgeK unL unR gc tm ea eb 56 c
      (budget unL unR hf0 hf1 hfF hfT hg0 hg1 hgF hgT) hlen hrun
  · intro c
    refine ⟨Polynomial.C (57 * c) * Polynomial.X + Polynomial.C (57 * c), fun n => ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  · intro K c
    refine ⟨Polynomial.C ((K + 1) * c) * Polynomial.X + Polynomial.C ((K + 1) * c),
      fun n => ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  · exact ⟨uL, uR,
      ⟨by simp [uL], fun b => by cases b <;> simp [uL], fun b t => by simp [uL],
        fun a t => by simp [uL]⟩,
      ⟨by simp [uR], fun b => by cases b <;> simp [uR], fun a t => by simp [uR],
        fun b t => by simp [uR]⟩,
      by simp [uL], by simp [uR]⟩

end BQPReferenceValidation.Source17

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate17
    let target ← getConstInfo ``ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate17
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders; axioms {axioms}"
