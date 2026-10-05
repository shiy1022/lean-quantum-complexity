import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_encNat_parser_block
import Theorems.Thm_ShiTM_unary_count_to_dispatch_symbol

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMInstructionFront

theorem parse_tag_to_dispatch {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {kin kmark ktag : K}
    (dIM : kin ≠ kmark) (dMT : kmark ≠ ktag) (dIT : kin ≠ ktag)
    {lb ldisp : Lam} {lcnt : ℕ → Lam}
    {fpopI : sig → Option (Gam kin) → sig} {gtestI : sig → Bool}
    {hpushM : sig → Gam kmark} {eIM : Gam kin → Gam kmark}
    {fpopM : sig → Option (Gam kmark) → sig} {gmark : sig → Bool}
    (mk : Gam kmark) (bin : Bool → Gam kin) (tagOf : ℕ → Gam ktag) (NB : ℕ)
    (hMlb : M lb = Turing.TM2.Stmt.pop kin fpopI
            (Turing.TM2.Stmt.branch gtestI
              (Turing.TM2.Stmt.push kmark hpushM (Turing.TM2.Stmt.goto (fun _ => lb)))
              (Turing.TM2.Stmt.goto (fun _ => lcnt 0))))
    (hvalM : ∀ (w : sig) (y : Gam kin), hpushM (fpopI w (some y)) = eIM y)
    (honeI : ∀ w : sig, gtestI (fpopI w (some (bin true))) = true)
    (hzeroI : ∀ w : sig, gtestI (fpopI w (some (bin false))) = false)
    (hemk : eIM (bin true) = mk)
    (hMcnt : ∀ i : ℕ, i < NB → M (lcnt i) = Turing.TM2.Stmt.pop kmark fpopM
            (Turing.TM2.Stmt.branch gmark
              (Turing.TM2.Stmt.goto (fun _ => lcnt (i + 1)))
              (Turing.TM2.Stmt.push ktag (fun _ => tagOf i)
                (Turing.TM2.Stmt.goto (fun _ => ldisp)))))
    (hmarkM : ∀ w : sig, gmark (fpopM w (some mk)) = true)
    (hstopM : ∀ w : sig, gmark (fpopM w none) = false)
    (c : ℕ) (hc : c < NB) (z : List Bool) (rest : List (Gam kin)) (u : sig)
    (S' : ∀ k, List (Gam k))
    (hSin : S' kin = List.map bin (ShiBQP.encNat c ++ z) ++ rest)
    (hSm : S' kmark = []) :
    ∃ (v2 : sig) (S2 : ∀ k, List (Gam k)),
      (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
          cf.bind (Turing.TM2.step M))^[c + 1 + (c + 1)]
          (some { l := some lb, var := u, stk := S' })
        = some { l := some ldisp, var := v2, stk := S2 }
      ∧ S2 kin = List.map bin z ++ rest
      ∧ S2 ktag = tagOf c :: S' ktag
      ∧ S2 kmark = []
      ∧ (∀ j, j ≠ kin → j ≠ kmark → j ≠ ktag → S2 j = S' j) := by
  have hpre : S' kin = List.map bin (ShiBQP.encNat c) ++ (List.map bin z ++ rest) := by
    rw [hSin, List.map_append, List.append_assoc]
  obtain ⟨v1, S1, hA1, hS1i, hS1m, hS1f⟩ :
      ∃ (v1 : sig) (S1 : ∀ k, List (Gam k)),
        (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[c + 1]
            (some { l := some lb, var := u, stk := S' })
          = some { l := some (lcnt 0), var := v1, stk := S1 }
        ∧ S1 kin = List.map bin z ++ rest
        ∧ S1 kmark = List.replicate c mk ++ ([] : List (Gam kmark))
        ∧ (∀ j, j ≠ kin → j ≠ kmark → S1 j = S' j) := by
    refine ⟨_, _, (ShiTM.encNat_parser_block M dIM bin hMlb hvalM honeI hzeroI c
      (List.map bin z ++ rest) u S' hpre).1, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne dIM, Function.update_self]
    · rw [Function.update_self, hemk, hSm]
    · intro j hji hjm
      rw [Function.update_of_ne hjm, Function.update_of_ne hji]
  obtain ⟨v2, S2, hA2, hS2i, hS2t, hS2m, hS2f⟩ :
      ∃ (v2 : sig) (S2 : ∀ k, List (Gam k)),
        (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[c + 1]
            (some { l := some (lcnt 0), var := v1, stk := S1 })
          = some { l := some ldisp, var := v2, stk := S2 }
        ∧ S2 kin = List.map bin z ++ rest
        ∧ S2 ktag = tagOf c :: S' ktag
        ∧ S2 kmark = []
        ∧ (∀ j, j ≠ kin → j ≠ kmark → j ≠ ktag → S2 j = S' j) := by
    refine ⟨_, _, (ShiTM.unary_count_to_dispatch_symbol M dMT NB lcnt ldisp tagOf hMcnt mk
      hmarkM [] hstopM c hc v1 S1 hS1m).1, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne dIT, Function.update_of_ne dIM, hS1i]
    · rw [Function.update_self, hS1f ktag (Ne.symm dIT) (Ne.symm dMT)]
    · rw [Function.update_of_ne dMT, Function.update_self]
      all_goals rfl
    · intro j hji hjm hjt
      rw [Function.update_of_ne hjt, Function.update_of_ne hjm, hS1f j hji hjm]
  refine ⟨v2, S2, ?_, hS2i, hS2t, hS2m, hS2f⟩
  rw [Function.iterate_add_apply _ (c + 1) (c + 1), hA1, hA2]

/-! ### ARM B -- a one-index gate, TWO output fields (EMITX-1 at `kidx := kin`) -/


end ShiTMInstructionFront

