-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.stack_supplied_index_emitter_block`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_stack_supplied_index_emitter_block`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2

theorem stack_supplied_index_emitter_block :
    (∀ {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
      (M : Lam → Stmt Gam Lam sig) {kidx kout ktag : K},
      kidx ≠ kout → kidx ≠ ktag → kout ≠ ktag →
      ∀ {ldisp la0 la1 : Lam} {lm : Nat → Lam}
        {fpopTag : sig → Option (Gam ktag) → sig} {flab : sig → Lam}
        {fpush0 fmark : sig → Gam kout}
        {fpopI : sig → Option (Gam kidx) → sig} {gtestI : sig → Bool}
        {hpushI : sig → Gam kout} {fredel : sig → Gam kidx} {eI : Gam kidx → Gam kout}
        (mI dI : Gam kidx) (tout fout : Gam kout) (bout : Bool → Gam kout)
        (ib t : Nat) (ridx : List (Gam kidx))
        (tau : Gam ktag) (rtag : List (Gam ktag)) (v : sig) (S : ∀ k, List (Gam k)),
      bout true = tout → bout false = fout →
      M ldisp = Stmt.pop ktag fpopTag (Stmt.goto flab) →
      M la0 = Stmt.push kout fpush0 (Stmt.goto (fun _ => la1)) →
      M la1 = Stmt.pop kidx fpopI (Stmt.branch gtestI
          (Stmt.push kout hpushI (Stmt.goto (fun _ => la1)))
          (Stmt.push kidx fredel
            (Stmt.push kout fpush0 (Stmt.goto (fun _ => lm 0))))) →
      (∀ q : Nat, q < t → M (lm q)
          = Stmt.push kout fmark (Stmt.goto (fun _ => lm (q + 1)))) →
      (∀ w : sig, fpush0 w = fout) →
      (∀ w : sig, fmark w = tout) →
      (∀ w : sig, fredel w = dI) →
      (∀ (w : sig) (y : Gam kidx), hpushI (fpopI w (some y)) = eI y) →
      (∀ w : sig, gtestI (fpopI w (some mI)) = true) →
      (∀ w : sig, gtestI (fpopI w (some dI)) = false) →
      eI mI = tout →
      flab (fpopTag v (some tau)) = la0 →
      S ktag = tau :: rtag →
      S kidx = List.replicate ib mI ++ dI :: ridx →
      ∃ (w : sig) (T : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[ib + t + 3]
            (some { l := some ldisp, var := v, stk := S })
          = some { l := some (lm t), var := w, stk := T }
        ∧ T kout = (ShiBQP.encNat t ++ ShiBQP.encNat ib).map bout ++ S kout
        ∧ T kidx = dI :: ridx
        ∧ T ktag = rtag
        ∧ (∀ k, k ≠ ktag → k ≠ kidx → k ≠ kout → T k = S k)
        ∧ (∀ P : (∀ k, List (Gam k)) → Prop,
            (∀ A B : (∀ k, List (Gam k)),
              (∀ k, k ≠ ktag → k ≠ kidx → k ≠ kout → A k = B k) → P A → P B) →
            P S → P T)
        ∧ Nonempty (StateTransition.EvalsToInTime (step M)
            { l := some ldisp, var := v, stk := S }
            (some { l := some (lm t), var := w, stk := T }) (ib + t + 3)))
    ∧ (∀ (wv : Nat) (i : Fin wv),
        ShiBQP.encInstr (ShiShallow.Instr.h i)
            = ShiBQP.encNat 0 ++ ShiBQP.encNat (i : Nat)
        ∧ ShiBQP.encInstr (ShiShallow.Instr.s i)
            = ShiBQP.encNat 1 ++ ShiBQP.encNat (i : Nat)
        ∧ ShiBQP.encInstr (ShiShallow.Instr.t i)
            = ShiBQP.encNat 2 ++ ShiBQP.encNat (i : Nat)
        ∧ ShiBQP.encInstr (ShiShallow.Instr.x i)
            = ShiBQP.encNat 3 ++ ShiBQP.encNat (i : Nat))
    ∧ (∃ (A B : Fin 2 → List Bool) (L : List Bool),
        L ≠ [] ∧ A 0 = L ∧ (B 0).length ≤ (A 0).length ∧ B 1 = A 1 ∧ B 0 ≠ L)
    ∧ (∃ (Gm : Fin 3 → Type) (Lm sg : Type)
        (M : Lm → Stmt Gm Lm sg) (kt kx ko : Fin 3)
        (ld : Lm) (lmk : Nat → Lm)
        (fp : sg → Option (Gm kt) → sg) (fl : sg → Lm) (ta tb : Gm kt)
        (mk dl : Gm kx) (bo : Bool → Gm ko) (v0 : sg)
        (S : Nat → ∀ k, List (Gm k))
        (T1 T2 T3 : ∀ k, List (Gm k)) (w1 w2 w3 : sg),
        ([kt, kx, ko] : List (Fin 3)).Nodup
        ∧ mk ≠ dl
        ∧ ta ≠ tb
        ∧ bo true ≠ bo false
        ∧ M ld = Stmt.pop kt fp (Stmt.goto fl)
        ∧ fl (fp v0 (some ta)) ≠ fl (fp v0 (some tb))
        ∧ lmk 0 ≠ lmk 4
        ∧ (∀ ib : Nat, S ib kt = [ta] ∧ S ib kx = List.replicate ib mk ++ [dl]
            ∧ S ib ko = [])
        ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step M))^[11]
            (some { l := some ld, var := v0, stk := S 8 })
          = some { l := some (lmk 0), var := w1, stk := T1 }
        ∧ T1 ko = (ShiBQP.encNat 0 ++ ShiBQP.encNat 8).map bo
        ∧ T1 kx = [dl]
        ∧ T1 kt = []
        ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step M))^[11]
            (some { l := some ld, var := v0, stk := S 4 })
          = some { l := some (lmk 4), var := w2, stk := T2 }
        ∧ T2 ko = (ShiBQP.encNat 4 ++ ShiBQP.encNat 4).map bo
        ∧ T2 kx = [dl]
        ∧ T2 kt = []
        ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step M))^[5]
            (some { l := some ld, var := v0, stk := S 0 })
          = some { l := some (lmk 2), var := w3, stk := T3 }
        ∧ T3 ko = (ShiBQP.encNat 2 ++ ShiBQP.encNat 0).map bo
        ∧ T3 kx = [dl]
        ∧ T3 kt = []) := by
  sorry

end ShiTM
