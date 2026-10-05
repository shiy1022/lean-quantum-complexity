import «BQP-gate-dispatch»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPGateDispatch
open Turing Turing.TM2

private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (h : f^[a] x = y) (h' : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

theorem tagged_one_run (adj : Bool) (t : Fin 4) (n : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[t.val+3*n+4]
      (some (cfg (.tag 0) v
        (List.replicate t.val true ++ false::(List.replicate n true ++ false::s)) out)) =
    some (⟨none,false,inputStacks s
      (BQPOpcodeEmission.encode (List.replicate n 1 ++ (body adj t ++ List.replicate n 0)) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  let t' : Fin 5 := ⟨t.val,by omega⟩
  have ht := tag_run adj t' v (List.replicate n true ++ false::s) out
  have he : entry t' = .one t none := by simp [entry,t',t.isLt]
  rw [he] at ht
  have hb := one_run adj t n false s out
  have hall := chain _ _ _ _ _ _ ht hb
  rw [show t'.val+1+(3*n+3) = t.val+3*n+4 by dsimp [t']; omega] at hall
  exact hall

theorem tagged_two_run (adj : Bool) (i j : ℕ) (hne : i ≠ j) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[i+j+min i j+2*max i j+13]
      (some (cfg (.tag 0) v
        (List.replicate 4 true ++ false::(List.replicate i true ++ false::
          (List.replicate j true ++ false::s))) out)) =
    some (⟨none,false,inputStacks s
      (BQPOpcodeEmission.encode (BQPCnot.rendered i j) ++ out)⟩ : Cfg Gam Label Bool) := by
  have ht := tag_run adj (4 : Fin 5) v
    (List.replicate i true ++ false::(List.replicate j true ++ false::s)) out
  have he : entry (4 : Fin 5) = .two .left := by simp [entry]
  rw [he] at ht
  have hb := two_run adj i j hne false s out
  have hall := chain _ _ _ _ _ _ ht hb
  rw [show (4 : Fin 5).val+1+(i+j+min i j+2*max i j+8) =
    i+j+min i j+2*max i j+13 by norm_num; omega] at hall
  exact hall

end BQPGateDispatch
