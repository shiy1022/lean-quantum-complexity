import «BQP-counted-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCounted
open Turing Turing.TM2
variable {K L A : Type} [DecidableEq K]

theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (h : f^[a] x = y) (h' : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

/-- Counted sequencing of concrete bodies. The body premise is a usual
subroutine specification; the instruction and layer instances discharge it. -/
theorem repeat_run (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (layout : List Bool → List Bool → K → List Bool)
    (enc emit : A → List Bool) (cost : A → ℕ)
    (hbody : ∀ a s out,
      (ShiTMSubroutine.run M)^[cost a] (some ⟨some main,true,layout (enc a ++ s) out⟩) =
      some ⟨none,false,layout s (emit a ++ out)⟩)
    (xs : List A) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program input M main))^[(xs.map cost).sum+xs.length+1]
      (some (cfg (some none) v (layout ((xs.map enc).flatten ++ s) out)
        (List.replicate xs.length true))) =
    some (⟨none,false,extend (layout s ((xs.reverse.map emit).flatten ++ out)) []⟩ :
      Cfg (Gam K) (Label L) Bool) := by
  induction xs generalizing v out with
  | nil => simpa using driver_end input M main v (layout s out)
  | cons a xs ih =>
      have hdriver := driver_cons input M main v true
        (layout (enc a ++ ((xs.map enc).flatten ++ s)) out) (List.replicate xs.length true)
      have hcall := delegate input M main (cost a) true false
        (layout (enc a ++ ((xs.map enc).flatten ++ s)) out)
        (layout ((xs.map enc).flatten ++ s) (emit a ++ out)) (List.replicate xs.length true)
        (hbody a ((xs.map enc).flatten ++ s) out)
      have hrest := ih false (emit a ++ out)
      have hfirst := chain (ShiTMSubroutine.run (program input M main)) _ _ _ 1 (cost a) (by simpa only [Function.iterate_one] using hdriver) hcall
      have hall := chain _ _ _ _ _ _ hfirst hrest
      rw [show 1+cost a+((xs.map cost).sum+xs.length+1) =
        ((a::xs).map cost).sum+(a::xs).length+1 by
          simp only [List.map_cons, List.sum_cons, List.length_cons]; omega] at hall
      simpa only [List.length_cons, List.replicate_succ, List.map_cons, List.flatten_cons,
        List.reverse_cons, List.map_append, List.map_nil, List.flatten_append,
        List.flatten_nil, List.append_nil, List.append_assoc] using hall

/-- Read the actual unary list length before sequencing the bodies. -/
theorem counted_run (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (layout : List Bool → List Bool → K → List Bool)
    (hupdate : ∀ s out t, Function.update (layout s out) input t = layout t out)
    (enc emit : A → List Bool) (cost : A → ℕ)
    (hbody : ∀ a s out,
      (ShiTMSubroutine.run M)^[cost a] (some ⟨some main,true,layout (enc a ++ s) out⟩) =
      some ⟨none,false,layout s (emit a ++ out)⟩)
    (xs : List A) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program input M main))^[(xs.map cost).sum+2*xs.length+2]
      (some (cfg none v (layout
        (List.replicate xs.length true ++ false::((xs.map enc).flatten ++ s)) out) [])) =
    some (⟨none,false,extend (layout s ((xs.reverse.map emit).flatten ++ out)) []⟩ :
      Cfg (Gam K) (Label L) Bool) := by
  have hh := header_run input M main xs.length v (layout [] out) ((xs.map enc).flatten ++ s) []
  simp only [hupdate, List.append_nil] at hh
  have hr := repeat_run input M main layout enc emit cost hbody xs false s out
  have hall := chain _ _ _ _ _ _ hh hr
  rw [show xs.length+1+((xs.map cost).sum+xs.length+1) =
    (xs.map cost).sum+2*xs.length+2 by omega] at hall
  exact hall

end BQPCounted
