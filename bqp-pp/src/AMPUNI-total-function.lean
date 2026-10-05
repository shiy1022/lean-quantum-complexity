import Definitions.Def_PvsNP
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
noncomputable section
namespace ShiTMTotalFunction

private theorem iterate_none {A : Type} (f : A → Option A) (n : Nat) :
    (fun c : Option A => c.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

private theorem halted_eq_of_le {A : Type} (f : A → Option A) (c a b : A)
    (s t : Nat) (hs : s ≤ t) (ha : f a = none)
    (hra : (fun z : Option A => z.bind f)^[s] (some c) = some a)
    (hrb : (fun z : Option A => z.bind f)^[t] (some c) = some b) : a = b := by
  obtain ⟨d, hd⟩ : ∃ d, t = d+s := ⟨t-s, by omega⟩
  rw [hd, Function.iterate_add_apply, hra] at hrb
  cases d with
  | zero => exact Option.some.inj hrb
  | succ d =>
      rw [Function.iterate_succ_apply] at hrb
      simp only [Option.bind_some, ha, iterate_none] at hrb
      cases hrb

theorem halted_unique {A : Type} (f : A → Option A) (c a b : A)
    (s t : Nat) (ha : f a = none) (hb : f b = none)
    (hra : (fun z : Option A => z.bind f)^[s] (some c) = some a)
    (hrb : (fun z : Option A => z.bind f)^[t] (some c) = some b) : a = b := by
  rcases le_total s t with h | h
  · exact halted_eq_of_le f c a b s t h ha hra hrb
  · exact (halted_eq_of_le f c b a t s h hb hrb hra).symm

theorem outputs_unique (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₀))
    (ys zs : List (tm.Γ tm.k₁)) (a b : Nat)
    (hy : Nonempty (Turing.TM2OutputsInTime tm xs (some ys) a))
    (hz : Nonempty (Turing.TM2OutputsInTime tm xs (some zs) b)) : ys = zs := by
  obtain ⟨⟨⟨s, hs⟩, _⟩⟩ := hy
  obtain ⟨⟨⟨t, ht⟩, _⟩⟩ := hz
  have h := halted_unique tm.step (Turing.initList tm xs)
    (Turing.haltList tm ys) (Turing.haltList tm zs) s t rfl rfl hs ht
  have h' := congrArg (fun c : tm.Cfg => c.stk tm.k₁) h
  simpa [Turing.haltList] using h'

/-- A uniformly polynomial total machine defines a polynomial-time function;
uniqueness identifies that function with every separately verified output. -/
theorem function_of_total (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool) (C : Nat)
    (hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
        (some (ys.map eout.symm)) (C*(xs.length+1)^2))) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (xs ys : List Bool) (bound : Nat),
        Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
          (some (ys.map eout.symm)) bound) → g xs = ys := by
  classical
  let g : PvsNP.Str → PvsNP.Str := fun xs => (hall xs).choose
  have hg (xs : List Bool) : Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
      (some ((g xs).map eout.symm)) (C*(xs.length+1)^2)) := (hall xs).choose_spec
  refine ⟨g, ?_, ?_⟩
  · refine ⟨{
      tm := tm
      inputAlphabet := ein
      outputAlphabet := eout
      time := Polynomial.C C * (Polynomial.X + Polynomial.C 1)^2
      outputsFun := ?_ }⟩
    intro xs
    simpa using Classical.choice (hg xs)
  · intro xs ys bound hy
    have heq := outputs_unique tm (xs.map ein.symm) ((g xs).map eout.symm)
      (ys.map eout.symm) (C*(xs.length+1)^2) bound (hg xs) hy
    have h := congrArg (List.map eout) heq
    simpa [List.map_map, Function.comp_def] using h

end ShiTMTotalFunction
