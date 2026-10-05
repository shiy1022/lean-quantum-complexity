import «AMPUNI-total-function»

set_option autoImplicit false
noncomputable section
namespace ShiTMTotalFunction

/-- General-polynomial version of the total-machine packaging theorem. -/
theorem function_of_total_polynomial (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool) (P : Polynomial ℕ)
    (hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
        (some (ys.map eout.symm)) (P.eval xs.length))) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (xs ys : List Bool) (bound : Nat),
        Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
          (some (ys.map eout.symm)) bound) → g xs = ys := by
  classical
  let g : PvsNP.Str → PvsNP.Str := fun xs => (hall xs).choose
  have hg (xs : List Bool) : Nonempty (Turing.TM2OutputsInTime tm (xs.map ein.symm)
      (some ((g xs).map eout.symm)) (P.eval xs.length)) := (hall xs).choose_spec
  refine ⟨g, ?_, ?_⟩
  · refine ⟨{
      tm := tm
      inputAlphabet := ein
      outputAlphabet := eout
      time := P
      outputsFun := ?_ }⟩
    intro xs
    simpa using Classical.choice (hg xs)
  · intro xs ys bound hy
    have heq := outputs_unique tm (xs.map ein.symm) ((g xs).map eout.symm)
      (ys.map eout.symm) (P.eval xs.length) bound (hg xs) hy
    have h := congrArg (List.map eout) heq
    simpa [List.map_map, Function.comp_def] using h

end ShiTMTotalFunction
