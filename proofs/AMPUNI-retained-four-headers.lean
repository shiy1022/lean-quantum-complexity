import «AMPUNI-retained-header-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMRetainedTop

open ShiTMLayoutMachine ShiTMOuterLift

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The new entry phase consumes all four retained unary fields and hands the untouched
circuit suffix to the existing nested circuit parser. Each field count remains available
on its own stack for the later piece-table initializer and output emitter. -/
theorem four_headers_run (n wit anc out : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ (ShiBQP.encNat wit).map bit ++
        (ShiBQP.encNat anc).map bit ++ (ShiBQP.encNat out).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      topRun^[(n + 1) + (wit + 1) + (anc + 1) + (out + 1)]
        (some { l := some (.inr .inputLength), var := v, stk := S }) =
          some { l := some (.inl (.inr .circuitHeader)), var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) = rest
      ∧ U (.inr (0 : Fin 4)) = List.replicate n Cell.mark ++ S (.inr 0)
      ∧ U (.inr (1 : Fin 4)) = List.replicate wit Cell.mark ++ S (.inr 1)
      ∧ U (.inr (2 : Fin 4)) = List.replicate anc Cell.mark ++ S (.inr 2)
      ∧ U (.inr (3 : Fin 4)) = List.replicate out Cell.mark ++ S (.inr 3)
      ∧ ∀ j : OuterK, j ≠ .inl (11 : Fin 14) → U (.inl j) = S (.inl j) := by
  let r₃ := (ShiBQP.encNat out).map bit ++ rest
  let r₂ := (ShiBQP.encNat anc).map bit ++ r₃
  let r₁ := (ShiBQP.encNat wit).map bit ++ r₂
  have h₁src : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ r₁ := by
    simpa [r₁, r₂, r₃, List.append_assoc] using hsrc
  obtain ⟨S₁, h₁, hs₁, hc₁, hf₁⟩ :=
    header_run .inputLength n r₁ v S h₁src
  have h₂src : S₁ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat wit).map bit ++ r₂ := hs₁
  obtain ⟨S₂, h₂, hs₂, hc₂, hf₂⟩ :=
    header_run .witnessCount wit r₂ (some Cell.delim) S₁ h₂src
  have h₃src : S₂ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat anc).map bit ++ r₃ := hs₂
  obtain ⟨S₃, h₃, hs₃, hc₃, hf₃⟩ :=
    header_run .ancillaCount anc r₃ (some Cell.delim) S₂ h₃src
  have h₄src : S₃ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat out).map bit ++ rest := hs₃
  obtain ⟨S₄, h₄, hs₄, hc₄, hf₄⟩ :=
    header_run .outputIndex out rest (some Cell.delim) S₃ h₄src
  refine ⟨S₄, ?_, hs₄, ?_, ?_, ?_, ?_, ?_⟩
  · have h₁₂ := iterTwo topRun (n + 1) (wit + 1) _ _ _ h₁ h₂
    have h₁₂₃ := iterTwo topRun ((n + 1) + (wit + 1)) (anc + 1)
      _ _ _ h₁₂ h₃
    have h₁₂₃₄ := iterTwo topRun (((n + 1) + (wit + 1)) + (anc + 1))
      (out + 1) _ _ _ h₁₂₃ h₄
    simpa [nextHeader, Nat.add_assoc] using h₁₂₃₄
  · calc
      S₄ (.inr (0 : Fin 4)) = S₃ (.inr 0) := hf₄ _ (by simp) (by decide)
      _ = S₂ (.inr 0) := hf₃ _ (by simp) (by decide)
      _ = S₁ (.inr 0) := hf₂ _ (by simp) (by decide)
      _ = _ := by simpa [headerStack] using hc₁
  · have hs₁ : S₁ (.inr (1 : Fin 4)) = S (.inr 1) :=
      hf₁ _ (by simp) (by decide)
    calc
      S₄ (.inr (1 : Fin 4)) = S₃ (.inr 1) := hf₄ _ (by simp) (by decide)
      _ = S₂ (.inr 1) := hf₃ _ (by simp) (by decide)
      _ = List.replicate wit Cell.mark ++ S₁ (.inr 1) := by
        simpa [headerStack] using hc₂
      _ = _ := by rw [hs₁]
  · have hs₂ : S₂ (.inr (2 : Fin 4)) = S (.inr 2) := by
      calc
        S₂ (.inr (2 : Fin 4)) = S₁ (.inr 2) := hf₂ _ (by simp) (by decide)
        _ = S (.inr 2) := hf₁ _ (by simp) (by decide)
    calc
      S₄ (.inr (2 : Fin 4)) = S₃ (.inr 2) := hf₄ _ (by simp) (by decide)
      _ = List.replicate anc Cell.mark ++ S₂ (.inr 2) := by
        simpa [headerStack] using hc₃
      _ = _ := by rw [hs₂]
  · have hs₃ : S₃ (.inr (3 : Fin 4)) = S (.inr 3) := by
      calc
        S₃ (.inr (3 : Fin 4)) = S₂ (.inr 3) := hf₃ _ (by simp) (by decide)
        _ = S₁ (.inr 3) := hf₂ _ (by simp) (by decide)
        _ = S (.inr 3) := hf₁ _ (by simp) (by decide)
    calc
      S₄ (.inr (3 : Fin 4)) = List.replicate out Cell.mark ++ S₃ (.inr 3) := by
        simpa [headerStack] using hc₄
      _ = _ := by rw [hs₃]
  · intro j hj
    rw [hf₄ (.inl j) (by simpa using hj) (by simp),
      hf₃ (.inl j) (by simpa using hj) (by simp),
      hf₂ (.inl j) (by simpa using hj) (by simp),
      hf₁ (.inl j) (by simpa using hj) (by simp)]

end ShiTMRetainedTop
