import «AMPUNI-normalized-entry-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

/-- The existing unary-header run lifts to the redirected finite front-end. -/
theorem header_run_lift (h : Header) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ rest) :
    run^[n + 1]
        (some { l := some (headerLabel h), var := v, stk := S }) =
      (topRun^[n + 1]
        (some { l := some (.inr h), var := v, stk := S })).map
          (ShiTMSubroutine.cfg mapTop) := by
  induction n generalizing v S with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one] using header_step h v S
  | succ n ih =>
      have henc : ((ShiBQP.encNat (n + 1)).map bit ++ rest) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        simp [ShiBQP.encNat, bit, List.replicate_succ, List.append_assoc]
      have hm : S (.inl (.inl (11 : Fin 14))) =
          Cell.mark :: ((ShiBQP.encNat n).map bit ++ rest) := by
        rw [hsrc, henc]
      let T := Function.update
        (Function.update S (.inl (.inl (11 : Fin 14)))
          ((ShiBQP.encNat n).map bit ++ rest))
        (.inr (headerStack h))
        (Cell.mark :: S (.inr (headerStack h)))
      have ht : topRun
          (some { l := some (.inr h), var := v, stk := S }) =
            some { l := some (.inr h), var := some Cell.mark, stk := T } := by
        exact header_mark_step h v S _ hm
      have he : run
          (some { l := some (headerLabel h), var := v, stk := S }) =
            some { l := some (headerLabel h), var := some Cell.mark, stk := T } := by
        rw [header_step, ht]
        rfl
      have hTsrc : T (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encNat n).map bit ++ rest := by
        simp [T]
      have hrec := ih (some Cell.mark) T hTsrc
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        Function.iterate_succ_apply, he, ht] using hrec

theorem entry_header_run (h : Header) (n : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[n + 1]
        (some { l := some (headerLabel h), var := v, stk := S }) =
          some { l := some (mapTop (nextHeader h)), var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) = rest
      ∧ U (.inr (headerStack h)) =
          List.replicate n Cell.mark ++ S (.inr (headerStack h))
      ∧ ∀ j, j ≠ .inl (.inl (11 : Fin 14)) →
          j ≠ .inr (headerStack h) → U j = S j := by
  obtain ⟨U, hr, h11, hc, hf⟩ := header_run h n rest v S hsrc
  refine ⟨U, ?_, h11, hc, hf⟩
  rw [header_run_lift h n rest v S hsrc, hr]
  rfl

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Four already-proved unary-header scans now hand off to the finite
numeric-output controller, with the circuit suffix untouched. -/
theorem four_headers_to_output (n wit anc out : Nat) (rest : List Cell)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ (ShiBQP.encNat wit).map bit ++
        (ShiBQP.encNat anc).map bit ++ (ShiBQP.encNat out).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[(n + 1) + (wit + 1) + (anc + 1) + (out + 1)]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some { l := some outputEntry, var := some Cell.delim, stk := U }
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
    entry_header_run .inputLength n r₁ v S h₁src
  have h₂src : S₁ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat wit).map bit ++ r₂ := hs₁
  obtain ⟨S₂, h₂, hs₂, hc₂, hf₂⟩ :=
    entry_header_run .witnessCount wit r₂ (some Cell.delim) S₁ h₂src
  have h₃src : S₂ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat anc).map bit ++ r₃ := hs₂
  obtain ⟨S₃, h₃, hs₃, hc₃, hf₃⟩ :=
    entry_header_run .ancillaCount anc r₃ (some Cell.delim) S₂ h₃src
  have h₄src : S₃ (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat out).map bit ++ rest := hs₃
  obtain ⟨S₄, h₄, hs₄, hc₄, hf₄⟩ :=
    entry_header_run .outputIndex out rest (some Cell.delim) S₃ h₄src
  refine ⟨S₄, ?_, hs₄, ?_, ?_, ?_, ?_, ?_⟩
  · have h₁₂ := iterTwo run (n + 1) (wit + 1) _ _ _ h₁ h₂
    have h₁₂₃ := iterTwo run ((n + 1) + (wit + 1)) (anc + 1)
      _ _ _ h₁₂ h₃
    have h₁₂₃₄ := iterTwo run (((n + 1) + (wit + 1)) + (anc + 1))
      (out + 1) _ _ _ h₁₂₃ h₄
    simpa [outputEntry, mapTop, nextHeader, headerLabel,
      Nat.add_assoc] using h₁₂₃₄
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

/-- The length-aware family encoding supplies exactly the four headers that
the redirected finite front-end consumes. -/
theorem family_headers_to_output (F : ShiClassQMA.QMAFamily) (n : Nat)
    (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[(n + 1) + (F.wit n + 1) + (F.anc n + 1) +
        ((F.out n : Nat) + 1)]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some { l := some outputEntry, var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encCirc (F.circ n)).map bit ++ rest
      ∧ U (.inr (0 : Fin 4)) = List.replicate n Cell.mark ++ S (.inr 0)
      ∧ U (.inr (1 : Fin 4)) = List.replicate (F.wit n) Cell.mark ++ S (.inr 1)
      ∧ U (.inr (2 : Fin 4)) = List.replicate (F.anc n) Cell.mark ++ S (.inr 2)
      ∧ U (.inr (3 : Fin 4)) =
          List.replicate (F.out n : Nat) Cell.mark ++ S (.inr 3)
      ∧ ∀ j : OuterK, j ≠ .inl (11 : Fin 14) → U (.inl j) = S (.inl j) := by
  have hsplit : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ (ShiBQP.encNat (F.wit n)).map bit ++
        (ShiBQP.encNat (F.anc n)).map bit ++
        (ShiBQP.encNat (F.out n : Nat)).map bit ++
        ((ShiBQP.encCirc (F.circ n)).map bit ++ rest) := by
    simpa [ShiClassQMAU.encQMAFamilyAt, List.map_append,
      List.append_assoc] using hsrc
  exact four_headers_to_output n (F.wit n) (F.anc n) (F.out n : Nat)
    ((ShiBQP.encCirc (F.circ n)).map bit ++ rest) v S hsplit


end ShiTMNormalizedEntry
