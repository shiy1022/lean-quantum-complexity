import «AMPUNI-fanout-prepare-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadoutIndexLoad
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev archive : TopK := .inr (3 : Fin 4)
abbrev index : TopK := .inl (.inl (0 : Fin 14))
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
inductive Label where
  | clear | copy | restore | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.clear, .copy, .restore, .finished]
  (by intro l; cases l <;> simp)

/-- Copy only the unary output-index prefix. Peeking at the first non-mark
leaves the archive sentinel and every archived input cell untouched. -/
def machine : Label → Stmt TopGam Label Sig
  | .clear => .pop index pop (.branch isSome
      (.goto (fun _ => .clear)) (.goto (fun _ => .copy)))
  | .copy => .peek archive pop (.branch isMark
      (.pop archive pop (.push index (cst .mark)
        (.push scratch (cst .mark) (.goto (fun _ => .copy)))))
      (.goto (fun _ => .restore)))
  | .restore => .pop scratch pop (.branch isSome
      (.push archive (cst .mark) (.goto (fun _ => .restore)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := archive
  k₁ := index
  Γ := TopGam
  Λ := Label
  main := .clear
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem clear_run (xs : List Cell) (v : Sig) (S : ∀ k, List (TopGam k))
    (hs : S index = xs) :
    run^[xs.length+1] (some ⟨some .clear, v, S⟩) =
      some ⟨some .copy, none, Function.update S index []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, machine, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
      have hfirst : run (some ⟨some .clear, v, S⟩) =
          some ⟨some .clear, some x, Function.update S index xs⟩ := by
        simp [run, machine, step, stepAux, hs, pop, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih (some x) (Function.update S index xs) (by simp)

theorem copy_run (n : Nat) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hs : S archive = List.replicate n Cell.mark ++ Cell.mirrorEnd :: tail) :
    ∃ U : ∀ k, List (TopGam k),
      run^[n+1] (some ⟨some .copy, v, S⟩) =
        some ⟨some .restore, some Cell.mirrorEnd, U⟩
      ∧ U archive = Cell.mirrorEnd :: tail
      ∧ U index = List.replicate n Cell.mark ++ S index
      ∧ U scratch = List.replicate n Cell.mark ++ S scratch
      ∧ ∀ k, k ≠ archive → k ≠ index → k ≠ scratch → U k = S k := by
  induction n generalizing v S with
  | zero =>
      have he : S archive = Cell.mirrorEnd :: tail := by simpa using hs
      refine ⟨S, ?_, he, by simp, by simp, by intro k _ _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isMark]
  | succ n ih =>
      have hm : S archive = Cell.mark :: (List.replicate n Cell.mark ++ Cell.mirrorEnd :: tail) := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update (Function.update S archive
          (List.replicate n Cell.mark ++ Cell.mirrorEnd :: tail))
          index (Cell.mark :: S index)) scratch (Cell.mark :: S scratch)
      have hfirst : run (some ⟨some .copy, v, S⟩) =
          some ⟨some .copy, some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isMark, cst, T, archive, index, scratch]
      obtain ⟨U, hr, ha, hi, ht, hf⟩ := ih (some Cell.mark) T (by simp [T, archive, index, scratch])
      refine ⟨U, ?_, ha, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]; exact hr
      · rw [hi]; simp [T, archive, index, scratch, List.replicate_add, List.append_assoc]
      · rw [ht]; simp [T, List.replicate_add, List.append_assoc]
      · intro k hka hki hkt
        rw [hf k hka hki hkt]
        simp [T, hka, hki, hkt]

theorem restore_run (n : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hs : S scratch = List.replicate n Cell.mark) :
    ∃ U : ∀ k, List (TopGam k),
      run^[n+1] (some ⟨some .restore, v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U scratch = []
      ∧ U archive = List.replicate n Cell.mark ++ S archive
      ∧ ∀ k, k ≠ archive → k ≠ scratch → U k = S k := by
  induction n generalizing v S with
  | zero =>
      have he : S scratch = [] := by simpa using hs
      refine ⟨S, ?_, he, by simp, by intro k _ _; rfl⟩
      simp [run, machine, step, stepAux, he, pop, isSome]
  | succ n ih =>
      have hm : S scratch = Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hs
      let T := Function.update (Function.update S scratch (List.replicate n Cell.mark))
        archive (Cell.mark :: S archive)
      have hfirst : run (some ⟨some .restore, v, S⟩) =
          some ⟨some .restore, some Cell.mark, T⟩ := by
        simp [run, machine, step, stepAux, hm, pop, isSome, cst, T]
      obtain ⟨U, hr, ht, ha, hf⟩ := ih (some Cell.mark) T (by simp [T, archive, scratch])
      refine ⟨U, ?_, ht, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hfirst]; exact hr
      · rw [ha]; simp [T, List.replicate_add, List.append_assoc]
      · intro k hka hkt
        rw [hf k hka hkt]
        simp [T, hka, hkt]

/-- Load the original output index for another layout lookup, restoring the
entire retained archive and every other stack, including empty scratch. -/
theorem load_run (n : Nat) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (ha : S archive = List.replicate n Cell.mark ++ Cell.mirrorEnd :: tail)
    (ht : S scratch = []) :
    run^[(S index).length+2*n+3] (some ⟨some .clear, v, S⟩) =
      some ⟨some .finished, none, Function.update S index (List.replicate n Cell.mark)⟩ := by
  let T := Function.update S index []
  have hclear := clear_run (S index) v S rfl
  obtain ⟨U, hc, hau, hiu, htu, hfu⟩ := copy_run n tail none T (by simp [T, archive, index, ha])
  obtain ⟨W, hr, htw, haw, hfw⟩ := restore_run n (some Cell.mirrorEnd) U
    (by simpa [T, scratch, index, ht] using htu)
  have heq : W = Function.update S index (List.replicate n Cell.mark) := by
    funext k
    by_cases hki : k = index
    · subst k
      rw [hfw index (by decide) (by decide), hiu]
      simp [T]
    by_cases hka : k = archive
    · subst k
      rw [haw, hau]
      simp [Function.update_of_ne (show archive ≠ index by decide), ha]
    by_cases hkt : k = scratch
    · subst k
      rw [htw]
      simp [Function.update_of_ne (show scratch ≠ index by decide), ht]
    rw [hfw k hka hkt, hfu k hka hki hkt]
    simp [T, hki]
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ hclear hc
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hr
  rw [heq] at h2
  have hcost : (S index).length+1+(n+1)+(n+1) = (S index).length+2*n+3 := by omega
  simpa only [hcost] using h2

end ShiTMReadoutIndexLoad
