import «BQP-map-first-steps»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2

theorem scan_left_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (x : List Bool) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ∃ v', (ShiTMSubroutine.run (program tm ea eb))^[x.length]
      (some (cfg tm (.inl .scan) v S (x.map Sum.inl ++ i) o w b)) =
    some (cfg tm (.inl .scan) v' S i o w (x.reverse ++ b)) := by
  induction x generalizing v b with
  | nil => exact ⟨v, rfl⟩
  | cons a x ih =>
      obtain ⟨v', hv⟩ := ih (v.1,some (.inl a)) (a :: b)
      refine ⟨v', ?_⟩
      simp only [List.length_cons, Function.iterate_succ_apply, List.map_cons,
        List.cons_append, scan_inl tm]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv

theorem scan_right_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (x : List Bool) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ∃ v', (ShiTMSubroutine.run (program tm ea eb))^[x.length]
      (some (cfg tm (.inl .scan) v S (x.map Sum.inr ++ i) o w b)) =
    some (cfg tm (.inl .scan) v' S i o (x.reverse ++ w) b) := by
  induction x generalizing v w with
  | nil => exact ⟨v, rfl⟩
  | cons a x ih =>
      obtain ⟨v', hv⟩ := ih (v.1,some (.inr a)) (a :: w)
      refine ⟨v', ?_⟩
      simp only [List.length_cons, Function.iterate_succ_apply, List.map_cons,
        List.cons_append, scan_inr tm]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv

theorem restoreInput_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (b : List Bool) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[b.length + 1]
      (some (cfg tm (.inl .restoreInput) v S i o w b)) =
    some (cfg tm (.inr tm.main) (tm.initialState,none)
      (Function.update S tm.k₀ (b.reverse.map ea.symm ++ S tm.k₀)) i o w []) := by
  induction b generalizing v S with
  | nil => simpa using restoreInput_nil tm ea eb v S i o w []
  | cons a b ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[b.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, restoreInput_cons]
      simpa only [Function.update_self, Function.update_idem, List.reverse_cons,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append] using
        ih (v.1,some (.inl a)) (Function.update S tm.k₀ (ea.symm a :: S tm.k₀))

theorem restoreWitness_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (w : List Bool) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (b : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[w.length + 1]
      (some (cfg tm (.inl .restoreWitness) v S i o w b)) =
    some (cfg tm (.inl .reverseResult) (v.1,none) S i (w.reverse.map Sum.inr ++ o) [] b) := by
  induction w generalizing v o with
  | nil => exact restoreWitness_nil tm ea eb v S i o [] b
  | cons a w ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[w.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, restoreWitness_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using ih (v.1,some (.inr a)) (.inr a :: o)

theorem reverseResult_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (r : List (tm.Γ tm.k₁)) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (h : S tm.k₁ = r) :
    (ShiTMSubroutine.run (program tm ea eb))^[r.length + 1]
      (some (cfg tm (.inl .reverseResult) v S i o w b)) =
    some (cfg tm (.inl .emitResult) (v.1,none)
      (Function.update S tm.k₁ []) i o w (r.reverse.map eb ++ b)) := by
  induction r generalizing v S b with
  | nil =>
      have he : Function.update S tm.k₁ [] = S := by rw [← h]; exact Function.update_eq_self _ _
      simpa [he] using reverseResult_nil tm ea eb v S i o w b h
  | cons a r ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[r.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, reverseResult_cons tm ea eb v S i o w b a r h]
      simpa only [Function.update_idem, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] using
        ih (v.1,some (.inl (eb a))) (Function.update S tm.k₁ r) (eb a :: b) (by simp)

theorem emitResult_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (b : List Bool) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[b.length + 1]
      (some (cfg tm (.inl .emitResult) v S i o w b)) =
    some (⟨none, (tm.initialState,none), mapStacks tm S i (b.reverse.map Sum.inl ++ o) w []⟩ :
      Cfg (framed tm).Γ (Label tm) (State tm)) := by
  induction b generalizing v o with
  | nil => exact emitResult_nil tm ea eb v S i o w []
  | cons a b ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[b.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, emitResult_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using ih (v.1,some (.inl a)) (.inl a :: o)

end BQPMapFirst
