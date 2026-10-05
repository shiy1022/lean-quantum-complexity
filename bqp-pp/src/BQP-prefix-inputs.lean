import «BQP-prefix-runs»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPPrefixMachine
open Turing Turing.TM2

 theorem iterate_chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (ha : f^[a] x = y) (hb : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

 def encodePair (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (x w : List Bool) : List (tm.Γ tm.k₀) :=
  x.map (fun b => ea.symm (.inl b)) ++ w.map (fun b => ea.symm (.inr b))

 theorem good_prefix (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x w : List Bool) (b : Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[2*x.length+3]
      (some (initList (machine tm ea eb) (encodePair tm ea x (b::b::w)))) =
    some (embed tm (initList tm (encodePair tm ea x w))) := by
  let f := ShiTMSubroutine.run (program tm ea eb)
  let s := w.map (fun b => ea.symm (.inr b))
  let a := (x.map (fun b => ea.symm (.inl b))).reverse
  obtain ⟨v, hv⟩ := scan_run tm ea eb x (tm.initialState, none)
    (ea.symm (.inr b) :: ea.symm (.inr b) :: s) []
  simp only [List.append_nil] at hv
  have htwo : f^[2] (some (cfg tm (.inl .scan) v
      (ea.symm (.inr b) :: ea.symm (.inr b) :: s) a)) =
      some (cfg tm (.inl .restore) (v.1, some (ea.symm (.inr b))) s a) := by
    exact (congrArg f (scan_right tm ea eb b v _ a)).trans
      (by simpa using second_right tm ea eb b b (v.1, some (ea.symm (.inr b))) s a)
  have hr := restore_run tm ea eb a (v.1, some (ea.symm (.inr b))) s
  have h := iterate_chain f _ _ _ _ _ (iterate_chain f _ _ _ _ _ hv htwo) hr
  have hn : x.length + 2 + (a.length + 1) = 2*x.length+3 := by simp [a]; omega
  simp only [List.length_nil] at h
  rw [hn] at h
  simpa only [init_eq, encodePair, List.map_cons, a, s, List.reverse_reverse] using h

 theorem empty_witness (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x : List Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[2*x.length+3]
      (some (initList (machine tm ea eb) (encodePair tm ea x []))) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  let f := ShiTMSubroutine.run (program tm ea eb)
  let a := (x.map (fun b => ea.symm (.inl b))).reverse
  obtain ⟨v, hv⟩ := scan_run tm ea eb x (tm.initialState, none) [] []
  simp only [List.append_nil] at hv
  have h1 := scan_nil tm ea eb v a
  have hr := reject_run tm ea eb [] a (v.1, none)
  have h := iterate_chain f _ _ _ _ _ (iterate_chain f _ _ _ _ 1 hv h1) hr
  have hn : x.length + 1 + (0 + a.length + 2) = 2*x.length+3 := by simp [a]; omega
  simp only [List.length_nil] at h
  rw [hn] at h
  simpa only [init_eq, encodePair, List.map_nil, List.append_nil] using h

 theorem singleton_witness (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x : List Bool) (b : Bool) :
    (ShiTMSubroutine.run (program tm ea eb))^[2*x.length+4]
      (some (initList (machine tm ea eb) (encodePair tm ea x [b]))) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  let f := ShiTMSubroutine.run (program tm ea eb)
  let a := (x.map (fun b => ea.symm (.inl b))).reverse
  obtain ⟨v, hv⟩ := scan_run tm ea eb x (tm.initialState, none) [ea.symm (.inr b)] []
  simp only [List.append_nil] at hv
  have h1 := scan_right tm ea eb b v [] a
  have h2 := second_nil tm ea eb b (v.1, some (ea.symm (.inr b))) a
  have hr := reject_run tm ea eb [] a (v.1, none)
  have h := iterate_chain f _ _ _ _ _
    (iterate_chain f _ _ _ _ 1 (iterate_chain f _ _ _ _ 1 hv h1) h2) hr
  have hn : x.length + 1 + 1 + (0 + a.length + 2) = 2*x.length+4 := by simp [a]; omega
  simp only [List.length_nil] at h
  rw [hn] at h
  simpa only [init_eq, encodePair, List.map_cons, List.map_nil] using h

 theorem unequal_witness (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x w : List Bool) (b d : Bool) (hne : b ≠ d) :
    (ShiTMSubroutine.run (program tm ea eb))^[2*x.length+w.length+4]
      (some (initList (machine tm ea eb) (encodePair tm ea x (b::d::w)))) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  let f := ShiTMSubroutine.run (program tm ea eb)
  let s := w.map (fun b => ea.symm (.inr b))
  let a := (x.map (fun b => ea.symm (.inl b))).reverse
  obtain ⟨v, hv⟩ := scan_run tm ea eb x (tm.initialState, none)
    (ea.symm (.inr b)::ea.symm (.inr d)::s) []
  simp only [List.append_nil] at hv
  have h1 := scan_right tm ea eb b v (ea.symm (.inr d)::s) a
  have h2 := second_right tm ea eb b d (v.1, some (ea.symm (.inr b))) s a
  simp only [beq_iff_eq, hne, ↓reduceIte] at h2
  have hr := reject_run tm ea eb s a (v.1, some (ea.symm (.inr d)))
  have h := iterate_chain f _ _ _ _ _
    (iterate_chain f _ _ _ _ 1 (iterate_chain f _ _ _ _ 1 hv h1) h2) hr
  have hn : x.length + 1 + 1 + (s.length + a.length + 2) = 2*x.length+w.length+4 := by
    simp [a,s]; omega
  simp only [List.length_nil] at h
  rw [hn] at h
  simpa only [init_eq, encodePair, List.map_cons, a, s] using h

end BQPPrefixMachine
