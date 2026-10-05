import «BQP-prefix-steps»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPPrefixMachine
open Turing Turing.TM2

 theorem scan_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (x : List Bool) (v : State tm)
    (s a : List (tm.Γ tm.k₀)) :
    ∃ v', (ShiTMSubroutine.run (program tm ea eb))^[x.length]
      (some (cfg tm (.inl .scan) v (x.map (fun b => ea.symm (.inl b)) ++ s) a)) =
    some (cfg tm (.inl .scan) v' s
      ((x.map (fun b => ea.symm (.inl b))).reverse ++ a)) := by
  induction x generalizing v a with
  | nil => exact ⟨v, rfl⟩
  | cons b x ih =>
      obtain ⟨v', hv⟩ := ih (v.1, some (ea.symm (.inl b))) (ea.symm (.inl b) :: a)
      refine ⟨v', ?_⟩
      simp only [List.length_cons, Function.iterate_succ_apply, List.map_cons,
        List.cons_append, scan_left tm]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv

 theorem restore_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (a : List (tm.Γ tm.k₀))
    (v : State tm) (s : List (tm.Γ tm.k₀)) :
    (ShiTMSubroutine.run (program tm ea eb))^[a.length + 1]
      (some (cfg tm (.inl .restore) v s a)) =
    some (embed tm (initList tm (a.reverse ++ s))) := by
  induction a generalizing v s with
  | nil => exact restore_nil tm ea eb v s
  | cons b a ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[a.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, restore_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (v.1, some b) (b :: s)

 theorem rejectAux_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (a : List (tm.Γ tm.k₀)) (v : State tm) :
    (ShiTMSubroutine.run (program tm ea eb))^[a.length + 1]
      (some (cfg tm (.inl .rejectAux) v [] a)) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  induction a generalizing v with
  | nil => exact rejectAux_nil tm ea eb v
  | cons b a ih =>
      change (ShiTMSubroutine.run (program tm ea eb))^[a.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, rejectAux_cons]
      exact ih (v.1, some b)

 theorem reject_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (s a : List (tm.Γ tm.k₀)) (v : State tm) :
    (ShiTMSubroutine.run (program tm ea eb))^[s.length + a.length + 2]
      (some (cfg tm (.inl .rejectInput) v s a)) =
    some (haltList (machine tm ea eb) [eb.symm false]) := by
  induction s generalizing v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add]
      change (ShiTMSubroutine.run (program tm ea eb))^[a.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, rejectInput_nil]
      exact rejectAux_run tm ea eb a (v.1, none)
  | cons b s ih =>
      rw [show (b :: s).length + a.length + 2 = (s.length + a.length + 2) + 1 by simp; omega]
      rw [Function.iterate_succ_apply, rejectInput_cons]
      exact ih (v.1, some b)

 theorem init_eq (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (s : List (tm.Γ tm.k₀)) :
    initList (machine tm ea eb) s = cfg tm (.inl .scan) (tm.initialState, none) s [] := by
  apply congrArg (fun S => (⟨some (.inl .scan), (tm.initialState, none), S⟩ :
    Cfg (framed tm).Γ (Label tm) (State tm)))
  funext k
  cases k with
  | inl k =>
      by_cases h : k = tm.k₀
      · subst k; simp [initList, machine, framed, cfg, prefixStacks, ShiTMStackFrame.extendStacks] <;> rfl
      · have hn : (Sum.inl k : tm.K ⊕ Unit) ≠ .inl tm.k₀ := by simpa using h
        simp [initList, machine, framed, cfg, prefixStacks, ShiTMStackFrame.extendStacks,
          BQPShortMachine.inputStacks, h, hn]
  | inr u => cases u; simp [initList, machine, framed, cfg, prefixStacks, ShiTMStackFrame.extendStacks]

 theorem embedded_halt (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (out : List (tm.Γ tm.k₁)) :
    embed tm (haltList tm out) = haltList (machine tm ea eb) out := by
  apply congrArg (fun S => (⟨none, (tm.initialState, none), S⟩ :
    Cfg (framed tm).Γ (Label tm) (State tm)))
  funext k
  cases k with
  | inl k =>
      by_cases h : k = tm.k₁
      · subst k; simp [embed, ShiTMSubroutine.cfg, ShiTMStateFrame.cfg,
          ShiTMStackFrame.cfg, ShiTMStackFrame.extendStacks, haltList, machine, framed] <;> rfl
      · have hn : (Sum.inl k : tm.K ⊕ Unit) ≠ .inl tm.k₁ := by simpa using h
        simp [embed, ShiTMSubroutine.cfg, ShiTMStateFrame.cfg,
          ShiTMStackFrame.cfg, ShiTMStackFrame.extendStacks, haltList, machine, framed, h, hn]
  | inr u => cases u; simp [embed, ShiTMSubroutine.cfg, ShiTMStateFrame.cfg,
      ShiTMStackFrame.cfg, ShiTMStackFrame.extendStacks, haltList, machine, framed]

end BQPPrefixMachine
