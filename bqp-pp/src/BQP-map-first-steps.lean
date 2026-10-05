import «BQP-map-first-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2

def extras (i o : List (Bool ⊕ Bool)) (w b : List Bool) : ∀ e, List (ExtraGam e)
  | .input => i
  | .output => o
  | .witness => w
  | .buffer => b

def mapStacks (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) : ∀ k, List ((framed tm).Γ k) :=
  ShiTMStackFrame.extendStacks S (extras i o w b)

@[simp] theorem stacks_source (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (k : tm.K) :
    mapStacks tm S i o w b (.inl k) = S k := rfl

@[simp] theorem stacks_extra (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (e : Extra) :
    mapStacks tm S i o w b (.inr e) = extras i o w b e := rfl

def cfg (tm : FinTM2) (l : Label tm) (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) : Cfg (framed tm).Γ (Label tm) (State tm) :=
  ⟨some l, v, mapStacks tm S i o w b⟩

@[simp] theorem update_input (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (t : List (Bool ⊕ Bool)) :
    Function.update (mapStacks tm S i o w b) (.inr .input) t =
      mapStacks tm S t o w b := by
  funext k
  cases k with
  | inl k => simp [mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [mapStacks, ShiTMStackFrame.extendStacks, extras]

@[simp] theorem update_output (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (t : List (Bool ⊕ Bool)) :
    Function.update (mapStacks tm S i o w b) (.inr .output) t =
      mapStacks tm S i t w b := by
  funext k
  cases k with
  | inl k => simp [mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [mapStacks, ShiTMStackFrame.extendStacks, extras]

@[simp] theorem update_witness (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (t : List (Bool)) :
    Function.update (mapStacks tm S i o w b) (.inr .witness) t =
      mapStacks tm S i o t b := by
  funext k
  cases k with
  | inl k => simp [mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [mapStacks, ShiTMStackFrame.extendStacks, extras]

@[simp] theorem update_buffer (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (t : List (Bool)) :
    Function.update (mapStacks tm S i o w b) (.inr .buffer) t =
      mapStacks tm S i o w t := by
  funext k
  cases k with
  | inl k => simp [mapStacks, ShiTMStackFrame.extendStacks]
  | inr e => cases e <;> simp [mapStacks, ShiTMStackFrame.extendStacks, extras]

@[simp] theorem update_source (tm : FinTM2) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (k : tm.K) (t : List (tm.Γ k)) :
    Function.update (mapStacks tm S i o w b) (.inl k) t =
      mapStacks tm (Function.update S k t) i o w b := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j; simp [mapStacks, ShiTMStackFrame.extendStacks]
      · have hn : (Sum.inl j : tm.K ⊕ Extra) ≠ .inl k := by simpa using h
        simp [mapStacks, ShiTMStackFrame.extendStacks, h, hn]
  | inr e => simp [mapStacks, ShiTMStackFrame.extendStacks]

theorem scan_inl (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v S (.inl a :: i) o w b)) =
    some (cfg tm (.inl .scan) (v.1,some (.inl a)) S i o w (a :: b)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem scan_inr (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v S (.inr a :: i) o w b)) =
    some (cfg tm (.inl .scan) (v.1,some (.inr a)) S i o (a :: w) b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem scan_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .scan) v S [] o w b)) =
    some (cfg tm (.inl .restoreInput) (v.1,none) S [] o w b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem restoreInput_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restoreInput) v S i o w (a :: b))) =
    some (cfg tm (.inl .restoreInput) (v.1,some (.inl a))
      (Function.update S tm.k₀ (ea.symm a :: S tm.k₀)) i o w b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem restoreInput_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restoreInput) v S i o w [])) =
    some (cfg tm (.inr tm.main) (tm.initialState,none) S i o w []) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem restoreWitness_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restoreWitness) v S i o (a :: w) b)) =
    some (cfg tm (.inl .restoreWitness) (v.1,some (.inr a)) S i (.inr a :: o) w b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem restoreWitness_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .restoreWitness) v S i o [] b)) =
    some (cfg tm (.inl .reverseResult) (v.1,none) S i o [] b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem reverseResult_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : tm.Γ tm.k₁) (r : List (tm.Γ tm.k₁))
    (h : S tm.k₁ = a :: r) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .reverseResult) v S i o w b)) =
    some (cfg tm (.inl .reverseResult) (v.1,some (.inl (eb a)))
      (Function.update S tm.k₁ r) i o w (eb a :: b)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit, h,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem reverseResult_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (h : S tm.k₁ = []) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .reverseResult) v S i o w b)) =
    some (cfg tm (.inl .emitResult) (v.1,none) S i o w b) := by
  have he : Function.update S tm.k₁ [] = S := by rw [← h]; exact Function.update_eq_self _ _
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit, h, he,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem emitResult_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) (a : Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .emitResult) v S i o w (a :: b))) =
    some (cfg tm (.inl .emitResult) (v.1,some (.inl a)) S i (.inl a :: o) w b) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

theorem emitResult_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : State tm) (S : ∀ k, List (tm.Γ k))
    (i o : List (Bool ⊕ Bool)) (w b : List Bool) :
    ShiTMSubroutine.run (program tm ea eb)
      (some (cfg tm (.inl .emitResult) v S i o w [])) =
    some (⟨none, (tm.initialState,none), mapStacks tm S i o w []⟩ :
      Cfg (framed tm).Γ (Label tm) (State tm)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux, registerBit,
    extras, update_input tm, update_output tm, update_witness tm, update_buffer tm, update_source tm]

end BQPMapFirst
