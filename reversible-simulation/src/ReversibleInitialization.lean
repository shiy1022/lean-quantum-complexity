import ReversibleStatementSize

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleCoding ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

noncomputable def inputSymbol (tm : Turing.FinTM2) (a : tm.Γ tm.k₀) : MachineSymbol tm := by
  classical
  exact ⟨⟨tm.k₀, a⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)⟩

noncomputable def initialFiniteCfg (tm : Turing.FinTM2) (capacity : Nat)
    (xs : List (tm.Γ tm.k₀)) : FiniteCfg tm capacity where
  label := some tm.main
  memory := tm.initialState
  cells k := if k = tm.k₀ then tapeEncode capacity (xs.map (inputSymbol tm)) else fun _ => none

noncomputable def initialBoundedCfg (tm : Turing.FinTM2) (capacity : Nat)
    (xs : List (tm.Γ tm.k₀)) (h : xs.length ≤ capacity) : BoundedCfg tm capacity where
  cfg := Turing.initList tm xs
  length_bound k := (initial_stack_length tm xs k).trans h
  alphabet := initial_alphabet tm xs

/-- Tagging the initial symbols does not depend on alphabet proof witnesses. -/
theorem initialBoundedCfg_encode (tm : Turing.FinTM2) (capacity : Nat)
    (xs : List (tm.Γ tm.k₀)) (h : xs.length ≤ capacity) :
    (initialBoundedCfg tm capacity xs h).encode = initialFiniteCfg tm capacity xs := by
  apply FiniteCfg.ext
  · rfl
  · rfl
  · funext k
    by_cases hk : k = tm.k₀
    · subst k
      have hs : (initialBoundedCfg tm capacity xs h).stackSymbols tm.k₀ = xs.map (inputSymbol tm) := by
        apply List.ext_getElem
        · simp [BoundedCfg.stackSymbols, initialBoundedCfg, Turing.initList]
        · intro i hi hj
          apply Subtype.ext
          simp [BoundedCfg.stackSymbols, initialBoundedCfg, Turing.initList, inputSymbol]
      change tapeEncode capacity ((initialBoundedCfg tm capacity xs h).stackSymbols tm.k₀) = _
      rw [hs]
      simp [initialFiniteCfg]
    · have hs : (initialBoundedCfg tm capacity xs h).stackSymbols k = [] := by
        simp [BoundedCfg.stackSymbols, initialBoundedCfg, Turing.initList, hk]
      change tapeEncode capacity ((initialBoundedCfg tm capacity xs h).stackSymbols k) = _
      rw [hs]
      simp only [initialFiniteCfg, if_neg hk]
      funext i
      simp [tapeEncode]

def booleanInputCodes {n : Nat} (i : Fin n) : Bool → Formula (Fin n) :=
  fun b => if b then .input i else .neg (.input i)

theorem booleanInputCodes_eval {n : Nat} (i : Fin n) (x : Bits n) (b : Bool) :
    (booleanInputCodes i b).eval x = oneHot (x i) b := by
  cases b <;> cases h : x i <;> simp [booleanInputCodes, Formula.eval, oneHot, h]

theorem booleanInputCodes_size {n : Nat} (i : Fin n) (b : Bool) :
    (booleanInputCodes i b).size ≤ 2 := by
  cases b <;> simp [booleanInputCodes, Formula.size]

/-- Initialization uses raw input wires and constant formulas, including all padding cells. -/
noncomputable def initialFormulas (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : FormulaCfg tm capacity (Fin n) where
  label l := .constant (oneHot (some tm.main) l)
  memory v := .constant (oneHot tm.initialState v)
  cells k i a := if k = tm.k₀ then
    if hi : i.val < n then unaryTable (fun b => some (inputSymbol tm (e.symm b)))
      (booleanInputCodes ⟨i.val, hi⟩) a
    else .constant (oneHot none a)
    else .constant (oneHot none a)

theorem initialFormulas_denotes (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (x : Bits n) :
    (initialFormulas tm e capacity n).Denotes x
      (initialFiniteCfg tm capacity (List.ofFn (fun i => e.symm (x i)))) := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i a
  by_cases hk : k = tm.k₀
  · by_cases hi : i.val < n
    · have he := eval_unaryTable (fun b => some (inputSymbol tm (e.symm b)))
        (booleanInputCodes ⟨i.val, hi⟩) x (x ⟨i.val, hi⟩) a (booleanInputCodes_eval _ x)
      simpa [initialFormulas, initialFiniteCfg, hk, hi, tapeEncode, List.map_ofFn] using he
    · simp [initialFormulas, initialFiniteCfg, hk, hi, tapeEncode, List.map_ofFn, Formula.eval]
  · simp [initialFormulas, initialFiniteCfg, hk, Formula.eval]

theorem initialFormulas_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : (initialFormulas tm e capacity n).SizeBound 17 := by
  refine ⟨by omega, fun _ => by simp [initialFormulas, Formula.size],
    fun _ => by simp [initialFormulas, Formula.size], ?_⟩
  intro k i a
  by_cases hk : k = tm.k₀
  · by_cases hi : i.val < n
    · have hs := size_unaryTable (fun b => some (inputSymbol tm (e.symm b)))
        (booleanInputCodes ⟨i.val, hi⟩) a 2 (booleanInputCodes_size _)
      simpa [initialFormulas, hk, hi] using hs
    · simp [initialFormulas, hk, hi, Formula.size]
  · simp [initialFormulas, hk, Formula.size]

noncomputable def initialForest (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : List (Formula (Fin n)) := List.ofFn (initialFormulas tm e capacity n).bitFormula

@[simp] theorem initialForest_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : (initialForest tm e capacity n).length = configurationWidth tm capacity := by
  simp [initialForest]

theorem initialForest_eval (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (x : Bits n) (i : Fin (initialForest tm e capacity n).length) :
    ((initialForest tm e capacity n)[i.val]).eval x =
      (initialFiniteCfg tm capacity (List.ofFn (fun j => e.symm (x j)))).bitEncode
        ⟨i.val, by simpa using i.isLt⟩ := by
  simpa [initialForest] using FormulaCfg.bitFormula_eval _ x _
    (initialFormulas_denotes tm e capacity n x) ⟨i.val, by simpa using i.isLt⟩

theorem initialForest_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (capacity n : Nat) :
    ∀ p ∈ initialForest tm e capacity n, p.size ≤ 17 := by
  have h := initialFormulas_size tm e capacity n
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  unfold FormulaCfg.bitFormula
  cases (configurationBitEquiv tm capacity).symm i with
  | inl z => cases z with
    | inl l => exact h.2.1 l
    | inr v => exact h.2.2.1 v
  | inr z => exact h.2.2.2 z.1.1 z.1.2 z.2

end ShiReversibleTM
