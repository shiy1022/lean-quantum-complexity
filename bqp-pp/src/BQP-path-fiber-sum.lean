import Definitions.Def_ShiShallow_Core

/-! Finite reindexing and input-state identities for passing from the backward
amplitude expansion to forward paths with a common accepting endpoint. -/
set_option autoImplicit false

namespace BQPPaths
open ShiShallow

theorem inputState_delta {n m : ℕ} (x : Bits n) (y : Bits (n + m)) :
    inputState x y = if y = Fin.append x (fun _ : Fin m => false) then 1 else 0 := by
  classical
  have he : ((∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧
      (∀ k : Fin m, y (Fin.natAdd n k) = false)) ↔
      y = Fin.append x (fun _ : Fin m => false) := by
    constructor
    · intro h
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h.1 j
      · simpa using h.2 j
    · intro h
      rw [h]
      constructor <;> intro i <;> simp
  simp only [inputState, he]

/-- Reindex a sum over surviving backward paths using forward witnesses landing
at the chosen output. The endpoint condition is retained throughout. -/
theorem fiber_sum {ι κ Ω : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq Ω]
    (Y : ι → Ω) (B : ι → κ) (P : κ → Ω) (y z : Ω)
    (hmap : ∀ i, Y i = y → P (B i) = z)
    (hinj : ∀ i j, Y i = y → Y j = y → B i = B j → i = j)
    (hsurj : ∀ b, P b = z → ∃ i, Y i = y ∧ B i = b)
    (f : κ → ℂ) :
    ∑ b ∈ Finset.univ.filter (fun b => P b = z), f b =
      ∑ i ∈ Finset.univ.filter (fun i => Y i = y), f (B i) := by
  symm
  apply Finset.sum_bij (fun i _ => B i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hmap i hi
  · intro i hi j hj hij
    exact hinj i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
  · intro b hb
    obtain ⟨i, hi, hBi⟩ := hsurj b (Finset.mem_filter.mp hb).2
    exact ⟨i, by simp [hi], hBi⟩
  · intro i hi
    rfl

end BQPPaths
