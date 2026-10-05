import Quantum.ChannelMathlib

/-! Fresh-import audit for Q06: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

#check (IsCP.isPositiveMap : ∀ {m n : Type} [Fintype m] [Fintype n] {Φ : MatMap m n},
  IsCP Φ → IsPositiveMap Φ)
#check (not_isCP_transposeMap : ¬ IsCP (transposeMap Bool))
#check (IsChannel.map_density : ∀ {m n : Type} [Fintype m] [Fintype n] {Φ : MatMap m n},
  IsChannel Φ → ∀ {ρ : Matrix m m ℂ}, IsDensity ρ → IsDensity (Φ ρ))
#check (isChannel_krausMap : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] {ι : Type}
  [Fintype ι] {V : ι → Matrix n m ℂ}, ∑ i, (V i)ᴴ * V i = 1 → IsChannel (krausMap V))
#check (traceRight_liftR : ∀ {k m n : Type} [Fintype m] [Fintype n] {Φ : MatMap m n},
  IsTP Φ → ∀ X : Matrix (k × m) (k × m) ℂ, traceRight (liftR k Φ X) = traceRight X)
#check (tensorMap_kronecker : ∀ {m n p q : Type} (Φ : MatMap m n) (Ψ : MatMap p q)
  (A : Matrix m m ℂ) (B : Matrix p p ℂ), tensorMap Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B)
#check (isCP_iff_cpMap : ∀ {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (Φ : MatMap m n), IsCP Φ ↔ ∀ (j : ℕ) (M : CStarMatrix (Fin j) (Fin j) (Matrix m m ℂ)),
    0 ≤ M → 0 ≤ M.map Φ)

#print axioms ShiQuantum.IsCP.isPositiveMap
#print axioms ShiQuantum.IsChannel.map_density
#print axioms ShiQuantum.liftR_id
#print axioms ShiQuantum.liftR_comp
#print axioms ShiQuantum.isChannel_id
#print axioms ShiQuantum.IsCP.comp
#print axioms ShiQuantum.IsChannel.comp
#print axioms ShiQuantum.IsCP.add
#print axioms ShiQuantum.IsCP.smul
#print axioms ShiQuantum.isCP_sum
#print axioms ShiQuantum.liftR_conjMap
#print axioms ShiQuantum.isCP_conjMap
#print axioms ShiQuantum.isChannel_conjMap
#print axioms ShiQuantum.isChannel_unitary
#print axioms ShiQuantum.krausMap_apply
#print axioms ShiQuantum.isChannel_krausMap
#print axioms ShiQuantum.liftR_discardMap
#print axioms ShiQuantum.isChannel_discardMap
#print axioms ShiQuantum.liftR_prepMap
#print axioms ShiQuantum.isChannel_prepMap
#print axioms ShiQuantum.dephase_eq_krausMap
#print axioms ShiQuantum.isChannel_dephase
#print axioms ShiQuantum.IsInstrument.isChannel_sum
#print axioms ShiQuantum.IsInstrument.prob_nonneg
#print axioms ShiQuantum.IsInstrument.sum_prob
#print axioms ShiQuantum.isInstrument_basis
#print axioms ShiQuantum.transposeMap_isPositiveMap
#print axioms ShiQuantum.not_isCP_transposeMap
#print axioms ShiQuantum.isChannel_reindexMap
#print axioms ShiQuantum.liftR_liftR
#print axioms ShiQuantum.IsCP.liftR
#print axioms ShiQuantum.IsTP.liftR
#print axioms ShiQuantum.IsChannel.liftR
#print axioms ShiQuantum.traceRight_liftR
#print axioms ShiQuantum.IsChannel.marginal_invariant
#print axioms ShiQuantum.IsChannel.liftL
#print axioms ShiQuantum.traceRight_liftL
#print axioms ShiQuantum.liftR_kronecker
#print axioms ShiQuantum.liftL_kronecker
#print axioms ShiQuantum.tensorMap_kronecker
#print axioms ShiQuantum.IsChannel.tensor
#print axioms ShiQuantum.IsChannel.tensor_product
#print axioms ShiQuantum.flat_star_mul
#print axioms ShiQuantum.cstar_nonneg_iff_flat
#print axioms ShiQuantum.flat_map
#print axioms ShiQuantum.isCP_iff_cpMap
