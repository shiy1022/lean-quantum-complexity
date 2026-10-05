import Quantum.Dilation

/-! Fresh-import audit for Q08: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder Kronecker

#check (IsChannel.exists_stinespring : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n] {Φ : MatMap m n}, IsChannel Φ →
  ∃ V : Matrix (n × (m × n)) m ℂ, Vᴴ * V = 1 ∧ ∀ X, Φ X = traceRight (V * X * Vᴴ))
#check (IsChannel.stinespring_ampliation : ∀ {m n R : Type} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] [Fintype R] [DecidableEq R] {Φ : MatMap m n}, IsChannel Φ →
  ∃ V : Matrix (n × (m × n)) m ℂ, Vᴴ * V = 1 ∧ ∀ X : Matrix (R × m) (R × m) ℂ,
    liftR R Φ X = traceRight (Matrix.reindex (regAssoc R n (m × n)).symm
      (regAssoc R n (m × n)).symm
      (((1 : Matrix R R ℂ) ⊗ₖ V) * X * ((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ)))
#check (halmosSq_mem_unitaryGroup : ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b] {V : Matrix a b ℂ}, Vᴴ * V = 1 → halmosSq V ∈ Matrix.unitaryGroup (a ⊕ b) ℂ)
#check (halmosSq_inr : ∀ {a b : Type} [Fintype b] [DecidableEq a] (V : Matrix a b ℂ) (i : a)
  (c : b), halmosSq V (Sum.inl i) (Sum.inr c) = V i c)

#print axioms ShiQuantum.stinespring_isometry
#print axioms ShiQuantum.traceRight_stinespring
#print axioms ShiQuantum.IsChannel.exists_stinespring
#print axioms ShiQuantum.liftR_ptraceMap
#print axioms ShiQuantum.IsChannel.stinespring_ampliation
#print axioms ShiQuantum.halmos_inl
#print axioms ShiQuantum.halmos_unitary
#print axioms ShiQuantum.halmosSq_inr
#print axioms ShiQuantum.halmosSq_mem_unitaryGroup
