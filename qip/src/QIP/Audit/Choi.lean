import Quantum.Kraus

/-! Fresh-import audit for Q07: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder

#check (choi_apply : ∀ {m n : Type} [DecidableEq m] (Φ : MatMap m n) (a b : m) (i j : n),
  choi Φ (a, i) (b, j) = Φ (Matrix.single a b 1) i j)
#check (ofChoi_choi : ∀ {m n : Type} [Fintype m] [DecidableEq m] (Φ : MatMap m n),
  ofChoi (choi Φ) = Φ)
#check (choi_ofChoi : ∀ {m n : Type} [Fintype m] [DecidableEq m]
  (J : Matrix (m × n) (m × n) ℂ), choi (ofChoi J) = J)
#check (isCP_iff_choi_posSemidef : ∀ {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] (Φ : MatMap m n), IsCP Φ ↔ (choi Φ).PosSemidef)
#check (isTP_iff_traceRight_choi : ∀ {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
  (Φ : MatMap m n), IsTP Φ ↔ traceRight (choi Φ) = 1)
#check (isChannel_iff_exists_kraus : ∀ {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] (Φ : MatMap m n),
  IsChannel Φ ↔ ∃ K : m × n → Matrix n m ℂ, Φ = krausMap K ∧ ∑ c, (K c)ᴴ * K c = 1)

#print axioms ShiQuantum.map_eq_sum_single
#print axioms ShiQuantum.ofChoi_choi
#print axioms ShiQuantum.choi_ofChoi
#print axioms ShiQuantum.choi_injective
#print axioms ShiQuantum.choi_eq_liftR
#print axioms ShiQuantum.choi_id
#print axioms ShiQuantum.IsCP.choi_posSemidef
#print axioms ShiQuantum.traceRight_choi
#print axioms ShiQuantum.trace_ofChoi
#print axioms ShiQuantum.isTP_iff_traceRight_choi
#print axioms ShiQuantum.ofChoi_mul_conjTranspose
#print axioms ShiQuantum.sum_krausOfFactor
#print axioms ShiQuantum.isCP_iff_choi_posSemidef
#print axioms ShiQuantum.IsCP.exists_kraus
#print axioms ShiQuantum.isChannel_iff_exists_kraus
