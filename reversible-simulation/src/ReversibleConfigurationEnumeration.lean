import ReversibleFiniteCoordinateEnumeration

set_option autoImplicit false
namespace ShiReversibleTM
variable {A B α : Type} {m n : Nat}

theorem ofFn_sum_equiv (left : A ≃ Fin m) (right : B ≃ Fin n) (f : A ⊕ B → α) :
    List.ofFn (fun i => f (((Equiv.sumCongr left right).trans finSumFinEquiv).symm i)) =
      List.ofFn (fun i => f (.inl (left.symm i))) ++ List.ofFn (fun j => f (.inr (right.symm j))) := by
  change List.ofFn (fun i => f ((Equiv.sumCongr left right).symm (finSumFinEquiv.symm i))) = _
  exact ofFn_sum_coordinates (fun a => f ((Equiv.sumCongr left right).symm a))

theorem ofFn_prod_equiv (left : A ≃ Fin m) (right : B ≃ Fin n) (f : A × B → α) :
    List.ofFn (fun i => f (((Equiv.prodCongr left right).trans finProdFinEquiv).symm i)) =
      (List.ofFn (fun i => List.ofFn (fun j => f (left.symm i, right.symm j)))).flatten := by
  change List.ofFn (fun i => f ((Equiv.prodCongr left right).symm (finProdFinEquiv.symm i))) = _
  exact ofFn_prod_coordinates (fun a => f ((Equiv.prodCongr left right).symm a))

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

set_option backward.isDefEq.respectTransparency false in
/-- The established configuration codec enumerates labels, memory, then fixed stack/cell/symbol ranks. -/
theorem configurationBitEquiv_ofFn (tm : Turing.FinTM2) (capacity : Nat)
    (f : ConfigurationBit tm capacity → α) :
    List.ofFn (fun i => f ((configurationBitEquiv tm capacity).symm i)) =
      (List.ofFn (fun j : Fin (Fintype.card (Option tm.Λ)) => f (.inl (.inl ((Fintype.equivFin (Option tm.Λ)).symm j))))) ++
      List.ofFn (fun j : Fin (Fintype.card tm.σ) => f (.inl (.inr ((Fintype.equivFin tm.σ).symm j)))) ++
      (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        List.ofFn (fun i : Fin capacity => List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
          f (.inr (((Fintype.equivFin tm.K).symm k, i), (Fintype.equivFin (Option (MachineSymbol tm))).symm a)))))).flatten.flatten := by
  classical
  dsimp only [configurationBitEquiv, configurationWidth]
  rw [ofFn_sum_equiv
    ((Equiv.sumCongr (Fintype.equivFin (Option tm.Λ)) (Fintype.equivFin tm.σ)).trans finSumFinEquiv)
    ((Equiv.prodCongr (stackCellEquiv tm capacity) (Fintype.equivFin (Option (MachineSymbol tm)))).trans finProdFinEquiv) f]
  rw [ofFn_sum_equiv (Fintype.equivFin (Option tm.Λ)) (Fintype.equivFin tm.σ) (fun a => f (.inl a))]
  rw [ofFn_prod_equiv (stackCellEquiv tm capacity) (Fintype.equivFin (Option (MachineSymbol tm))) (fun a => f (.inr a))]
  unfold stackCellEquiv
  rw [ofFn_prod_equiv (Fintype.equivFin tm.K) (Equiv.refl (Fin capacity))
    (fun ki => List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
      f (.inr (ki, (Fintype.equivFin (Option (MachineSymbol tm))).symm a))))]
  rfl

end ShiReversibleTM
