import ReversibleMachineUniformFamilyBounds

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleTM ShiReversibleFormula ShiReversibleGateBridge

noncomputable def castQState {a b : Nat} (h : a=b) (ψ : ShiShallow.QState a) : ShiShallow.QState b := h ▸ ψ

theorem castLayered_run {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a) (ψ : ShiShallow.QState a) :
    ShiShallow.runLayered (castLayered h gs) (castQState h ψ)=castQState h (ShiShallow.runLayered gs ψ) := by
  cases h
  rfl

noncomputable def machineSemanticWorkSize (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) : Nat :=
  let cap := n+budget*machinePushBound tm+1
  paddedFinishedSize (initialForest tm e₀ cap n) (tickForest tm cap) (extractionForest tm e₁ cap)
    17 (tickSizeBound tm) (extractionBitBound tm cap) budget

noncomputable def machineInputQState (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (x : Bits n) :
    ShiShallow.QState (machineSemanticWireCount tm e₀ e₁ n budget) :=
  flatBasis (inputMemory (k := machineSemanticWorkSize tm e₀ e₁ n budget) x,
    fun _ : Fin (extractionForest tm e₁ (n+budget*machinePushBound tm+1)).length => false)

noncomputable def machineOutputQState (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (f : List Bool → List Bool)
    (n budget : Nat) (x : Bits n) : ShiShallow.QState (machineSemanticWireCount tm e₀ e₁ n budget) :=
  flatBasis (inputMemory (k := machineSemanticWorkSize tm e₀ e₁ n budget) x,
    fun i : Fin (extractionForest tm e₁ (n+budget*machinePushBound tm+1)).length =>
      (outputCode (n+budget*machinePushBound tm+1) (f (List.ofFn x)))[i.val]?.getD false)

/-- Exact full-string output, preserved input and zero quantum workspace in the actual established family. -/
noncomputable def PaddedMachineFamilyClean (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) (f : List Bool → List Bool) : Prop :=
  ∀ n (x : Bits n),
    let h := machineSemanticWireCount_eq tm e₀ e₁ n ((n+c)^d)
    ShiShallow.runLayered ((paddedMachineUniformFamily tm e₀ e₁ c d).circ n)
      (castQState h (machineInputQState tm e₀ e₁ n ((n+c)^d) x))=
      castQState h (machineOutputQState tm e₀ e₁ f n ((n+c)^d) x)

theorem paddedMachineUniformFamily_clean {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (c d : Nat) (ht : M.time=(Polynomial.X+Polynomial.C c)^d) :
    PaddedMachineFamilyClean M.tm M.inputAlphabet M.outputAlphabet c d f := by
  intro n x
  dsimp only
  change ShiShallow.runLayered (castLayered _ _) (castQState _ _)=_
  rw [castLayered_run]
  apply congrArg (castQState (machineSemanticWireCount_eq M.tm M.inputAlphabet M.outputAlphabet n ((n+c)^d)))
  have hb : M.time.eval n = (n+c)^d := by
    rw [ht]
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  rw [← hb]
  exact polyTime_paddedMachineQuantumCircuit_clean M n x

end ShiReversibleGenerator
