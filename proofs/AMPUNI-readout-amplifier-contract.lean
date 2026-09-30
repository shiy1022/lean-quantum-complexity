import «AMPUNI-readout-contract»
import «AMPUNI-copy-local-blocks»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMReadout
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMCircuitNormalization
open ShiClassQMAAmp ShiClassQMAAmpX

/-- Computable wire values from the same four-piece local layouts used by
the three circuit-copy passes. The original output index may be any wire. -/
def amplifierValues (n w a : Nat) (v : Nat) : Fin 4 → Nat :=
  ![ShiTMLayoutMachine.depth (copyPieces0 n w a) v,
    ShiTMLayoutMachine.depth (copyPieces1 n w a) v,
    ShiTMLayoutMachine.depth (copyPieces2 n w a) v,
    3*n+3*w+3*a+3]

private theorem scratch_val (n w a : Nat) : (ampScr n w a).val = 3*n+3*w+3*a+3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ :=
    Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)
  apply hs
  rfl

theorem amplifierValues_eq (n w a : Nat) (v : Fin (n+(w+(a+1)))) :
    amplifierValues n w a v.val =
      ![(ampE n w a 0 (by omega) v).val,
        (ampE n w a (n+(w+(a+1))) (by omega) v).val,
        (ampE n w a (2*(n+(w+(a+1)))) (by omega) v).val,
        (ampScr n w a).val] := by
  have h0 : ShiTMLayoutMachine.depth (copyPieces0 n w a) v.val =
      (ampE n w a 0 (by omega) v).val := by
    rw [depth_copy0_global n w a v.val v.isLt]
    simpa using depth_ampPieces_eq_ampE n w a 0 (by omega) v
  have h1 : ShiTMLayoutMachine.depth (copyPieces1 n w a) v.val =
      (ampE n w a (n+(w+(a+1))) (by omega) v).val := by
    rw [depth_copy1_global n w a v.val v.isLt]
    exact depth_ampPieces_eq_ampE n w a _ _ v
  have h2 : ShiTMLayoutMachine.depth (copyPieces2 n w a) v.val =
      (ampE n w a (2*(n+(w+(a+1)))) (by omega) v).val := by
    rw [depth_copy2_global n w a v.val v.isLt]
    exact depth_ampPieces_eq_ampE n w a _ _ v
  simp only [amplifierValues, h0, h1, h2, scratch_val]

theorem programBytes_ampReadX (n w a : Nat) (v : Fin (n+(w+(a+1)))) :
    programBytes (amplifierValues n w a v.val) = (stripCircPrefix (ampReadX n w a v)).map bit := by
  unfold ampReadX
  rw [← programBytes_readCirc, amplifierValues_eq]

/-- The readout emitter targets the actual amplifier circuit at its arbitrary
original output wire. Preparing the four computed unary registers is the
remaining executable input obligation of this subroutine. -/
theorem amplifier_readout_run (n w a : Nat) (out : Fin (n+(w+(a+1))))
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (wire h) = List.replicate (amplifierValues n w a out.val h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost (amplifierValues n w a out.val) program+1]
        (some ⟨some (.dispatch 0), v, S⟩) = some ⟨some .finished, v', U⟩
      ∧ U output = ((stripCircPrefix (ampReadX n w a out)).map bit).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  obtain ⟨U, v', hr, ho, hf⟩ := program_run _ v S hvalues ht
  exact ⟨U, v', hr, by simpa only [programBytes_ampReadX] using ho, hf⟩

theorem amplifierValues_le (n w a : Nat) (v : Fin (n+(w+(a+1)))) (h : Fin 4) :
    amplifierValues n w a v.val h ≤ 3*n+3*w+3*a+3 := by
  rw [amplifierValues_eq]
  have h0 := (ampE n w a 0 (by omega) v).isLt
  have h1 := (ampE n w a (n+(w+(a+1))) (by omega) v).isLt
  have h2 := (ampE n w a (2*(n+(w+(a+1)))) (by omega) v).isLt
  have hs := (ampScr n w a).isLt
  fin_cases h <;> simp <;> omega

theorem family_readout_cost_le (F : ShiClassQMA.QMAFamily) (n : Nat) :
    let L := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length
    scheduleCost (amplifierValues n (F.wit n) (F.anc n) (F.out n).val) program+1 ≤ 3631*L := by
  let L := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length
  have hlen : n+F.wit n+F.anc n+1 ≤ L := by
    dsimp [L]
    simp only [ShiClassQMAU.encQMAFamilyAt, ShiBQP.encNat,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have h := program_cost_le (amplifierValues n (F.wit n) (F.anc n) (F.out n).val)
    (3*n+3*F.wit n+3*F.anc n+3)
    (fun k => amplifierValues_le n (F.wit n) (F.anc n) (F.out n) k)
  change _ ≤ 3631*L
  omega

end ShiTMReadout
