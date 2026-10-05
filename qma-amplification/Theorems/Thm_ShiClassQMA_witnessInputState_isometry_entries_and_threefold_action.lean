-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.witnessInputState_isometry_entries_and_threefold_action`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_witnessInputState_isometry_entries_and_threefold_action`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiTensor_tensor_split_append_inverse

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem witnessInputState_isometry_entries_and_threefold_action {n : ℕ} (F : QMAFamily) (x : Bits n)
    (W : Matrix (Bits (n + (F.wit n + (F.anc n + 1))))
                (Bits (F.wit n)) ℂ)
    (hW : ∀ ψ : QState (F.wit n),
            Matrix.mulVec W ψ = witnessInputState F x ψ) :
    (∀ (y : Bits (n + (F.wit n + (F.anc n + 1))))
        (u : Bits (F.wit n)),
        W y u
          = if ((∀ i : Fin n, y (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
                (∀ l : Fin (F.anc n + 1), y (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
              ∧ (fun j : Fin (F.wit n) => y (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))) = u
            then 1 else 0)
    ∧ (∀ Θ : QState (F.wit n + F.wit n + F.wit n),
        Matrix.mulVec
            (Matrix.of fun
                (Y : Bits
                  (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))
                    + (n + (F.wit n + (F.anc n + 1)))))
                (U : Bits (F.wit n + F.wit n + F.wit n)) =>
              W (ShiTensor.leftBits (ShiTensor.leftBits Y))
                  (ShiTensor.leftBits (ShiTensor.leftBits U))
                * W (ShiTensor.rightBits (ShiTensor.leftBits Y))
                    (ShiTensor.rightBits (ShiTensor.leftBits U))
                * W (ShiTensor.rightBits Y) (ShiTensor.rightBits U)) Θ
          = fun Y =>
              if ((∀ i : Fin n,
                     ShiTensor.leftBits (ShiTensor.leftBits Y)
                       (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
                   (∀ l : Fin (F.anc n + 1),
                     ShiTensor.leftBits (ShiTensor.leftBits Y)
                       (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
                  ∧ ((∀ i : Fin n,
                        ShiTensor.rightBits (ShiTensor.leftBits Y)
                          (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
                      (∀ l : Fin (F.anc n + 1),
                        ShiTensor.rightBits (ShiTensor.leftBits Y)
                          (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
                  ∧ ((∀ i : Fin n,
                        ShiTensor.rightBits Y
                          (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
                      (∀ l : Fin (F.anc n + 1),
                        ShiTensor.rightBits Y
                          (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
              then Θ (Fin.append
                    (Fin.append
                      (fun j : Fin (F.wit n) =>
                        ShiTensor.leftBits (ShiTensor.leftBits Y)
                          (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j)))
                      (fun j : Fin (F.wit n) =>
                        ShiTensor.rightBits (ShiTensor.leftBits Y)
                          (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))))
                    (fun j : Fin (F.wit n) =>
                      ShiTensor.rightBits Y
                        (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))))
              else 0) := by
  sorry

end ShiClassQMA
