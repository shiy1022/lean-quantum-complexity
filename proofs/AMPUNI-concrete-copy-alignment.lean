import «AMPUNI-complete-copy-encodings»
import Definitions.Def_ShiClassQMAAmpX

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp ShiClassQMAAmpX

namespace ShiTMCompleteController

open ShiTMLayoutMachine

private theorem ampE_injective (n w a off : Nat)
    (hoff : off + (n + (w + (a + 1))) ≤
      3 * (n + (w + (a + 1)))) :
    Function.Injective (ampE n w a off hoff) := by
  have hs : Function.Injective (ampSig n w a) :=
    (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1.injective
  have he : Function.Injective
      (ampEmb (n + (w + (a + 1))) off hoff) := by
    intro x y hxy
    have hv := congrArg Fin.val hxy
    change off + x.val = off + y.val at hv
    exact Fin.val_injective (by omega)
  exact hs.comp he

/-- The three verifier-copy terms appearing, in order, in `ampCircX`. -/
noncomputable def embeddedCopy0 (F : ShiClassQMA.QMAFamily) (n : Nat) :
    Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))) :=
  ShiEmbed.embedCirc
    (ampE n (F.wit n) (F.anc n) 0 (by omega))
    (ampE_injective n (F.wit n) (F.anc n) 0 (by omega)) (F.circ n)

noncomputable def embeddedCopy1 (F : ShiClassQMA.QMAFamily) (n : Nat) :
    Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))) :=
  ShiEmbed.embedCirc
    (ampE n (F.wit n) (F.anc n)
      (n + (F.wit n + (F.anc n + 1))) (by omega))
    (ampE_injective n (F.wit n) (F.anc n)
      (n + (F.wit n + (F.anc n + 1))) (by omega)) (F.circ n)

noncomputable def embeddedCopy2 (F : ShiClassQMA.QMAFamily) (n : Nat) :
    Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))) :=
  ShiEmbed.embedCirc
    (ampE n (F.wit n) (F.anc n)
      (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega))
    (ampE_injective n (F.wit n) (F.anc n)
      (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega)) (F.circ n)

theorem ampCircX_exact_copies (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ampCircX F n =
      ampFan2X n (F.wit n) (F.anc n) ++
      ampFan3X n (F.wit n) (F.anc n) ++
      embeddedCopy0 F n ++ embeddedCopy1 F n ++ embeddedCopy2 F n ++
      ampReadX n (F.wit n) (F.anc n) (F.out n) := by
  rfl

theorem firstCopyBytes_eq_exact_copy (F : ShiClassQMA.QMAFamily) (n : Nat) :
    firstCopyBytes F n = (ShiBQP.encCirc (embeddedCopy0 F n)).map bit := by
  simpa only [embeddedCopy0] using
    firstCopyBytes_eq_embedCirc F n (by omega)
      (ampE_injective n (F.wit n) (F.anc n) 0 (by omega))

theorem copy1Bytes_eq_exact_copy (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMCopyStageWithSkip.copyBytes 1 F n =
      (ShiBQP.encCirc (embeddedCopy1 F n)).map bit := by
  simpa only [embeddedCopy1] using
    copy1Bytes_eq_embedCirc F n (by omega)
      (ampE_injective n (F.wit n) (F.anc n)
        (n + (F.wit n + (F.anc n + 1))) (by omega))

theorem copy2Bytes_eq_exact_copy (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMCopyStageWithSkip.copyBytes 2 F n =
      (ShiBQP.encCirc (embeddedCopy2 F n)).map bit := by
  simpa only [embeddedCopy2] using
    copy2Bytes_eq_embedCirc F n (by omega)
      (ampE_injective n (F.wit n) (F.anc n)
        (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega))

end ShiTMCompleteController
