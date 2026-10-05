import «AMPUNI-layout-residual-exact»
import Theorems.Thm_ShiTM_stack_supplied_index_emitter_block
import Theorems.Thm_ShiTM_piece_list_reload_pass

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

private theorem iter3 {α : Type} (f : α → α) (a b c : Nat) (x y z u : α)
    (h1 : f^[a] x = y) (h2 : f^[b] y = z) (h3 : f^[c] z = u) :
    f^[a + b + c] x = u := by
  rw [show a + b + c = c + (b + a) from by omega,
    Function.iterate_add_apply f c (b + a), Function.iterate_add_apply f b a,
    h1, h2, h3]

/-- The accepted layout arm with an exact cost depending only on the piece layout, raw
wire, tag and fixed mirrors.  This strengthens `layoutRunner` precisely at the point
needed by the nested iterator. -/
theorem layoutRunnerExact (t : Fin 5) (rtag : List Cell)
    (ps : List (Nat × Nat)) (w : Nat)
    (pa ta pb tb : List Cell) (v : Sig) (S : ∀ k, List (Gam k))
    (hw : w < (ps.map Prod.fst).sum)
    (hSv : S (layoutStack 0) = List.replicate w .mark)
    (hSl : S (layoutStack 1) = pieceCells Prod.fst ps)
    (hSb : S (layoutStack 2) = pieceCells Prod.snd ps)
    (hSd : S (layoutStack 3) = [])
    (hSu : S (layoutStack 4) = [.delim])
    (hStag : S (layoutStack 7) = tagCell t :: rtag)
    (hSml : S (layoutStack 8) = pa ++ .mirrorEnd :: ta)
    (hSmb : S (layoutStack 9) = pb ++ .mirrorEnd :: tb)
    (hSs : S (layoutStack 10) = [])
    (hpla : (List.map id pa).reverse = pieceCells Prod.fst ps)
    (hplb : (List.map id pb).reverse = pieceCells Prod.snd ps)
    (h1ca : ∀ (u : Sig) (y : Cell), y ∈ pa → notMirrorEnd (pop u (some y)) = true)
    (hstpa : ∀ u : Sig, notMirrorEnd (pop u (some .mirrorEnd)) = false)
    (h1cb : ∀ (u : Sig) (y : Cell), y ∈ pb → notMirrorEnd (pop u (some y)) = true)
    (hstpb : ∀ u : Sig, notMirrorEnd (pop u (some .mirrorEnd)) = false) :
    ∃ v' T,
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[cost ps w
          + (depth ps w + t.val + 3)
          + (residualPiece ps w + residualBase ps w
              + 2 * (pa.length + pb.length) + 8)]
        (some { l := some (b .wire), var := v, stk := S })
        = some { l := some (b .done), var := v', stk := T }
      ∧ T (layoutStack 6)
          = (ShiBQP.encNat t.val ++ ShiBQP.encNat (depth ps w)).map bit
              ++ S (layoutStack 6)
      ∧ T (layoutStack 4) = [.delim]
      ∧ T (layoutStack 0) = []
      ∧ T (layoutStack 1) = pieceCells Prod.fst ps
      ∧ T (layoutStack 2) = pieceCells Prod.snd ps
      ∧ T (layoutStack 7) = rtag
      ∧ T (layoutStack 8) = S (layoutStack 8)
      ∧ T (layoutStack 9) = S (layoutStack 9)
      ∧ T (layoutStack 10) = []
      ∧ T (layoutStack 3) = []
      ∧ residualPiece ps w ≤ (pieceCells Prod.fst ps).length
      ∧ residualBase ps w ≤ (pieceCells Prod.snd ps).length
      ∧ (∀ k, (∀ i : Fin 11, k ≠ layoutStack i) → T k = S k) := by
  rcases program_equations t with
    ⟨hwire, hafterPiece, hafterBase, hfinishPiece, hfinishBase,
      hdispatch, hemitDelim, hemitIndex, hmark, hjoin,
      hreloadPiece, hreloadPieceMirror, hreloadPieceSentinel, hreloadPieceRestore,
      hreloadBase, hreloadBaseMirror, hreloadBaseSentinel, hreloadBaseRestore⟩
  have e0 : layoutStack (0 : Fin 11) = (0 : Fin 14) := by apply Fin.ext; rfl
  have e1 : layoutStack (1 : Fin 11) = (1 : Fin 14) := by apply Fin.ext; rfl
  have e2 : layoutStack (2 : Fin 11) = (2 : Fin 14) := by apply Fin.ext; rfl
  have e4 : layoutStack (4 : Fin 11) = (4 : Fin 14) := by apply Fin.ext; rfl
  have e6 : layoutStack (6 : Fin 11) = (6 : Fin 14) := by apply Fin.ext; rfl
  have e7 : layoutStack (7 : Fin 11) = (7 : Fin 14) := by apply Fin.ext; rfl
  obtain ⟨v1, T1, hrun1, hT1u, hT1v, hT1d, hT1l, hT1b,
      hr1, hr2, hT1ll, hT1bl, hT1fr⟩ :=
    exactWireRunner ps w v S hw hSv hSl hSb hSd
  have hT1tag : T1 (layoutStack 7) = tagCell t :: rtag := by
    rw [hT1fr (layoutStack 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hStag
  have hT1idx : T1 (layoutStack 4) = List.replicate (depth ps w) .mark ++ [.delim] := by
    rw [e4] at hSu ⊢
    rw [hT1u, hSu]
  obtain ⟨v2, T2, hrun2, hT2o, hT2i, hT2t, hT2fr, _, _⟩ :=
    ShiTM.stack_supplied_index_emitter_block.1
      machine (by decide) (by decide) (by decide)
      .mark .delim .mark .delim bit (depth ps w) t.val [] (tagCell t) rtag v1 T1
      rfl rfl hdispatch hemitDelim hemitIndex hmark
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl (dispatch_tag t)
      hT1tag hT1idx
  rw [hjoin] at hrun2
  have hT2ml : T2 (layoutStack 8) = pa ++ .mirrorEnd :: ta := by
    rw [hT2fr (layoutStack 8) (by decide) (by decide) (by decide),
      hT1fr (layoutStack 8) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hSml
  have hT2mb : T2 (layoutStack 9) = pb ++ .mirrorEnd :: tb := by
    rw [hT2fr (layoutStack 9) (by decide) (by decide) (by decide),
      hT1fr (layoutStack 9) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hSmb
  have hT2s : T2 (layoutStack 10) = [] := by
    rw [hT2fr (layoutStack 10) (by decide) (by decide) (by decide),
      hT1fr (layoutStack 10) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hSs
  obtain ⟨v3, T3, hrun3, hT3l, hT3b, hT3ml, hT3mb, hT3s, hT3fr, _, _, _, _, _⟩ :=
    ShiTM.piece_list_reload_pass.1
      machine
      (kl := layoutStack 1) (kb := layoutStack 2)
      (kml := layoutStack 8) (kmb := layoutStack 9)
      (ks := layoutStack 10) (kd := layoutStack 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      id id id id id id id id
      hreloadPiece hreloadPieceMirror hreloadPieceSentinel hreloadPieceRestore
      hreloadBase hreloadBaseMirror hreloadBaseSentinel hreloadBaseRestore
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      .mirrorEnd (fun _ => rfl) .mirrorEnd (fun _ => rfl)
      pa ta h1ca hstpa pb tb h1cb hstpb
      (pieceCells Prod.fst) (pieceCells Prod.snd) ps hpla hplb v2 T2 hT2ml hT2mb hT2s
  have hT2l : T2 (layoutStack 1) = T1 (layoutStack 1) :=
    hT2fr _ (by decide) (by decide) (by decide)
  have hT2b : T2 (layoutStack 2) = T1 (layoutStack 2) :=
    hT2fr _ (by decide) (by decide) (by decide)
  have hlen1 : (T2 (layoutStack 1)).length = residualPiece ps w := by
    rw [hT2l, e1, hT1l]
    rfl
  have hlen2 : (T2 (layoutStack 2)).length = residualBase ps w := by
    rw [hT2b, e2, hT1b]
    rfl
  have hchain := iter3 _ _ _ _ _ _ _ _ hrun1 hrun2 hrun3
  rw [hlen1, hlen2] at hchain
  have hT2d : T2 (layoutStack 3) = [] := by
    rw [hT2fr (layoutStack 3) (by decide) (by decide) (by decide)]
    exact hT1d
  have hT3d : T3 (layoutStack 3) = [] := by
    rw [hT3fr (layoutStack 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hT2d
  refine ⟨v3, T3, hchain, ?_, ?_, ?_, hT3l, hT3b, ?_, ?_, ?_, hT3s, hT3d,
    hr1, hr2, ?_⟩
  · rw [hT3fr (layoutStack 6) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), e6, hT2o,
      hT1fr (6 : Fin 14) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
  · rw [hT3fr (layoutStack 4) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    rw [e4]
    exact hT2i
  · rw [hT3fr (layoutStack 0) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hT2fr (layoutStack 0) (by decide) (by decide) (by decide), e0]
    exact hT1v
  · rw [hT3fr (layoutStack 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    rw [e7]
    exact hT2t
  · rw [hT3ml, hT2fr (layoutStack 8) (by decide) (by decide) (by decide),
      hT1fr (layoutStack 8) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
  · rw [hT3mb, hT2fr (layoutStack 9) (by decide) (by decide) (by decide),
      hT1fr (layoutStack 9) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
  · intro k hk
    rw [hT3fr k (hk 1) (hk 2) (hk 8) (hk 9) (hk 10) (hk 5),
      hT2fr k (hk 7) (hk 4) (hk 6),
      hT1fr k (hk 0) (hk 1) (hk 2) (hk 3) (hk 4) (hk 5)]

end ShiTMLayoutMachine
