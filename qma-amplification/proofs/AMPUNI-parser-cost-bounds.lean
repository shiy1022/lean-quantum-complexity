import «AMPUNI-nested-circuit-layers»
import «AMPUNI-copy-local-blocks»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace ShiTMParserCost
open ShiTMLayoutMachine

/-- A common linear measure of the unary layout tables. -/
def tableSize (ps : List (Nat × Nat)) : Nat :=
  (ps.map (fun p => p.1 + p.2 + 3)).sum

theorem widths_le (ps : List (Nat × Nat)) :
    (ps.map Prod.fst).sum ≤ tableSize ps := by
  induction ps with
  | nil => simp [tableSize]
  | cons p ps ih =>
      simp only [tableSize, List.map_cons, List.sum_cons] at *
      omega

theorem pieces_le (ps : List (Nat × Nat)) :
    (ps.map (fun p => p.1 + 1)).sum ≤ tableSize ps := by
  induction ps with
  | nil => simp [tableSize]
  | cons p ps ih =>
      simp only [tableSize, List.map_cons, List.sum_cons] at *
      omega

theorem bases_le (ps : List (Nat × Nat)) :
    (ps.map (fun p => p.2 + 1)).sum ≤ tableSize ps := by
  induction ps with
  | nil => simp [tableSize]
  | cons p ps ih =>
      simp only [tableSize, List.map_cons, List.sum_cons] at *
      omega

theorem depth_le (ps : List (Nat × Nat)) (w : Nat) :
    depth ps w ≤ tableSize ps := by
  induction ps generalizing w with
  | nil => simp [depth, tableSize]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      have ht := ih (w-a)
      simp only [tableSize] at ht
      simp only [depth, tableSize, List.map_cons, List.sum_cons]
      split <;> omega

theorem lookup_cost_le (ps : List (Nat × Nat)) (w : Nat) :
    cost ps w ≤ 2 * tableSize ps := by
  induction ps generalizing w with
  | nil => simp [cost, tableSize]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      have ht := ih (w-a)
      simp only [tableSize] at ht
      simp only [cost, tableSize, List.map_cons, List.sum_cons]
      split <;> omega

theorem residual_piece_le (ps : List (Nat × Nat)) (w : Nat) :
    residualPiece ps w ≤ (ps.map (fun p => p.1+1)).sum := by
  have hs := Classical.choose_spec
    (Classical.choose_spec ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact)
  induction ps generalizing w with
  | nil =>
      have hz : residualPiece [] w = 0 := hs.1 w
      simp [hz]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      have he : residualPiece ((a,b)::ps) w =
          if w<a then (a-w)+(ps.map (fun p => p.1+1)).sum
          else residualPiece ps (w-a) := hs.2.1 a b ps w
      have ht := ih (w-a)
      rw [he]
      simp only [List.map_cons, List.sum_cons]
      split <;> omega

theorem residual_base_le (ps : List (Nat × Nat)) (w : Nat) :
    residualBase ps w ≤ (ps.map (fun p => p.2+1)).sum := by
  have hs := Classical.choose_spec
    (Classical.choose_spec ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact)
  induction ps generalizing w with
  | nil =>
      have hz : residualBase [] w = 0 := hs.2.2.1 w
      simp [hz]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      have he : residualBase ((a,b)::ps) w =
          if w<a then (ps.map (fun p => p.2+1)).sum
          else residualBase ps (w-a) := hs.2.2.2.1 a b ps w
      have ht := ih (w-a)
      rw [he]
      simp only [List.map_cons, List.sum_cons]
      split <;> omega

theorem one_index_cost_le (t : Fin 5) (ps : List (Nat × Nat)) (i : Nat)
    (pa pb : List Cell) (hi : i < (ps.map Prod.fst).sum)
    (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    oneIndexCost t ps i pa pb ≤ 12 * tableSize ps + 30 := by
  have hw := widths_le ps
  have hd := depth_le ps i
  have hc := lookup_cost_le ps i
  have hrp := (residual_piece_le ps i).trans (pieces_le ps)
  have hrb := (residual_base_le ps i).trans (bases_le ps)
  have ht := t.isLt
  have hlen : (encodedChunk t ps i).length = t.val + depth ps i + 2 := by
    simp [encodedChunk, ShiBQP.encNat] <;> omega
  simp only [oneIndexCost, hlen]
  omega

theorem cnot_cost_le (ps : List (Nat × Nat)) (i j : Nat)
    (pa pb : List Cell) (hi : i < (ps.map Prod.fst).sum)
    (hj : j < (ps.map Prod.fst).sum)
    (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    cnotArmCost ps i j pa pb ≤ 30 * tableSize ps + 60 := by
  have hw := widths_le ps
  have hdi := depth_le ps i
  have hdj := depth_le ps j
  have hci := lookup_cost_le ps i
  have hcj := lookup_cost_le ps j
  have hrpi := (residual_piece_le ps i).trans (pieces_le ps)
  have hrpj := (residual_piece_le ps j).trans (pieces_le ps)
  have hrbi := (residual_base_le ps i).trans (bases_le ps)
  have hrbj := (residual_base_le ps j).trans (bases_le ps)
  have hlen : (cnotChunk ps i j).length = depth ps i + depth ps j + 7 := by
    simp [cnotChunk, ShiBQP.encNat] <;> omega
  simp only [cnotArmCost, hlen]
  omega

/-- Every well-scoped source instruction has a linear cost in table size,
provided the two mirrors have the corresponding bounded lengths. -/
theorem record_cost_le (ps : List (Nat × Nat)) (r : SourceRecord ps)
    (pa pb : List Cell) (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    r.cost pa pb ≤ 30 * tableSize ps + 80 := by
  cases r with
  | single t ht i hi =>
      have h := one_index_cost_le t ps i pa pb hi ha hb
      simp only [SourceRecord.cost]
      omega
  | cnot i j hi hj =>
      have h := cnot_cost_le ps i j pa pb hi hj ha hb
      simp only [SourceRecord.cost]
      omega

theorem copy0_table_size_le (n w a : Nat) :
    tableSize (copyPieces0 n w a) ≤ 20 * (n+w+a+1) := by
  simp [tableSize, copyPieces0]
  omega

theorem copy1_table_size_le (n w a : Nat) :
    tableSize (copyPieces1 n w a) ≤ 20 * (n+w+a+1) := by
  simp [tableSize, copyPieces1]
  omega

theorem copy2_table_size_le (n w a : Nat) :
    tableSize (copyPieces2 n w a) ≤ 20 * (n+w+a+1) := by
  simp [tableSize, copyPieces2]
  omega

open ShiTMOuterLift

theorem gate_list_cost_le (ps : List (Nat × Nat)) (rs : List (SourceRecord ps))
    (pa pb : List Cell) (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    gateListCost pa pb rs ≤ (30 * tableSize ps + 82) * rs.length + 1 := by
  induction rs with
  | nil => simp [gateListCost]
  | cons r rs ih =>
      have hr := record_cost_le ps r pa pb ha hb
      simp only [gateListCost, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem layer_list_cost_le (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps))) (pa pb : List Cell)
    (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    layerListCost pa pb layers ≤
      (30 * tableSize ps + 83) * (layers.map List.length).sum + 3 * layers.length + 1 := by
  induction layers with
  | nil => simp [layerListCost]
  | cons layer layers ih =>
      have hg := gate_list_cost_le ps layer pa pb ha hb
      simp only [layerListCost, List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
      omega

theorem layer_counts_le_source_length (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps))) :
    (layers.map List.length).sum + layers.length ≤ (sourceLayers layers).length := by
  induction layers with
  | nil => simp [sourceLayers]
  | cons layer layers ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, sourceLayers,
        sourceLayer, List.length_append, List.length_map, ShiBQP.encNat,
        List.length_replicate, List.length_nil] at *
      omega

/-- The complete layer parser has a numerical bound linear in encoded payload
length and table size. Instantiating the fixed copy tables yields a quadratic
input-size bound; this lemma alone does not assert malformed-input termination. -/
theorem layer_cost_le_source_length (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps))) (pa pb : List Cell)
    (ha : pa.length ≤ tableSize ps) (hb : pb.length ≤ tableSize ps) :
    layerListCost pa pb layers ≤
      (30 * tableSize ps + 86) * (sourceLayers layers).length + 1 := by
  have hc := layer_counts_le_source_length ps layers
  have hg : (layers.map List.length).sum ≤ (sourceLayers layers).length := by omega
  have hl : layers.length ≤ (sourceLayers layers).length := by omega
  calc
    layerListCost pa pb layers ≤
        (30 * tableSize ps + 83) * (layers.map List.length).sum + 3 * layers.length + 1 :=
      layer_list_cost_le ps layers pa pb ha hb
    _ ≤ (30 * tableSize ps + 83) * (sourceLayers layers).length +
        3 * (sourceLayers layers).length + 1 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ hg)
        (Nat.mul_le_mul_left _ hl)) 1
    _ = (30 * tableSize ps + 86) * (sourceLayers layers).length + 1 := by
      simp only [Nat.add_mul]
      omega

theorem piece_cells_length (f : Nat × Nat → Nat) (ps : List (Nat × Nat)) :
    (pieceCells f ps).length = (ps.map (fun p => f p + 1)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pieceCells, ih, Nat.add_assoc] <;> omega

/-- With the actual reversed table mirrors, only numerical size bounds remain.
For the three fixed copy tables, the table bound is supplied above. -/
theorem layer_cost_with_mirrors_le_quadratic (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps))) (L : Nat)
    (hB : tableSize ps ≤ 20 * L) (hL : (sourceLayers layers).length ≤ L) :
    layerListCost (pieceCells Prod.fst ps).reverse (pieceCells Prod.snd ps).reverse layers ≤
      (600 * L + 86) * L + 1 := by
  have ha : ((pieceCells Prod.fst ps).reverse).length ≤ tableSize ps := by
    simpa only [List.length_reverse, piece_cells_length] using pieces_le ps
  have hb : ((pieceCells Prod.snd ps).reverse).length ≤ tableSize ps := by
    simpa only [List.length_reverse, piece_cells_length] using bases_le ps
  have hk : 30 * tableSize ps + 86 ≤ 600 * L + 86 := by omega
  exact (layer_cost_le_source_length ps layers _ _ ha hb).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hk hL) 1)

end ShiTMParserCost
