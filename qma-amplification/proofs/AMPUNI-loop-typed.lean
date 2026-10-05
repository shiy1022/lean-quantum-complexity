import «AMPUNI-loop-records»
import «AMPUNI-raw-layout-contract»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- Each typed gate becomes a bounded source record at its copy's wire offset. -/
def typedRecord (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) : Instr m → SourceRecord ps
  | .h i => .single 0 (by decide) (off + i.val) (by omega)
  | .s i => .single 1 (by decide) (off + i.val) (by omega)
  | .t i => .single 2 (by decide) (off + i.val) (by omega)
  | .x i => .single 3 (by decide) (off + i.val) (by omega)
  | .cnot i j _ => .cnot (off + i.val) (off + j.val) (by omega) (by omega)

theorem typedRecord_source (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (g : Instr m) :
    (typedRecord ps off hfit g).source =
      (ShiTMRawLayout.encode
        (ShiTMRawLayout.mapOperands (fun _ x => x) ps off (ShiTMRawLayout.ofInstr g))).map bit := by
  cases g <;> rfl

theorem typedRecord_target (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (g : Instr m) :
    (typedRecord ps off hfit g).target =
      (ShiTMRawLayout.encode
        (ShiTMRawLayout.mapOperands depth ps off (ShiTMRawLayout.ofInstr g))).map bit := by
  cases g <;> rfl

theorem typedRecord_sourceList (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (gs : List (Instr m)) :
    SourceRecord.sourceList (gs.map (typedRecord ps off hfit)) =
      ((gs.map (fun g => ShiTMRawLayout.encode
        (ShiTMRawLayout.mapOperands (fun _ x => x) ps off (ShiTMRawLayout.ofInstr g)))).flatten).map bit := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [SourceRecord.sourceList, typedRecord_source, ih, List.map_append]

theorem typedRecord_targetList (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (gs : List (Instr m)) :
    SourceRecord.targetList (gs.map (typedRecord ps off hfit)) =
      ((gs.map (fun g => ShiTMRawLayout.encode
        (ShiTMRawLayout.mapOperands depth ps off (ShiTMRawLayout.ofInstr g)))).flatten).map bit := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [SourceRecord.targetList, typedRecord_target, ih, List.map_append]

end ShiTMLayoutMachine
