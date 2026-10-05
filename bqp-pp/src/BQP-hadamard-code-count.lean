import «BQP-opcode-count»
import «BQP-family-compiler»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BQPOpcodeCount
open Turing Turing.TM2 BQPProgram

def opcodeReg (c : ℕ) : Reg :=
  (decide (c / 8 % 2 = 1), decide (c / 4 % 2 = 1),
    decide (c / 2 % 2 = 1), decide (c % 2 = 1))
def codeCount (p : List ℕ) : ℕ := (p.map (fun c => if selected (opcodeReg c) then 1 else 0)).sum

theorem encode_regs (p : List ℕ) :
    BQPOpcodeEmission.encode p =
      ((p.reverse.map opcodeReg).map (fun r => [r.1,r.2.1,r.2.2.1,r.2.2.2])).flatten := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      simp only [BQPOpcodeEmission.encode, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, ← ih]
      rfl

theorem encoded_run (C : Checker) (p : List ℕ) (out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run program)^[p.length+1] (some (cfg v (C.encode p) out)) =
      some (⟨none,zero,tapes [] (List.replicate (codeCount p) true ++ out)⟩ : Cfg Gam Unit Reg) := by
  rw [checker_encode_eq, encode_regs]
  simpa only [List.length_map, List.length_reverse, List.map_map, List.map_reverse,
    List.sum_reverse, Function.comp_def, codeCount] using blocks_run (p.reverse.map opcodeReg) out v

@[simp] theorem codeCount_append (p q : List ℕ) : codeCount (p++q) = codeCount p + codeCount q := by
  simp [codeCount]
@[simp] theorem codeCount_replicate_zero (n : ℕ) : codeCount (List.replicate n 0) = 0 := by
  simp [codeCount, opcodeReg, selected]
@[simp] theorem codeCount_replicate_one (n : ℕ) : codeCount (List.replicate n 1) = 0 := by
  simp [codeCount, opcodeReg, selected]
@[simp] theorem codeCount_wrap (n : ℕ) (body : List ℕ) : codeCount (wrap n body) = codeCount body := by
  simp [wrap]

theorem codeCount_gate {n : ℕ} (g : ShiShallow.Instr n) :
    codeCount (gateBlock g) = (if (match g with | .h _ => true | _ => false) then 1 else 0) := by
  cases g with
  | h i => simp [gateBlock, codeCount, wrap, opcodeReg, selected]
  | s i => simp [gateBlock, codeCount, wrap, opcodeReg, selected]
  | t i => simp [gateBlock, codeCount, wrap, opcodeReg, selected]
  | x i => simp [gateBlock, codeCount, wrap, opcodeReg, selected]
  | cnot i j hij =>
      simp only [gateBlock]
      split <;> simp [codeCount, wrap, opcodeReg, selected]

theorem codeCount_forward {n : ℕ} (gs : List (ShiShallow.Instr n)) :
    codeCount (forwardBody gs) = BQPPaths.hadamardCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change codeCount (gateBlock g ++ forwardBody gs) = _
      rw [codeCount_append, codeCount_gate, ih]
      cases g <;> simp [BQPPaths.hadamardCount, Nat.add_comm]

abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 1
  Γ := Gam
  Λ := Unit
  main := ()
  ΛFin := inferInstance
  σ := Reg
  initialState := zero
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) : initList machine s = cfg zero s [] := by
  apply congrArg (fun S => (⟨some (),zero,S⟩ : Cfg Gam Unit Reg))
  funext k; fin_cases k <;> rfl

theorem final_eq (s : List Bool) :
    (⟨none,zero,tapes [] s⟩ : Cfg Gam Unit Reg) = haltList machine s := by
  apply congrArg (fun S => (⟨none,zero,S⟩ : Cfg Gam Unit Reg))
  funext k; fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (C : Checker) (p : List ℕ) : TM2OutputsInTime machine (C.encode p)
    (some (List.replicate (codeCount p) true)) (p.length+1) := by
  refine { steps := p.length+1, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[p.length+1] (some (initList machine (C.encode p))) =
    some (haltList machine _)
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil] using encoded_run C p [] zero

theorem family_typed (C : Checker) (F : ShiClass.Family) :
    Nonempty (TM2ComputableInPolyTime
      (fun n => C.encode (forwardBody (F.circ n).flatten)) id
      (fun n => List.replicate (BQPPaths.hadamardCount (F.circ n).flatten) true)) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro n
  have h := outputs C (forwardBody (F.circ n).flatten)
  have ht : h.steps ≤ (C.encode (forwardBody (F.circ n).flatten)).length+1 := by
    have hb := h.steps_le_m
    rw [C.encode_length]
    omega
  simpa only [TM2OutputsInTime, id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    codeCount_forward] using ({ h with steps_le_m := ht } : TM2OutputsInTime _ _ _ _)

/-- Unary Hadamard count computed from the actual uniform-family circuit. -/
theorem family_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => List.replicate (familyH F x) true) := by
  have h := BQPTypedPolyTime.comp (BQPFamilyPasses.circuit_polyTime F hu)
    (BQPFamilyPasses.forward_typed checker F)
  have hgen : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun n => checker.encode (forwardBody (F.circ n).flatten)) List.length) := by
    obtain ⟨A⟩ := h
    exact ⟨{ A with outputsFun := A.outputsFun }⟩
  have hc := BQPTypedPolyTime.comp hgen (family_typed checker F)
  exact hc

end BQPOpcodeCount
