import «BQP-program-data»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow

@[simp] theorem wrap_length (i : ℕ) (body : List ℕ) :
    (wrap i body).length = 2 * i + body.length := by simp [wrap]; omega

 theorem gateBlock_length {n : ℕ} (g : Instr n) : (gateBlock g).length ≤ 2 * n + 7 := by
  cases g with
  | h i => simp [gateBlock]; omega
  | s i => simp [gateBlock]; omega
  | t i => simp [gateBlock]; omega
  | x i => simp [gateBlock]; omega
  | cnot i j hij =>
    dsimp only [gateBlock]
    split <;> simp [wrap_length] <;> omega

 theorem adjointBlock_length {n : ℕ} (g : Instr n) : (adjointBlock g).length ≤ 2 * n + 7 := by
  cases g with
  | s i => simp [adjointBlock] <;> omega
  | t i => simp [adjointBlock] <;> omega
  | h i => exact gateBlock_length (.h i)
  | x i => exact gateBlock_length (.x i)
  | cnot i j hij => exact gateBlock_length (.cnot i j hij)

 theorem blocks_length {n : ℕ} (B : Instr n → List ℕ)
    (hB : ∀ g, (B g).length ≤ 2*n+7) (gs : List (Instr n)) :
    (gs.map B).flatten.length ≤ gs.length * (2*n+7) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hB g
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    nlinarith

 theorem forwardBody_length {n : ℕ} (gs : List (Instr n)) :
    (forwardBody gs).length ≤ gs.length * (2*n+7) :=
  blocks_length gateBlock gateBlock_length gs

 theorem adjointBody_length {n : ℕ} (gs : List (Instr n)) :
    (adjointBody gs).length ≤ gs.length * (2*n+7) := by
  simpa only [adjointBody, List.length_reverse] using
    blocks_length adjointBlock adjointBlock_length gs.reverse

 theorem load_length (l : List Bool) : (load l).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [load]
  | cons b l ih => cases b <;> simp [load] <;> omega

 theorem endpoint_length (l : List Bool) : (endpoint l).length ≤ 4 * l.length := by
  induction l with
  | nil => simp [endpoint]
  | cons b l ih => cases b <;> simp [endpoint] <;> omega

/-- A polynomial output-size bound for the actual doubled program; its input,
output-wire test, both gate passes, and endpoint cleanup are all counted. -/
theorem compile_length {n m : ℕ} (gs : List (Instr (n+m))) (x : Bits n) (out : Fin (n+m)) :
    (compile gs x out).length ≤ 16 * (n+m+1) * (gs.length+1) := by
  have hl := load_length (paddedInput m x)
  have he := endpoint_length (paddedInput m x)
  have hf := forwardBody_length gs
  have ha := adjointBody_length gs
  have ho := out.isLt
  rw [show (paddedInput m x).length = n+m by simp [paddedInput]] at hl he
  simp only [compile, List.length_append, List.length_replicate, wrap_length,
    List.length_cons, List.length_nil]
  nlinarith

 theorem encoded_compile_length (C : Checker) {n m : ℕ} (gs : List (Instr (n+m)))
    (x : Bits n) (out : Fin (n+m)) :
    (C.encode (compile gs x out)).length ≤ 64 * (n+m+1) * (gs.length+1) := by
  rw [C.encode_length]
  have h := compile_length gs x out
  nlinarith

end BQPProgram
