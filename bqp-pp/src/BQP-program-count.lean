import «BQP-program-data»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow BQPPaths

def opcodeCount (Q : List ℕ) : ℕ := Q.countP (fun c => decide (c % 16 = 2))

 theorem checker_count (C : Checker) (Q : List ℕ) : C.count Q = opcodeCount Q := by
  induction Q with
  | nil => exact C.count_nil
  | cons c Q ih => rw [C.count_cons, ih]; simp [opcodeCount, List.countP_cons, Nat.add_comm]

@[simp] theorem opcodeCount_append (P Q : List ℕ) :
    opcodeCount (P ++ Q) = opcodeCount P + opcodeCount Q := by simp [opcodeCount]

@[simp] theorem opcodeCount_zero (k : ℕ) : opcodeCount (List.replicate k 0) = 0 := by
  simp [opcodeCount]

@[simp] theorem opcodeCount_one (k : ℕ) : opcodeCount (List.replicate k 1) = 0 := by
  simp [opcodeCount]

@[simp] theorem opcodeCount_wrap (i : ℕ) (body : List ℕ) :
    opcodeCount (wrap i body) = opcodeCount body := by simp [wrap]

 theorem gateBlock_count {n : ℕ} (g : Instr n) :
    opcodeCount (gateBlock g) = (match g with | .h _ => 1 | _ => 0) := by
  cases g with
  | h i => change opcodeCount (wrap i [2]) = 1; rw [opcodeCount_wrap]; rfl
  | s i => simp [gateBlock, opcodeCount, wrap]
  | t i => simp [gateBlock, opcodeCount, wrap]
  | x i => simp [gateBlock, opcodeCount, wrap]
  | cnot i j hij =>
      dsimp only [gateBlock]
      split <;> simp [opcodeCount, wrap]

 theorem adjointBlock_count {n : ℕ} (g : Instr n) :
    opcodeCount (adjointBlock g) = (match g with | .h _ => 1 | _ => 0) := by
  cases g with
  | s i => simp [adjointBlock, opcodeCount, wrap]
  | t i => simp [adjointBlock, opcodeCount, wrap]
  | h i => exact gateBlock_count (.h i)
  | x i => exact gateBlock_count (.x i)
  | cnot i j hij => exact gateBlock_count (.cnot i j hij)

 theorem forwardBody_count {n : ℕ} (gs : List (Instr n)) :
    opcodeCount (forwardBody gs) = hadamardCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change opcodeCount (gateBlock g ++ forwardBody gs) = _
    rw [opcodeCount_append, gateBlock_count, ih]
    cases g <;> simp [hadamardCount, Nat.add_comm]

 theorem adjointBody_count {n : ℕ} (gs : List (Instr n)) :
    opcodeCount (adjointBody gs) = hadamardCount gs := by
  have hf : ∀ xs : List (Instr n), opcodeCount (xs.map adjointBlock).flatten = hadamardCount xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons g xs ih =>
      change opcodeCount (adjointBlock g ++ (xs.map adjointBlock).flatten) = _
      rw [opcodeCount_append, adjointBlock_count, ih]
      cases g <;> simp [hadamardCount, Nat.add_comm]
  simpa [adjointBody, hadamardCount] using hf gs.reverse

@[simp] theorem load_count (l : List Bool) : opcodeCount (load l) = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> rw [load, opcodeCount_append, ih] <;> rfl

@[simp] theorem endpoint_count (l : List Bool) : opcodeCount (endpoint l) = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> rw [endpoint, opcodeCount_append, ih] <;> rfl

/-- The exact witness length of the same program passed to the implemented
single-run checker: one choice for every forward and adjoint Hadamard. -/
theorem compile_count (C : Checker) {n m : ℕ} (gs : List (Instr (n + m)))
    (x : Bits n) (out : Fin (n + m)) :
    C.count (compile gs x out) = hadamardCount gs + hadamardCount gs := by
  rw [checker_count]
  simp only [compile, opcodeCount_append, load_count, endpoint_count,
    opcodeCount_zero, opcodeCount_wrap, forwardBody_count, adjointBody_count]
  simp [opcodeCount]

end BQPProgram
