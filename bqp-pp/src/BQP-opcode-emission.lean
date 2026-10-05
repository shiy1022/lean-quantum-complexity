import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPOpcodeEmission
open Turing Turing.TM2

/-- The checker stores the most significant bit first within each opcode. -/
def bits (c : ℕ) : List Bool :=
  [decide (c / 8 % 2 = 1), decide (c / 4 % 2 = 1),
    decide (c / 2 % 2 = 1), decide (c % 2 = 1)]

/-- Opcodes are stored in reverse program order, preserving each four-bit block. -/
def encode : List ℕ → List Bool
  | [] => []
  | c :: p => encode p ++ bits c

@[simp] theorem encode_append (p q : List ℕ) : encode (p ++ q) = encode q ++ encode p := by
  induction p with
  | nil => simp [encode]
  | cons c p ih => simp [encode, ih, List.append_assoc]

@[simp] theorem encode_length (p : List ℕ) : (encode p).length = 4*p.length := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [encode, bits, ih]; omega

variable {K L V : Type} [DecidableEq K] {G : K → Type}

/-- Emit an explicit Boolean string onto a stack in one finite statement tree.
Its size depends on the supplied fixed string, never on the machine input. -/
def pushBits (k : K) (e : G k ≃ Bool) (bs : List Bool) (q : Stmt G L V) : Stmt G L V :=
  bs.foldr (fun b q => .push k (fun _ => e.symm b) q) q

theorem stepAux_pushBits (k : K) (e : G k ≃ Bool) (bs : List Bool)
    (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    stepAux (pushBits k e bs q) v S =
      stepAux q v (Function.update S k (bs.reverse.map e.symm ++ S k)) := by
  induction bs generalizing S with
  | nil => simp [pushBits]
  | cons b bs ih =>
      simp only [pushBits, List.foldr_cons, stepAux]
      have h := ih (Function.update S k (e.symm b :: S k))
      simpa only [pushBits, Function.update_self, Function.update_idem,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using h

/-- A fixed opcode block is implemented by a fixed finite statement, with no
unbounded list hidden in the finite control. -/
def emit (k : K) (e : G k ≃ Bool) (p : List ℕ) (q : Stmt G L V) : Stmt G L V :=
  pushBits k e (encode p).reverse q

theorem stepAux_emit (k : K) (e : G k ≃ Bool) (p : List ℕ)
    (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    stepAux (emit k e p q) v S =
      stepAux q v (Function.update S k ((encode p).map e.symm ++ S k)) := by
  simpa only [emit, List.reverse_reverse] using stepAux_pushBits k e (encode p).reverse q v S

end BQPOpcodeEmission
