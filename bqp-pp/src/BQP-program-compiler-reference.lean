/-
BRIDGE-C2.  THE ROUTE-(A) COMPILER, with its defining clauses exposed, together with the
three STRUCTURAL obligations of the semantic bridge: the doubled witness budget, head
safety, and the opcode well-formedness that the single-run checker needs.

The compiled program for a gate list `gs`, a classical input `x` and an output wire `out` is

    comp = ld (tp x)                       -- load `x` by a left-to-right sweep of `X`s
           ++ replicate (n+m') 0           -- return the head to wire 0
           ++ bdy gs                       -- U
           ++ (replicate out 1 ++ [8] ++ replicate out 0)   -- the output-wire test
           ++ bdyAdj gs                    -- U-dagger, in REVERSE gate order
           ++ en (tp x)                    -- the endpoint test "the tape is back to x,0..0"
           ++ replicate (n+m') 0

Three design points, each forced by a hazard.

* ADJOINTS ARE COMPILED PER BLOCK, NOT PER OPCODE.  Opcode 6 (`ct := head bit`) destroys the
  previous control and has no per-opcode inverse, so reversing an opcode list and inverting
  each entry is wrong.  `bdyAdj` recurses on the gate list and appends at the END, so the
  gate order is reversed while each gate is replaced by its own adjoint BLOCK:
  `H` and `X` are self-inverse, `S` becomes three opcode-4s, `T` becomes seven opcode-3s,
  and CNOT is its own inverse as a block.

* HEAD DRIFT is discharged by the decidable analyser `mv`: every block is head-NEUTRAL, so
  `mv (comp ...) 0 = some 0` follows by induction over blocks rather than by `decide` on a
  concrete program.  CNOT is wrapped at the LEFT-most of its two wires so that the two-site
  body never steps left of its own wrapper.

* THE INPUT-LOADING PREFIX uses only opcodes 1 and 5, never opcode 0, so it is a genuine
  prefix that contributes no witness bits; the head is walked back afterwards.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

private def wrp (i : ℕ) (body : List ℕ) : List ℕ :=
  List.replicate i 1 ++ (body ++ List.replicate i 0)

private def blk {m : ℕ} : Instr m → List ℕ
  | .h i => wrp (i : ℕ) [2]
  | .s i => wrp (i : ℕ) [4]
  | .t i => wrp (i : ℕ) [3]
  | .x i => wrp (i : ℕ) [5]
  | .cnot i j _ =>
      if (i : ℕ) < (j : ℕ) then
        wrp (i : ℕ) ([6] ++ (List.replicate ((j : ℕ) - (i : ℕ)) 1
          ++ ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)))
      else
        wrp (j : ℕ) (List.replicate ((i : ℕ) - (j : ℕ)) 1
          ++ ([6] ++ (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7])))

private def blkA {m : ℕ} : Instr m → List ℕ
  | .h i => wrp (i : ℕ) [2]
  | .s i => wrp (i : ℕ) [4, 4, 4]
  | .t i => wrp (i : ℕ) [3, 3, 3, 3, 3, 3, 3]
  | .x i => wrp (i : ℕ) [5]
  | .cnot i j hij => blk (Instr.cnot i j hij)

private def bdy {m : ℕ} : List (Instr m) → List ℕ
  | [] => []
  | g :: gs => blk g ++ bdy gs

private def bdyA {m : ℕ} : List (Instr m) → List ℕ
  | [] => []
  | g :: gs => bdyA gs ++ blkA g

private def ld : List Bool → List ℕ
  | [] => []
  | b :: l => (if b then [5, 1] else [1]) ++ ld l

private def en : List Bool → List ℕ
  | [] => []
  | b :: l => (if b then [8, 1] else [5, 8, 5, 1]) ++ en l

private def tp (n m' : ℕ) (x : Bits n) : List Bool :=
  List.ofFn (fun k : Fin (n + m') => if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false)

private def cmpP (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n)
    (out : Fin (n + m')) : List ℕ :=
  ld (tp n m' x) ++ (List.replicate (n + m') 0 ++ (bdy gs ++ (wrp (out : ℕ) [8]
    ++ (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0)))))

theorem compilerData :
    ∀ (N : ∀ m : ℕ, List (Instr m) → ℕ) (hc : List ℕ → ℕ) (mv : List ℕ → ℕ → Option ℕ),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- CHECK-1f (II): the Hadamard count of an opcode stream
      hc [] = 0 →
      (∀ (c : ℕ) (Q : List ℕ), hc (c :: Q) = (if c % 16 = 2 then 1 else 0) + hc Q) →
      -- CHECK-1fc (1): the left-safety analyser
      (∀ k : ℕ, mv [] k = some k) →
      (∀ (c : ℕ) (P : List ℕ), c % 16 = 0 → mv (c :: P) 0 = none) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 0 → mv (c :: P) (k + 1) = mv P k) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 1 → mv (c :: P) k = mv P (k + 1)) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 2 ≤ c % 16 → c % 16 ≤ 9 →
          mv (c :: P) k = mv P k) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 10 ≤ c % 16 → mv (c :: P) k = none) →
      ∃ (B BA : ∀ m : ℕ, Instr m → List ℕ) (D DA : ∀ m : ℕ, List (Instr m) → List ℕ)
        (L E : List Bool → List ℕ) (T : ∀ n m' : ℕ, Bits n → List Bool)
        (C : ∀ n m' : ℕ, List (Instr (n + m')) → Bits n → Fin (n + m') → List ℕ),
        -- the per-gate blocks
        (∀ (m : ℕ) (i : Fin m), B m (Instr.h i)
            = List.replicate (i : ℕ) 1 ++ ([2] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i : Fin m), B m (Instr.s i)
            = List.replicate (i : ℕ) 1 ++ ([4] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i : Fin m), B m (Instr.t i)
            = List.replicate (i : ℕ) 1 ++ ([3] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i : Fin m), B m (Instr.x i)
            = List.replicate (i : ℕ) 1 ++ ([5] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j), (i : ℕ) < (j : ℕ) →
            B m (Instr.cnot i j hij)
              = List.replicate (i : ℕ) 1 ++ (([6] ++ (List.replicate ((j : ℕ) - (i : ℕ)) 1
                  ++ ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)))
                ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j), (j : ℕ) < (i : ℕ) →
            B m (Instr.cnot i j hij)
              = List.replicate (j : ℕ) 1 ++ ((List.replicate ((i : ℕ) - (j : ℕ)) 1
                  ++ ([6] ++ (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7])))
                ++ List.replicate (j : ℕ) 0))
        -- the per-gate ADJOINT blocks: `T` becomes seven 3s, `S` three 4s, CNOT is its own
        ∧ (∀ (m : ℕ) (i : Fin m), BA m (Instr.h i) = B m (Instr.h i))
        ∧ (∀ (m : ℕ) (i : Fin m), BA m (Instr.x i) = B m (Instr.x i))
        ∧ (∀ (m : ℕ) (i : Fin m), BA m (Instr.s i)
            = List.replicate (i : ℕ) 1 ++ ([4, 4, 4] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i : Fin m), BA m (Instr.t i)
            = List.replicate (i : ℕ) 1
                ++ ([3, 3, 3, 3, 3, 3, 3] ++ List.replicate (i : ℕ) 0))
        ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j),
            BA m (Instr.cnot i j hij) = B m (Instr.cnot i j hij))
        -- the gate list, forward and reversed
        ∧ (∀ m : ℕ, D m [] = [])
        ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), D m (g :: gs) = B m g ++ D m gs)
        ∧ (∀ m : ℕ, DA m [] = [])
        ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
            DA m (g :: gs) = DA m gs ++ BA m g)
        -- the input-loading sweep and the endpoint test
        ∧ L [] = []
        ∧ (∀ (b : Bool) (l : List Bool), L (b :: l) = (if b then [5, 1] else [1]) ++ L l)
        ∧ E [] = []
        ∧ (∀ (b : Bool) (l : List Bool),
            E (b :: l) = (if b then [8, 1] else [5, 8, 5, 1]) ++ E l)
        ∧ (∀ (n m' : ℕ) (x : Bits n), T n m' x
            = List.ofFn (fun k : Fin (n + m') =>
                if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false))
        -- the whole route-(A) program
        ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
            C n m' gs x out
              = L (T n m' x) ++ (List.replicate (n + m') 0 ++ (D (n + m') gs
                  ++ ((List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0))
                    ++ (DA (n + m') gs
                      ++ (E (T n m' x) ++ List.replicate (n + m') 0))))))
        -- (1) the DOUBLED witness budget: one bit per Hadamard on each of the two passes
        ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
            hc (C n m' gs x out) = N (n + m') gs + N (n + m') gs)
        -- (2) HEAD SAFETY: the program never steps left of wire 0, and ends where it began
        ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
            mv (C n m' gs x out) 0 = some 0)
        -- (3) every emitted opcode is a legal, non-aborting opcode
        ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
              (c : ℕ), c ∈ C n m' gs x out → c ≤ 8)
        -- (4) the input enters through a prefix of moves and `X` gates costing no witness
        ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
            ∃ pre post : List ℕ,
              C n m' gs x out = pre ++ post
              ∧ (∀ c ∈ pre, c = 1 ∨ c = 5)
              ∧ hc pre = 0
              ∧ hc post = N (n + m') gs + N (n + m') gs) := by
  intro N hc mv hN0 hNh hNo hc0 hcC hmvN hmvZ0 hmvZS hmvR hmvS hmvB
  -- ## hc is additive, and only opcode 2 contributes
  have hcApp : ∀ P Q : List ℕ, hc (P ++ Q) = hc P + hc Q := by
    intro P
    induction P with
    | nil => intro Q; rw [List.nil_append, hc0, Nat.zero_add]
    | cons c P ih => intro Q; rw [List.cons_append, hcC, hcC, ih, Nat.add_assoc]
  have hcNo2 : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≠ 2) → hc P = 0 := by
    intro P
    induction P with
    | nil => intro _; exact hc0
    | cons c P ih =>
      intro h
      rw [hcC, if_neg (h c (by simp)), ih (fun d hd => h d (by simp [hd])), Nat.add_zero]
  have hcRep : ∀ (r c : ℕ), c % 16 ≠ 2 → hc (List.replicate r c) = 0 := by
    intro r c h
    refine hcNo2 _ ?_
    intro d hd
    rw [List.eq_of_mem_replicate hd]
    exact h
  have hcWrp : ∀ (i : ℕ) (body : List ℕ), hc (wrp i body) = hc body := by
    intro i body
    rw [wrp, hcApp, hcApp, hcRep i 1 (by omega), hcRep i 0 (by omega), Nat.zero_add,
      Nat.add_zero]
  -- ## the Hadamard count of each block
  have hcNoBody : ∀ (i : ℕ) (body : List ℕ), (∀ c ∈ body, c % 16 ≠ 2) →
      hc (wrp i body) = 0 := by
    intro i body h
    rw [hcWrp]
    exact hcNo2 body h
  have hcBh : ∀ (m : ℕ) (i : Fin m), hc (blk (Instr.h i)) = 1 := by
    intro m i
    show hc (wrp (i : ℕ) [2]) = 1
    rw [hcWrp, hcC, if_pos (by omega), hc0]
  have hcBs : ∀ (m : ℕ) (i : Fin m), hc (blk (Instr.s i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [4] (by intro d hd; simp at hd; omega)
  have hcBt : ∀ (m : ℕ) (i : Fin m), hc (blk (Instr.t i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [3] (by intro d hd; simp at hd; omega)
  have hcBx : ∀ (m : ℕ) (i : Fin m), hc (blk (Instr.x i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [5] (by intro d hd; simp at hd; omega)
  have hcBc : ∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j), hc (blk (Instr.cnot i j hij)) = 0 := by
    intro m i j hij
    show hc (blk (Instr.cnot i j hij)) = 0
    rw [blk]
    split
    · refine hcNoBody _ _ ?_
      intro d hd
      rw [List.mem_append, List.mem_append, List.mem_append] at hd
      rcases hd with hd | hd | hd | hd
      · simp at hd; omega
      · rw [List.eq_of_mem_replicate hd]; omega
      · simp at hd; omega
      · rw [List.eq_of_mem_replicate hd]; omega
    · refine hcNoBody _ _ ?_
      intro d hd
      rw [List.mem_append, List.mem_append, List.mem_append] at hd
      rcases hd with hd | hd | hd | hd
      · rw [List.eq_of_mem_replicate hd]; omega
      · simp at hd; omega
      · rw [List.eq_of_mem_replicate hd]; omega
      · simp at hd; omega
  have hcBAh : ∀ (m : ℕ) (i : Fin m), hc (blkA (Instr.h i)) = 1 := by
    intro m i
    show hc (wrp (i : ℕ) [2]) = 1
    rw [hcWrp, hcC, if_pos (by omega), hc0]
  have hcBAs : ∀ (m : ℕ) (i : Fin m), hc (blkA (Instr.s i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [4, 4, 4] (by intro d hd; simp at hd; omega)
  have hcBAt : ∀ (m : ℕ) (i : Fin m), hc (blkA (Instr.t i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [3, 3, 3, 3, 3, 3, 3] (by intro d hd; simp at hd; omega)
  have hcBAx : ∀ (m : ℕ) (i : Fin m), hc (blkA (Instr.x i)) = 0 := by
    intro m i
    exact hcNoBody (i : ℕ) [5] (by intro d hd; simp at hd; omega)
  have hcBAc : ∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j),
      hc (blkA (Instr.cnot i j hij)) = 0 := by
    intro m i j hij
    exact hcBc m i j hij
  have hcD : ∀ (m : ℕ) (gs : List (Instr m)), hc (bdy gs) = N m gs := by
    intro m gs
    induction gs with
    | nil => rw [show bdy ([] : List (Instr m)) = [] from rfl, hc0, hN0]
    | cons g gs ih =>
      rw [show bdy (g :: gs) = blk g ++ bdy gs from rfl, hcApp, ih]
      cases g with
      | h i => rw [hcBh, hNh, Nat.add_comm]
      | s i => rw [hcBs, Nat.zero_add, hNo m _ gs (by intro k; simp)]
      | t i => rw [hcBt, Nat.zero_add, hNo m _ gs (by intro k; simp)]
      | x i => rw [hcBx, Nat.zero_add, hNo m _ gs (by intro k; simp)]
      | cnot i j hij => rw [hcBc, Nat.zero_add, hNo m _ gs (by intro k; simp)]
  have hcDA : ∀ (m : ℕ) (gs : List (Instr m)), hc (bdyA gs) = N m gs := by
    intro m gs
    induction gs with
    | nil => rw [show bdyA ([] : List (Instr m)) = [] from rfl, hc0, hN0]
    | cons g gs ih =>
      rw [show bdyA (g :: gs) = bdyA gs ++ blkA g from rfl, hcApp, ih]
      cases g with
      | h i => rw [hcBAh, hNh]
      | s i => rw [hcBAs, Nat.add_zero, hNo m _ gs (by intro k; simp)]
      | t i => rw [hcBAt, Nat.add_zero, hNo m _ gs (by intro k; simp)]
      | x i => rw [hcBAx, Nat.add_zero, hNo m _ gs (by intro k; simp)]
      | cnot i j hij => rw [hcBAc, Nat.add_zero, hNo m _ gs (by intro k; simp)]
  have hcL : ∀ l : List Bool, hc (ld l) = 0 := by
    intro l
    induction l with
    | nil => exact hc0
    | cons b l ih =>
      rw [show ld (b :: l) = (if b then [5, 1] else [1]) ++ ld l from rfl, hcApp, ih,
        Nat.add_zero]
      cases b
      · rw [if_neg (by simp), hcC, if_neg (by omega), hc0]
      · rw [if_pos rfl, hcC, if_neg (by omega), hcC, if_neg (by omega), hc0]
  have hcE : ∀ l : List Bool, hc (en l) = 0 := by
    intro l
    induction l with
    | nil => exact hc0
    | cons b l ih =>
      rw [show en (b :: l) = (if b then [8, 1] else [5, 8, 5, 1]) ++ en l from rfl, hcApp,
        ih, Nat.add_zero]
      refine hcNo2 _ ?_
      intro d hd
      cases b
      · rw [if_neg (by simp)] at hd; simp at hd; omega
      · rw [if_pos rfl] at hd; simp at hd; omega
  -- ## the analyser composes
  have mvApp : ∀ (P Q : List ℕ) (k : ℕ), mv (P ++ Q) k = (mv P k).bind (fun j => mv Q j) := by
    intro P
    induction P with
    | nil => intro Q k; rw [List.nil_append, hmvN k]; rfl
    | cons c P ih =>
      intro Q k
      have h16 : c % 16 = 0 ∨ c % 16 = 1 ∨ (2 ≤ c % 16 ∧ c % 16 ≤ 9) ∨ 10 ≤ c % 16 := by
        omega
      rcases h16 with h | h | ⟨h1, h2⟩ | h
      · cases k with
        | zero => rw [List.cons_append, hmvZ0 c (P ++ Q) h, hmvZ0 c P h]; rfl
        | succ k => rw [List.cons_append, hmvZS c (P ++ Q) k h, hmvZS c P k h, ih]
      · rw [List.cons_append, hmvR c (P ++ Q) k h, hmvR c P k h, ih]
      · rw [List.cons_append, hmvS c (P ++ Q) k h1 h2, hmvS c P k h1 h2, ih]
      · rw [List.cons_append, hmvB c (P ++ Q) k h, hmvB c P k h]; rfl
  have mvR : ∀ (r k : ℕ), mv (List.replicate r 1) k = some (k + r) := by
    intro r
    induction r with
    | zero => intro k; rw [List.replicate_zero, hmvN k, Nat.add_zero]
    | succ r ih =>
      intro k
      rw [List.replicate_succ, hmvR 1 _ k (by omega), ih]
      congr 1
      omega
  have mvZ : ∀ (r k : ℕ), mv (List.replicate r 0) (k + r) = some k := by
    intro r
    induction r with
    | zero => intro k; rw [List.replicate_zero, Nat.add_zero, hmvN k]
    | succ r ih =>
      intro k
      have he : k + (r + 1) = (k + r) + 1 := by omega
      rw [List.replicate_succ, he, hmvZS 0 _ (k + r) (by omega), ih]
  have mvStay : ∀ P : List ℕ, (∀ c ∈ P, 2 ≤ c % 16 ∧ c % 16 ≤ 9) →
      ∀ k : ℕ, mv P k = some k := by
    intro P
    induction P with
    | nil => intro _ k; exact hmvN k
    | cons c P ih =>
      intro h k
      obtain ⟨h1, h2⟩ := h c (by simp)
      rw [hmvS c P k h1 h2, ih (fun d hd => h d (by simp [hd])) k]
  have mvWrp : ∀ body : List ℕ, (∀ k : ℕ, mv body k = some k) →
      ∀ (i k : ℕ), mv (wrp i body) k = some k := by
    intro body hb i k
    rw [wrp, mvApp, mvR i k]
    show mv (body ++ List.replicate i 0) (k + i) = some k
    rw [mvApp, hb (k + i)]
    show mv (List.replicate i 0) (k + i) = some k
    exact mvZ i k
  have mvB : ∀ (m : ℕ) (g : Instr m) (k : ℕ), mv (blk g) k = some k := by
    intro m g k
    cases g with
    | h i => exact mvWrp [2] (mvStay [2] (by intro d hd; simp at hd; omega)) _ k
    | s i => exact mvWrp [4] (mvStay [4] (by intro d hd; simp at hd; omega)) _ k
    | t i => exact mvWrp [3] (mvStay [3] (by intro d hd; simp at hd; omega)) _ k
    | x i => exact mvWrp [5] (mvStay [5] (by intro d hd; simp at hd; omega)) _ k
    | cnot i j hij =>
      show mv (blk (Instr.cnot i j hij)) k = some k
      rw [blk]
      split
      · refine mvWrp _ ?_ _ k
        intro k'
        rw [mvApp, mvStay [6] (by intro d hd; simp at hd; omega) k']
        show mv (List.replicate ((j : ℕ) - (i : ℕ)) 1
          ++ ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)) k' = some k'
        rw [mvApp, mvR _ k']
        show mv ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)
          (k' + ((j : ℕ) - (i : ℕ))) = some k'
        rw [mvApp, mvStay [7] (by intro d hd; simp at hd; omega)]
        show mv (List.replicate ((j : ℕ) - (i : ℕ)) 0)
          (k' + ((j : ℕ) - (i : ℕ))) = some k'
        exact mvZ _ k'
      · refine mvWrp _ ?_ _ k
        intro k'
        rw [mvApp, mvR _ k']
        show mv ([6] ++ (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7]))
          (k' + ((i : ℕ) - (j : ℕ))) = some k'
        rw [mvApp, mvStay [6] (by intro d hd; simp at hd; omega)]
        show mv (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7])
          (k' + ((i : ℕ) - (j : ℕ))) = some k'
        rw [mvApp, mvZ _ k']
        show mv [7] k' = some k'
        exact mvStay [7] (by intro d hd; simp at hd; omega) k'
  have mvBA : ∀ (m : ℕ) (g : Instr m) (k : ℕ), mv (blkA g) k = some k := by
    intro m g k
    cases g with
    | h i => exact mvWrp [2] (mvStay [2] (by intro d hd; simp at hd; omega)) _ k
    | s i =>
      exact mvWrp [4, 4, 4] (mvStay [4, 4, 4] (by intro d hd; simp at hd; omega)) _ k
    | t i =>
      exact mvWrp [3, 3, 3, 3, 3, 3, 3]
        (mvStay [3, 3, 3, 3, 3, 3, 3] (by intro d hd; simp at hd; omega)) _ k
    | x i => exact mvWrp [5] (mvStay [5] (by intro d hd; simp at hd; omega)) _ k
    | cnot i j hij =>
      show mv (blk (Instr.cnot i j hij)) k = some k
      exact mvB m (Instr.cnot i j hij) k
  have mvD : ∀ (m : ℕ) (gs : List (Instr m)) (k : ℕ), mv (bdy gs) k = some k := by
    intro m gs
    induction gs with
    | nil => intro k; exact hmvN k
    | cons g gs ih =>
      intro k
      rw [show bdy (g :: gs) = blk g ++ bdy gs from rfl, mvApp, mvB m g k]
      show mv (bdy gs) k = some k
      exact ih k
  have mvDA : ∀ (m : ℕ) (gs : List (Instr m)) (k : ℕ), mv (bdyA gs) k = some k := by
    intro m gs
    induction gs with
    | nil => intro k; exact hmvN k
    | cons g gs ih =>
      intro k
      rw [show bdyA (g :: gs) = bdyA gs ++ blkA g from rfl, mvApp, ih k]
      show mv (blkA g) k = some k
      exact mvBA m g k
  have mvL : ∀ (l : List Bool) (k : ℕ), mv (ld l) k = some (k + l.length) := by
    intro l
    induction l with
    | nil => intro k; rw [show ld ([] : List Bool) = [] from rfl, hmvN k]; simp
    | cons b l ih =>
      intro k
      rw [show ld (b :: l) = (if b then [5, 1] else [1]) ++ ld l from rfl, mvApp]
      have hstep : mv (if b then [5, 1] else [1]) k = some (k + 1) := by
        cases b
        · rw [if_neg (by simp), hmvR 1 [] k (by omega), hmvN]
        · rw [if_pos rfl, hmvS 5 [1] k (by omega) (by omega), hmvR 1 [] k (by omega),
            hmvN]
      rw [hstep]
      show mv (ld l) (k + 1) = some (k + (b :: l).length)
      rw [ih (k + 1)]
      congr 1
      simp
      omega
  have mvE : ∀ (l : List Bool) (k : ℕ), mv (en l) k = some (k + l.length) := by
    intro l
    induction l with
    | nil => intro k; rw [show en ([] : List Bool) = [] from rfl, hmvN k]; simp
    | cons b l ih =>
      intro k
      rw [show en (b :: l) = (if b then [8, 1] else [5, 8, 5, 1]) ++ en l from rfl, mvApp]
      have hstep : mv (if b then [8, 1] else [5, 8, 5, 1]) k = some (k + 1) := by
        cases b
        · rw [if_neg (by simp), hmvS 5 [8, 5, 1] k (by omega) (by omega),
            hmvS 8 [5, 1] k (by omega) (by omega), hmvS 5 [1] k (by omega) (by omega),
            hmvR 1 [] k (by omega), hmvN]
        · rw [if_pos rfl, hmvS 8 [1] k (by omega) (by omega), hmvR 1 [] k (by omega),
            hmvN]
      rw [hstep]
      show mv (en l) (k + 1) = some (k + (b :: l).length)
      rw [ih (k + 1)]
      congr 1
      simp
      omega
  -- ## membership
  have memWrp : ∀ (i : ℕ) (body : List ℕ) (c : ℕ), c ∈ wrp i body →
      c = 1 ∨ c = 0 ∨ c ∈ body := by
    intro i body c hcm
    rw [wrp, List.mem_append, List.mem_append] at hcm
    rcases hcm with hcm | hcm | hcm
    · exact Or.inl (List.eq_of_mem_replicate hcm)
    · exact Or.inr (Or.inr hcm)
    · exact Or.inr (Or.inl (List.eq_of_mem_replicate hcm))
  have memB : ∀ (m : ℕ) (g : Instr m) (c : ℕ), c ∈ blk g → c ≤ 8 := by
    intro m g c hcm
    cases g with
    | h i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | s i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | t i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | x i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | cnot i j hij =>
      rw [show blk (Instr.cnot i j hij)
          = if (i : ℕ) < (j : ℕ) then
              wrp (i : ℕ) ([6] ++ (List.replicate ((j : ℕ) - (i : ℕ)) 1
                ++ ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)))
            else
              wrp (j : ℕ) (List.replicate ((i : ℕ) - (j : ℕ)) 1
                ++ ([6] ++ (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7]))) from rfl] at hcm
      split at hcm
      · rcases memWrp _ _ _ hcm with h | h | h
        · omega
        · omega
        · rw [List.mem_append, List.mem_append, List.mem_append] at h
          rcases h with h | h | h | h
          · simp at h; omega
          · rw [List.eq_of_mem_replicate h]; omega
          · simp at h; omega
          · rw [List.eq_of_mem_replicate h]; omega
      · rcases memWrp _ _ _ hcm with h | h | h
        · omega
        · omega
        · rw [List.mem_append, List.mem_append, List.mem_append] at h
          rcases h with h | h | h | h
          · rw [List.eq_of_mem_replicate h]; omega
          · simp at h; omega
          · rw [List.eq_of_mem_replicate h]; omega
          · simp at h; omega
  have memBA : ∀ (m : ℕ) (g : Instr m) (c : ℕ), c ∈ blkA g → c ≤ 8 := by
    intro m g c hcm
    cases g with
    | h i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | s i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | t i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | x i =>
      rcases memWrp _ _ _ hcm with h | h | h
      · omega
      · omega
      · simp at h; omega
    | cnot i j hij => exact memB m (Instr.cnot i j hij) c hcm
  have memD : ∀ (m : ℕ) (gs : List (Instr m)) (c : ℕ), c ∈ bdy gs → c ≤ 8 := by
    intro m gs
    induction gs with
    | nil => intro c hcm; simp [show bdy ([] : List (Instr m)) = [] from rfl] at hcm
    | cons g gs ih =>
      intro c hcm
      rw [show bdy (g :: gs) = blk g ++ bdy gs from rfl, List.mem_append] at hcm
      rcases hcm with h | h
      · exact memB m g c h
      · exact ih c h
  have memDA : ∀ (m : ℕ) (gs : List (Instr m)) (c : ℕ), c ∈ bdyA gs → c ≤ 8 := by
    intro m gs
    induction gs with
    | nil => intro c hcm; simp [show bdyA ([] : List (Instr m)) = [] from rfl] at hcm
    | cons g gs ih =>
      intro c hcm
      rw [show bdyA (g :: gs) = bdyA gs ++ blkA g from rfl, List.mem_append] at hcm
      rcases hcm with h | h
      · exact ih c h
      · exact memBA m g c h
  have memL : ∀ (l : List Bool) (c : ℕ), c ∈ ld l → c = 1 ∨ c = 5 := by
    intro l
    induction l with
    | nil => intro c hcm; simp [show ld ([] : List Bool) = [] from rfl] at hcm
    | cons b l ih =>
      intro c hcm
      rw [show ld (b :: l) = (if b then [5, 1] else [1]) ++ ld l from rfl,
        List.mem_append] at hcm
      rcases hcm with h | h
      · cases b
        · rw [if_neg (by simp)] at h; simp at h; omega
        · rw [if_pos rfl] at h; simp at h; omega
      · exact ih c h
  have memE : ∀ (l : List Bool) (c : ℕ), c ∈ en l → c ≤ 8 := by
    intro l
    induction l with
    | nil => intro c hcm; simp [show en ([] : List Bool) = [] from rfl] at hcm
    | cons b l ih =>
      intro c hcm
      rw [show en (b :: l) = (if b then [8, 1] else [5, 8, 5, 1]) ++ en l from rfl,
        List.mem_append] at hcm
      rcases hcm with h | h
      · cases b
        · rw [if_neg (by simp)] at h; simp at h; omega
        · rw [if_pos rfl] at h; simp at h; omega
      · exact ih c h
  -- ## assemble
  have htplen : ∀ (n m' : ℕ) (x : Bits n), (tp n m' x).length = n + m' := by
    intro n m' x
    rw [tp, List.length_ofFn]
  refine ⟨fun m g => blk g, fun m g => blkA g, fun m gs => bdy gs, fun m gs => bdyA gs,
    ld, en, tp, cmpP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m i; rfl
  · intro m i; rfl
  · intro m i; rfl
  · intro m i; rfl
  · intro m i j hij h
    show blk (Instr.cnot i j hij) = _
    rw [blk, if_pos h]
    rfl
  · intro m i j hij h
    show blk (Instr.cnot i j hij) = _
    rw [blk, if_neg (by omega)]
    rfl
  · intro m i; rfl
  · intro m i; rfl
  · intro m i; rfl
  · intro m i; rfl
  · intro m i j hij; rfl
  · intro m; rfl
  · intro m g gs; rfl
  · intro m; rfl
  · intro m g gs; rfl
  · rfl
  · intro b l; rfl
  · rfl
  · intro b l; rfl
  · intro n m' x; rfl
  · intro n m' gs x out; rfl
  · -- (1) the doubled witness budget
    intro n m' gs x out
    rw [cmpP, hcApp, hcApp, hcApp, hcApp, hcApp, hcApp, hcL, hcE, hcD, hcDA, hcWrp,
      hcRep (n + m') 0 (by omega), hcC, if_neg (by omega), hc0]
    omega
  · -- (2) head safety
    intro n m' gs x out
    rw [cmpP, mvApp, mvL (tp n m' x) 0, htplen]
    show (mv (List.replicate (n + m') 0 ++ (bdy gs ++ (wrp (out : ℕ) [8]
      ++ (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0))))) (0 + (n + m')))
        = some 0
    rw [mvApp, mvZ (n + m') 0]
    show (mv (bdy gs ++ (wrp (out : ℕ) [8]
      ++ (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0)))) 0) = some 0
    rw [mvApp, mvD (n + m') gs 0]
    show (mv (wrp (out : ℕ) [8]
      ++ (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0))) 0) = some 0
    rw [mvApp, mvWrp [8] (mvStay [8] (by intro d hd; simp at hd; omega)) (out : ℕ) 0]
    show (mv (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0)) 0) = some 0
    rw [mvApp, mvDA (n + m') gs 0]
    show (mv (en (tp n m' x) ++ List.replicate (n + m') 0) 0) = some 0
    rw [mvApp, mvE (tp n m' x) 0, htplen]
    exact mvZ (n + m') 0
  · -- (3) opcode well-formedness
    intro n m' gs x out c hcm
    rw [cmpP, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
      List.mem_append, List.mem_append] at hcm
    rcases hcm with h | h | h | h | h | h | h
    · rcases memL _ c h with h' | h' <;> omega
    · rw [List.eq_of_mem_replicate h]; omega
    · exact memD (n + m') gs c h
    · rcases memWrp _ _ _ h with h' | h' | h'
      · omega
      · omega
      · simp at h'; omega
    · exact memDA (n + m') gs c h
    · exact memE _ c h
    · rw [List.eq_of_mem_replicate h]; omega
  · -- (4) the input-loading prefix
    intro n m' gs x out
    refine ⟨ld (tp n m' x), List.replicate (n + m') 0 ++ (bdy gs ++ (wrp (out : ℕ) [8]
      ++ (bdyA gs ++ (en (tp n m' x) ++ List.replicate (n + m') 0)))), rfl,
      memL (tp n m' x), hcL _, ?_⟩
    rw [hcApp, hcApp, hcApp, hcApp, hcApp, hcE, hcD, hcDA, hcWrp,
      hcRep (n + m') 0 (by omega), hcC, if_neg (by omega), hc0]
    omega


end BQPBridgeReference
