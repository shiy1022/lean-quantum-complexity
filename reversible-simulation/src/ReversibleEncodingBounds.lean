import ReversibleLiteralEmission

set_option autoImplicit false
namespace ShiReversibleEncoding

@[simp] theorem encStr_length (ls : List (List Bool)) :
    (ShiBQP.encStr ls).length = ls.length + 1 + ls.flatten.length := by
  simp [ShiBQP.encStr, ShiBQP.encNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem flatten_map_length_le {A B : Type} (f : A → List B) (xs : List A) (bound : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.map f).flatten.length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hs := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
      omega

theorem encLayer_length {m : Nat} (l : List (ShiShallow.Instr m)) :
    (ShiBQP.encLayer l).length ≤ l.length * (2 * m + 6) + 1 := by
  have h := flatten_map_length_le ShiBQP.encInstr l (2 * m + 5)
    (fun g _ => ShiReversibleGenerator.encInstr_length g)
  simp only [ShiBQP.encLayer, encStr_length, List.length_map]
  calc
    l.length + 1 + (l.map ShiBQP.encInstr).flatten.length ≤
        l.length + 1 + l.length * (2 * m + 5) := by omega
    _ = l.length * (2 * m + 6) + 1 := by ring

theorem encCirc_length_of_singleton {m : Nat} (c : ShiShallow.Layered m)
    (h : ∀ l ∈ c, l.length = 1) :
    (ShiBQP.encCirc c).length ≤ c.length * (2 * m + 8) + 1 := by
  have hb : ∀ l ∈ c, (ShiBQP.encLayer l).length ≤ 2 * m + 7 := by
    intro l hl
    have e := encLayer_length l
    rw [h l hl] at e
    simpa using e
  have e := flatten_map_length_le ShiBQP.encLayer c (2 * m + 7) hb
  simp only [ShiBQP.encCirc, encStr_length, List.length_map]
  calc
    c.length + 1 + (c.map ShiBQP.encLayer).flatten.length ≤
        c.length + 1 + c.length * (2 * m + 7) := by omega
    _ = c.length * (2 * m + 8) + 1 := by ring

theorem encFamilyAt_length (F : ShiClass.Family) (n : Nat)
    (h : ∀ l ∈ F.circ n, l.length = 1) :
    (ShiBQP.encFamilyAt F n).length ≤
      (F.circ n).length * (2 * (n + (F.anc n + 1)) + 8) + n + 2 * F.anc n + 3 := by
  have hc := encCirc_length_of_singleton (F.circ n) h
  have ho := (F.out n).isLt
  simp only [ShiBQP.encFamilyAt, List.length_append, ShiBQP.encNat,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The unchanged polynomial family bounds also bound its actual serialized bytes. -/
theorem encFamilyAt_polynomial_bound (F : ShiClass.Family) (hp : ShiBQP.PolyBounded F)
    (hs : ∀ n l, l ∈ F.circ n → l.length = 1) :
    ∃ p : Polynomial Nat, ∀ n, (ShiBQP.encFamilyAt F n).length ≤ p.eval n := by
  obtain ⟨q, hd, ha⟩ := hp
  refine ⟨q * (Polynomial.C 2 * (Polynomial.X + q + Polynomial.C 1) + Polynomial.C 8) +
    Polynomial.X + Polynomial.C 2 * q + Polynomial.C 3, ?_⟩
  intro n
  have e := encFamilyAt_length F n (hs n)
  have hc : (F.circ n).length ≤ q.eval n := hd n
  have hprod := Nat.mul_le_mul hc
    (show 2 * (n + (F.anc n + 1)) + 8 ≤ 2 * (n + q.eval n + 1) + 8 by
      have h := ha n
      omega)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h := ha n
  omega

end ShiReversibleEncoding
