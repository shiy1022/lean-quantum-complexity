import Definitions.Def_ShiClassQMAAmp
import Theorems.Thm_ShiShallow_exists_layout_bijection

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ShiClassQMAAmp

private theorem dHit (D : List (ℕ × ℕ) → ℕ → ℕ)
    (hD : ∀ (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ),
      D ((a, b) :: r) x = if x < a then b + x else D r (x - a))
    (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ) (h : x < a) :
    D ((a, b) :: r) x = b + x := by
  rw [hD, if_pos h]

private theorem dSkip (D : List (ℕ × ℕ) → ℕ → ℕ)
    (hD : ∀ (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ),
      D ((a, b) :: r) x = if x < a then b + x else D r (x - a))
    (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ) (h : a ≤ x) :
    D ((a, b) :: r) x = D r (x - a) := by
  rw [hD, if_neg (Nat.not_lt.mpr h)]

private theorem layout_eq
    (D : List (ℕ × ℕ) → ℕ → ℕ)
    (hD : ∀ (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ),
      D ((a, b) :: r) x = if x < a then b + x else D r (x - a))
    (n wit anc : ℕ)
    (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) :
    D [(n, 0), (wit, n), (anc, n + 3 * wit), (1, n + 3 * wit + anc),
       (n, n + 3 * wit + anc + 1), (wit, n + wit),
       (anc, 2 * n + 3 * wit + anc + 1), (1, 2 * n + 3 * wit + 2 * anc + 1),
       (n, 2 * n + 3 * wit + 2 * anc + 2), (wit, n + 2 * wit),
       (anc, 3 * n + 3 * wit + 2 * anc + 2), (1, 3 * n + 3 * wit + 3 * anc + 2),
       (1, 3 * n + 3 * wit + 3 * anc + 3)] v.val
      = ((ampSig n wit anc) v).val := by
  obtain ⟨hbij, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    Classical.choose_spec (ShiShallow.exists_layout_bijection n wit anc)
  unfold ampSig
  have hv := v.isLt
  by_cases q1 : v.val < n
  · rw [dHit D hD n 0 _ v.val q1]
    have hs := h1 v v.val q1 rfl
    omega
  · have q1' : n ≤ v.val := Nat.le_of_not_gt q1
    rw [dSkip D hD n 0 _ v.val q1']
    by_cases q2 : v.val - n < wit
    · rw [dHit D hD wit n _ (v.val - n) q2]
      have hs := h2 v (v.val - n) q2 (by omega)
      omega
    · have q2' : wit ≤ v.val - n := Nat.le_of_not_gt q2
      rw [dSkip D hD wit n _ (v.val - n) q2']
      by_cases q3 : v.val - n - wit < anc
      · rw [dHit D hD anc (n + 3 * wit) _ (v.val - n - wit) q3]
        have hs := h3 v (v.val - n - wit) q3 (by omega)
        omega
      · have q3' : anc ≤ v.val - n - wit := Nat.le_of_not_gt q3
        rw [dSkip D hD anc (n + 3 * wit) _ (v.val - n - wit) q3']
        by_cases q4 : v.val - n - wit - anc < 1
        · rw [dHit D hD 1 (n + 3 * wit + anc) _ (v.val - n - wit - anc) q4]
          have hs := h4 v (by omega)
          omega
        · have q4' : 1 ≤ v.val - n - wit - anc := Nat.le_of_not_gt q4
          rw [dSkip D hD 1 (n + 3 * wit + anc) _ (v.val - n - wit - anc) q4']
          by_cases q5 : v.val - n - wit - anc - 1 < n
          · rw [dHit D hD n (n + 3 * wit + anc + 1) _
                (v.val - n - wit - anc - 1) q5]
            have hs := h5 v (v.val - n - wit - anc - 1) q5 (by omega)
            omega
          · have q5' : n ≤ v.val - n - wit - anc - 1 := Nat.le_of_not_gt q5
            rw [dSkip D hD n (n + 3 * wit + anc + 1) _
                  (v.val - n - wit - anc - 1) q5']
            by_cases q6 : v.val - n - wit - anc - 1 - n < wit
            · rw [dHit D hD wit (n + wit) _
                  (v.val - n - wit - anc - 1 - n) q6]
              have hs := h6 v (v.val - n - wit - anc - 1 - n) q6 (by omega)
              omega
            · have q6' : wit ≤ v.val - n - wit - anc - 1 - n := Nat.le_of_not_gt q6
              rw [dSkip D hD wit (n + wit) _
                    (v.val - n - wit - anc - 1 - n) q6']
              by_cases q7 : v.val - n - wit - anc - 1 - n - wit < anc
              · rw [dHit D hD anc (2 * n + 3 * wit + anc + 1) _
                    (v.val - n - wit - anc - 1 - n - wit) q7]
                have hs := h7 v (v.val - n - wit - anc - 1 - n - wit) q7 (by omega)
                omega
              · have q7' : anc ≤ v.val - n - wit - anc - 1 - n - wit := Nat.le_of_not_gt q7
                rw [dSkip D hD anc (2 * n + 3 * wit + anc + 1) _
                      (v.val - n - wit - anc - 1 - n - wit) q7']
                by_cases q8 : v.val - n - wit - anc - 1 - n - wit - anc < 1
                · rw [dHit D hD 1 (2 * n + 3 * wit + 2 * anc + 1) _
                      (v.val - n - wit - anc - 1 - n - wit - anc) q8]
                  have hs := h8 v (by omega)
                  omega
                · have q8' : 1 ≤ v.val - n - wit - anc - 1 - n - wit - anc :=
                    Nat.le_of_not_gt q8
                  rw [dSkip D hD 1 (2 * n + 3 * wit + 2 * anc + 1) _
                        (v.val - n - wit - anc - 1 - n - wit - anc) q8']
                  by_cases q9 : v.val - n - wit - anc - 1 - n - wit - anc - 1 < n
                  · rw [dHit D hD n (2 * n + 3 * wit + 2 * anc + 2) _
                        (v.val - n - wit - anc - 1 - n - wit - anc - 1) q9]
                    have hs := h9 v
                      (v.val - n - wit - anc - 1 - n - wit - anc - 1) q9 (by omega)
                    omega
                  · have q9' : n ≤ v.val - n - wit - anc - 1 - n - wit - anc - 1 :=
                      Nat.le_of_not_gt q9
                    rw [dSkip D hD n (2 * n + 3 * wit + 2 * anc + 2) _
                          (v.val - n - wit - anc - 1 - n - wit - anc - 1) q9']
                    by_cases q10 :
                        v.val - n - wit - anc - 1 - n - wit - anc - 1 - n < wit
                    · rw [dHit D hD wit (n + 2 * wit) _
                          (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n) q10]
                      have hs := h10 v
                        (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n) q10 (by omega)
                      omega
                    · have q10' :
                          wit ≤ v.val - n - wit - anc - 1 - n - wit - anc - 1 - n :=
                        Nat.le_of_not_gt q10
                      rw [dSkip D hD wit (n + 2 * wit) _
                            (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n) q10']
                      by_cases q11 :
                          v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit < anc
                      · rw [dHit D hD anc (3 * n + 3 * wit + 2 * anc + 2) _
                            (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit) q11]
                        have hs := h11 v
                          (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit)
                          q11 (by omega)
                        omega
                      · have q11' :
                            anc ≤ v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit :=
                          Nat.le_of_not_gt q11
                        rw [dSkip D hD anc (3 * n + 3 * wit + 2 * anc + 2) _
                              (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit) q11']
                        by_cases q12 :
                            v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc < 1
                        · rw [dHit D hD 1 (3 * n + 3 * wit + 3 * anc + 2) _
                              (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc) q12]
                          have hs := h12 v (by omega)
                          omega
                        · have q12' :
                              1 ≤ v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc :=
                            Nat.le_of_not_gt q12
                          rw [dSkip D hD 1 (3 * n + 3 * wit + 3 * anc + 2) _
                                (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc) q12']
                          have q13 :
                              v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc - 1 < 1 := by
                            omega
                          rw [dHit D hD 1 (3 * n + 3 * wit + 3 * anc + 3) _
                                (v.val - n - wit - anc - 1 - n - wit - anc - 1 - n - wit - anc - 1) q13]
                          have hs := h13 v (by omega)
                          omega

/-- At every copy offset, the recursively computable thirteen-piece index map used by the
emitter is exactly the wire map `ampE` used by the explicit amplifier.  In particular, the
same statement applies independently to both operands of a controlled-not instruction. -/
theorem solution
    (D : List (ℕ × ℕ) → ℕ → ℕ)
    (hD : ∀ (a b : ℕ) (r : List (ℕ × ℕ)) (x : ℕ),
      D ((a, b) :: r) x = if x < a then b + x else D r (x - a))
    (n wit anc off : ℕ)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (i : Fin (n + (wit + (anc + 1)))) :
    D [(n, 0), (wit, n), (anc, n + 3 * wit), (1, n + 3 * wit + anc),
       (n, n + 3 * wit + anc + 1), (wit, n + wit),
       (anc, 2 * n + 3 * wit + anc + 1), (1, 2 * n + 3 * wit + 2 * anc + 1),
       (n, 2 * n + 3 * wit + 2 * anc + 2), (wit, n + 2 * wit),
       (anc, 3 * n + 3 * wit + 2 * anc + 2), (1, 3 * n + 3 * wit + 3 * anc + 2),
       (1, 3 * n + 3 * wit + 3 * anc + 3)] (off + i.val)
      = ((ampE n wit anc off hoff) i).val := by
  have h := layout_eq D hD n wit anc
    (ampEmb (n + (wit + (anc + 1))) off hoff i)
  exact h
