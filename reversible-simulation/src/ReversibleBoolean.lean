import ReversibleCore

set_option autoImplicit false

namespace ShiReversible

/-- A Boolean assignment with a fresh target distinct from its operands. -/
inductive Assignment (n : Nat) where
  | constant (t : Fin n) (value : Bool)
  | copy (s t : Fin n) (h : s ≠ t)
  | neg (s t : Fin n) (h : s ≠ t)
  | conj (a b t : Fin n) (ha : a ≠ t) (hb : b ≠ t)

def Assignment.target {n : Nat} : Assignment n → Fin n
  | .constant t _ => t
  | .copy _ t _ => t
  | .neg _ t _ => t
  | .conj _ _ t _ _ => t

def Assignment.value {n : Nat} : Assignment n → Bits n → Bool
  | .constant _ b, _ => b
  | .copy r _ _, s => s r
  | .neg r _ _, s => !s r
  | .conj a b _ _ _, s => s a && s b

def Assignment.eval {n : Nat} (a : Assignment n) (s : Bits n) : Bits n :=
  Function.update s a.target (a.value s)

def Assignment.compile {n : Nat} : Assignment n → List (Gate n)
  | .constant t false => []
  | .constant t true => [.x t]
  | .copy r t h => [.cx r t h]
  | .neg r t h => [.cx r t h, .x t]
  | .conj a b t ha hb => [.ccx a b t ha hb]

theorem Assignment.compile_correct {n : Nat} (a : Assignment n) (s : Bits n)
    (hz : s a.target = false) : run a.compile s = a.eval s := by
  cases a with
  | constant t b =>
    cases b
    · funext i
      by_cases hi : i = t
      · subst i
        simpa [Assignment.compile, Assignment.eval, Assignment.target,
          Assignment.value] using hz
      · simp [Assignment.compile, Assignment.eval, Assignment.target,
          Assignment.value, Function.update_of_ne hi]
    · simp_all [Assignment.compile, Assignment.eval, Assignment.target,
        Assignment.value, Gate.eval, run]
  | copy r t h =>
    simp_all [Assignment.compile, Assignment.eval, Assignment.target,
      Assignment.value, Gate.eval, run]
  | neg r t h =>
    funext i
    by_cases hi : i = t
    · subst i
      simp_all [Assignment.compile, Assignment.eval, Assignment.target,
        Assignment.value, Gate.eval, run]
    · simp [Assignment.compile, Assignment.eval, Assignment.target,
        Assignment.value, Gate.eval, run, Function.update_of_ne hi]
  | conj a b t ha hb =>
    simp_all [Assignment.compile, Assignment.eval, Assignment.target,
      Assignment.value, Gate.eval, run]

theorem Assignment.eval_other {n : Nat} (a : Assignment n) (s : Bits n)
    (i : Fin n) (h : i ≠ a.target) : a.eval s i = s i := by
  simp [Assignment.eval, Function.update_of_ne h]

theorem Assignment.compile_length {n : Nat} (a : Assignment n) :
    a.compile.length ≤ 2 := by
  cases a with
  | constant t b => cases b <;> simp [Assignment.compile]
  | copy => simp [Assignment.compile]
  | neg => simp [Assignment.compile]
  | conj => simp [Assignment.compile]

def compileAssignments {n : Nat} (c : List (Assignment n)) : List (Gate n) :=
  c.flatMap Assignment.compile

def evalAssignments {n : Nat} (c : List (Assignment n)) (s : Bits n) : Bits n :=
  c.foldl (fun s a => a.eval s) s

/-- Correctness of a single-assignment reversible compiler, on zero target wires. -/
theorem compileAssignments_correct {n : Nat} (c : List (Assignment n))
    (hn : (c.map Assignment.target).Nodup) (s : Bits n)
    (hz : ∀ a ∈ c, s a.target = false) :
    run (compileAssignments c) s = evalAssignments c s := by
  induction c generalizing s with
  | nil => rfl
  | cons a c ih =>
    have hn' : (c.map Assignment.target).Nodup := (List.nodup_cons.mp hn).2
    have hne (b : Assignment n) (hb : b ∈ c) : b.target ≠ a.target := by
      intro heq
      apply (List.nodup_cons.mp hn).1
      exact List.mem_map.mpr ⟨b, hb, heq⟩
    change run (a.compile ++ compileAssignments c) s =
      evalAssignments c (a.eval s)
    rw [run_append, a.compile_correct s (hz a (by simp))]
    apply ih hn'
    intro b hb
    rw [a.eval_other s b.target (hne b hb)]
    exact hz b (by simp [hb])

theorem compileAssignments_length {n : Nat} (c : List (Assignment n)) :
    (compileAssignments c).length ≤ 2 * c.length := by
  induction c with
  | nil => simp [compileAssignments]
  | cons a c ih =>
    have ha := a.compile_length
    simp only [compileAssignments, List.flatMap_cons, List.length_append,
      List.length_cons] at *
    omega

end ShiReversible
