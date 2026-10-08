import ReversibleFormulaRaw
import ReversibleCircuitTheorem

set_option autoImplicit false

namespace ShiReversibleFormula

open ShiReversible

/-- Embed an explicitly addressed topological node into the existing gate compiler. -/
def RawAssignment.toAssignment {n : Nat} (a : RawAssignment)
    (ht : a.target < n) (hp : a.Topological) : Assignment n := by
  cases a with
  | constant t b => exact .constant ⟨t, ht⟩ b
  | copy r t =>
    have hr : r < t := hp
    exact .copy ⟨r, hr.trans ht⟩ ⟨t, ht⟩ (by intro h; exact hr.ne (congrArg Fin.val h))
  | neg r t =>
    have hr : r < t := hp
    exact .neg ⟨r, hr.trans ht⟩ ⟨t, ht⟩ (by intro h; exact hr.ne (congrArg Fin.val h))
  | conj a b t =>
    have ha : a < t := hp.1
    have hb : b < t := hp.2
    exact .conj ⟨a, ha.trans ht⟩ ⟨b, hb.trans ht⟩ ⟨t, ht⟩
      (by intro h; exact ha.ne (congrArg Fin.val h))
      (by intro h; exact hb.ne (congrArg Fin.val h))

@[simp] theorem RawAssignment.toAssignment_target {n : Nat} (a : RawAssignment)
    (ht : a.target < n) (hp : a.Topological) :
    (a.toAssignment ht hp).target.val = a.target := by
  cases a <;> rfl

def restrict (n : Nat) (s : Nat → Bool) : Bits n := fun i => s i.val

theorem RawAssignment.toAssignment_eval {n : Nat} (a : RawAssignment)
    (ht : a.target < n) (hp : a.Topological) (s : Nat → Bool) :
    (a.toAssignment ht hp).eval (restrict n s) = restrict n (a.eval s) := by
  cases a <;> funext i <;>
    simp [RawAssignment.toAssignment, Assignment.eval, Assignment.target,
      Assignment.value, RawAssignment.eval, RawAssignment.target, RawAssignment.value,
      restrict, Function.update_apply, Fin.ext_iff]

/-- A list is bounded only after proving every addressed node topological and in range. -/
def boundProgram (n : Nat) (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological) :
    List (Assignment n) :=
  nodes.attach.map (fun a => a.val.toAssignment (ht a.val a.property) (hp a.val a.property))

@[simp] theorem boundProgram_length (n : Nat) (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological) :
    (boundProgram n nodes ht hp).length = nodes.length := by simp [boundProgram]

@[simp] theorem boundProgram_cons (n : Nat) (a : RawAssignment) (nodes : List RawAssignment)
    (ht : ∀ b ∈ a :: nodes, b.target < n) (hp : ∀ b ∈ a :: nodes, b.Topological) :
    boundProgram n (a :: nodes) ht hp = a.toAssignment (ht a (by simp)) (hp a (by simp)) ::
      boundProgram n nodes (fun b hb => ht b (by simp [hb]))
        (fun b hb => hp b (by simp [hb])) := by
  simp [boundProgram, List.attach_cons, List.map_map, Function.comp_def]

theorem boundProgram_correct (n : Nat) (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological)
    (s : Nat → Bool) :
    evalAssignments (boundProgram n nodes ht hp) (restrict n s) = restrict n (rawRun nodes s) := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a nodes ih =>
    rw [boundProgram_cons]
    change evalAssignments (boundProgram n nodes _ _)
      ((a.toAssignment _ _).eval (restrict n s)) = restrict n (rawRun nodes (a.eval s))
    rw [RawAssignment.toAssignment_eval, ih]

theorem boundProgram_targets (n : Nat) (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes, a.target < n) (hp : ∀ a ∈ nodes, a.Topological) :
    (boundProgram n nodes ht hp).map (fun a => a.target.val) = nodes.map RawAssignment.target := by
  induction nodes with
  | nil => rfl
  | cons a nodes ih => simp [boundProgram_cons, ih]

end ShiReversibleFormula
