import ReversibleCleanHaltProgramTemplate
import ReversibleCounterTM2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- A checked finite continuation template with canonical raw-length input compiles directly into a polynomial-time TM2, including cleanup and its actual last halt. -/
theorem cleanTemplate_polytime (p : CounterProgramTemplate R) (input : R)
    (he : p.Embeds) (hr : p.Runs)
    (hready : ∀ n,p.ready (Function.update (fun _ : R => 0) input n))
    (hb : p.CounterBound Polynomial.X) (ht : p.PolynomiallyTimed Polynomial.X) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun xs => p.bytes (Function.update (fun _ : R => 0) input xs.length))) := by
  classical
  let q := cleanHaltProgramTemplate p
  letI : Fintype (q.Labels Unit) := q.finite Unit inferInstance
  obtain ⟨clock,hclock⟩ := (cleanHaltProgramTemplate_resources p Polynomial.X hb ht).2
  apply counterProgram_polytime (q.code (fun _ : Unit => .halt) ()) input (q.entry ())
    (fun xs => p.bytes (Function.update (fun _ : R => 0) input xs.length)) (clock+Polynomial.C 1)
  intro xs
  let initial := Function.update (fun _ : R => 0) input xs.length
  have hi : ∀ r,initial r ≤ Polynomial.X.eval xs.length := by
    intro r
    simp only [initial,Function.update_apply,Polynomial.eval_X]
    split_ifs <;> omega
  have ready := hready xs.length
  have run := cleanHaltProgramTemplate_halted_run p he hr initial [] ready
  rw [List.append_nil] at run
  refine ⟨q.steps initial+1,⟨none,fun _ => 0,p.bytes initial⟩,run,rfl,?_,rfl,?_⟩
  · intro r; rfl
  · have h := hclock xs.length initial hi ((cleanHaltProgramTemplate_ready p initial).2 ready)
    simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_right h 1

end ShiReversibleGenerator
