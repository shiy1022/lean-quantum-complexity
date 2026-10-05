import «BQP-map-first-io»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPMapFirst
open Turing Turing.TM2

def outputs (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (x y w : List Bool) (t : ℕ)
    (h : TM2OutputsInTime tm (x.map ea.symm) (some (y.map eb.symm)) t) :
    TM2OutputsInTime (machine tm ea eb) (pair x w) (some (pair y w))
      (t+2*x.length+2*w.length+2*y.length+5) := by
  refine { steps := (2*x.length+w.length+2)+h.steps+(w.length+2*y.length+3)
           steps_le_m := by have hb := h.steps_le_m; omega
           evals_in_steps := ?_ }
  have hd := delegated_run tm ea eb (extras [] [] w.reverse []) h.steps
    (some (initList tm (x.map ea.symm))) (haltList tm (y.map eb.symm)) h.evals_in_steps
  have hp := iterate_chain _ _ _ _ _ _ (input_prefix tm ea eb x w) hd
  exact iterate_chain _ _ _ _ _ _ hp (output_suffix tm ea eb y w)

end BQPMapFirst
