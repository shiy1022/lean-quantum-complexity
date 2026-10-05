import QIP.Smoke

/-! Fresh-import audit of the Q00 smoke module. -/

#check (ShiQIP.smoke_two_mul : ∀ x : ℝ, 2 * x = x + x)
#print axioms ShiQIP.smoke_two_mul
