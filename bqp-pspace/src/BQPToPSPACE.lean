/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

BQP ⊆ PSPACE by composing the published BQP ⊆ PP with PP ⊆ PSPACE (plan task S15).
-/
import PPToPSPACE
import «BQP-final-inclusion»

set_option autoImplicit false

/-- **`BQP ⊆ PSPACE`** for the original circuit-family BQP and the corrected
finite-multistack PSPACE. -/
theorem ShiBQP.bqp_subset_pspace : ShiBQP.BQP ⊆ ShiSpace.PSPACE := by
  intro L hL
  exact ShiSpace.pp_subset_pspace (ShiBQP.bqp_subset_pp hL)
