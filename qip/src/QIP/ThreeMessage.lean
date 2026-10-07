import QIP.FamilyConstruction


/-!
# Q40 — `QIP = QIP(3)`

`qipm_subset_qip` gives `QIP(3) ⊆ QIP` directly. Conversely, a family deciding `A` is turned
into the three-message family `F.three` (`QIP.FamilyConstruction`), which decides `A`, has the
schedule `stdSchedule 3` on every input, and is a polynomial-time uniform, polynomially bounded
family of valid verifiers.
-/

namespace ShiQIP

/-- `QIP ⊆ QIP(3)`. -/
theorem qip_subset_qip3 : QIP ⊆ QIPm 3 := fun _ ⟨F, hF⟩ =>
  ⟨F.three, F.three_schedule, F.three_decides hF⟩

/-- **`QIP = QIP(3)`**: every promise problem with a polynomial-message quantum interactive proof
has one with exactly three messages (prover, verifier, prover). -/
theorem qip_eq_qip3 : QIP = QIPm 3 :=
  Set.Subset.antisymm qip_subset_qip3 (qipm_subset_qip 3)

/-- The language-level statement, through the promise embedding `ofLanguage L = (L, Lᶜ)`. -/
theorem ofLanguage_mem_qip_iff (L : Language Bool) :
    ofLanguage L ∈ QIP ↔ ofLanguage L ∈ QIPm 3 := by
  rw [qip_eq_qip3]

end ShiQIP
