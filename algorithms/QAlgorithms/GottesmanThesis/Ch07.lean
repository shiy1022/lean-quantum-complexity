import QAlgorithms.Defs.FTCircuit

/-!
# Gottesman thesis, Chapter 7: bounds on quantum error-correcting codes

D. Gottesman, *Stabilizer codes and quantum error correction* (PhD thesis, 1997), cited
"Gottesman thesis p.N" (PDF pages).
-/

namespace QAlgorithms.GottesmanThesis

/-- Gottesman thesis §7.5, pp.90–91 (unnumbered): the quantum capacity of the qubit erasure
channel with erasure probability `p` is `max(0, 1 − 2p)`.

The erasure channel (frozen `erasureChannel n p`) acts independently on each of the `n` qubits:
with probability `1 − p` the qubit passes unchanged with flag `0`, with probability `p` it is
replaced by the maximally mixed state with flag `1`, so the receiver knows which qubits were
erased. A rate `R` is achievable (frozen `IsAchievableQRate`) when for all `ε, δ > 0` and all large
`n` there are an encoding channel of `k ≥ (R − δ) n` qubits into `n` qubits and a decoding channel
(seeing the flags) whose composite with the erasure channel has entanglement fidelity `≥ 1 − ε`
(the 1-EPP picture of §7.4; no classical feedback). The capacity being `max(0, 1 − 2p)` is stated
as: the achievable rates are exactly the `R ≤ max(0, 1 − 2p)` (the δ-slack in the definition makes
the set of achievable rates closed, so the supremum is attained).

Erratum (author's errata page): the thesis's proof of the upper bound `1 − 2p` assumes no
superadditivity when a noiseless channel is added to a zero-rate channel; the value itself is the
established one (Bennett–DiVincenzo–Smolin), and is stated unchanged. -/
theorem erasureChannel_capacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) :
    IsAchievableQRate (fun n => erasureChannel n p) R ↔ R ≤ max 0 (1 - 2 * p) := by
  sorry

end QAlgorithms.GottesmanThesis
