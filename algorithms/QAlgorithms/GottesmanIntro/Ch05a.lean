import QAlgorithms.Defs.FTCircuit

/-!
# Gottesman, *An introduction to quantum error correction*, §5.1–5.2: good extended rectangles
are correct; level reduction (Theorems 6, 7, Lemmas 2, 3)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages).

Standing assumptions of the section, all carried by the frozen definition layer: one
`[[n, 1, 2t + 1]]` code (p.19) with an ideal decoder (Def. 1) and fault-tolerant gadgets for
preparation, measurement, the gates `H`, `R_{π/8}`, CNOT, wait, and error correction (Defs. 2–5,
`FTProtocol.IsFaultTolerant`); faults are Pauli errors at the locations of the gadgets (p.20,
`PauliArrangement`); the correctness diagrams (72)–(74) and (83) are equalities of
superoperators, hence hold on all inputs including parts of entangled states (p.38).
-/

namespace QAlgorithms.GottesmanIntro

/-- Gottesman intro p.35, Theorem 6 (Good implies correct): "A good ExRec is correct."
Let `P` be a fault-tolerant protocol for an `[[n, 1, 2t + 1]]` code (gadgets satisfying
Defs. 2–5 with the ideal decoder of Def. 1). For every location type `κ` (preparation,
measurement, `H`, `R_{π/8}`, CNOT, wait) and every Pauli fault arrangement `F` of a full ExRec
of type `κ` (leading ECs, the gadget, trailing ECs; Def. 7) with at most `t` faults in total
(good, Def. 9), the ExRec is correct (Def. 8, diagrams (72)–(74)). -/
theorem good_exRec_correct (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (hgood : F.count P ∅ ≤ P.t) :
    ExRecCorrect P κ F ∅ := by
  sorry

/-- Gottesman intro p.36, Theorem 7: "Suppose a fault-tolerant circuit for `C` contains only
good extended rectangles. Then the output distribution of the fault-tolerant protocol is the same
as the output distribution of `C`." Let `P` be a fault-tolerant protocol (Defs. 2–5) whose
location gadgets have a common depth, and `C` a circuit of preparation, gate, measurement and
wait locations as in Def. 6 (no input, every qubit prepared first and measured last). Let `fa`
be a Pauli fault arrangement on the fault-tolerant circuit `C′ = ftCircuit P C` such that every
(full) ExRec of `C′` contains at most `t` faulty locations. Then the distribution of the
measurement record of the faulty `C′`, decoded classically by the measurement gadgets'
decoding (`ftDecode`), equals the output distribution of the ideal circuit `C`. -/
theorem output_eq_of_all_good (P : FTProtocol) (hP : P.IsFaultTolerant)
    (hdepth : P.HasUniformDepth) {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit)
    (fa : PauliArrangement)
    (hgood : ∀ ℓ ∈ C.locs, (faultyLocs (ftCircuit P C) fa ∩ exRecLocs P C ℓ ∅).card ≤ P.t) :
    pushDist (ftDecode P C) ((ftCircuit P C).outDist (pauliErr (ftCircuit P C) fa) 1) =
      C.idealOutDist := by
  sorry

/-- Gottesman intro p.38, Lemma 2: "If an ExRec is correct for an ideal decoder, it is correct
for a *-decoder." Let `P` be a fault-tolerant protocol and `W` a *-decoder for its ideal decoder
(a unitary from a block to one qubit ⊗ a syndrome register `Fin σ` whose syndrome-discarded
version is `P.dec`, p.37–38). For every ExRec type `κ`, every Pauli fault arrangement `F` and
every set `trunc` of removed trailing ECs (`∅` for a full ExRec; p.39: Lemma 2 "also works for
truncated ExRecs"), if the ExRec is correct for the ideal decoder then it is correct for `W`:
for a gate or wait ExRec, eq. (83) holds for some quantum operation `V` on the syndrome
registers (chosen after the faults); for a preparation ExRec, the *-decoded output is
`|0⟩⟨0| ⊗ τ` for some syndrome state `τ`; for a measurement ExRec, the syndrome is discarded. -/
theorem exRecCorrectStar_of_exRecCorrect (P : FTProtocol) (hP : P.IsFaultTolerant) {σ : ℕ}
    (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (hW : IsStarDecoder P.dec W) (κ : LocKind)
    (F : ExRecFaults κ) (trunc : Finset (Fin κ.trailCount)) (hcorr : ExRecCorrect P κ F trunc) :
    ExRecCorrectStar P W κ F trunc := by
  sorry

/-- Gottesman intro p.38, Lemma 3: "A good truncated ExRec is correct for both ideal decoders and
*-decoders." Let `P` be a fault-tolerant protocol (Defs. 2–5). For every ExRec type `κ`, every
nonempty set `trunc` of output blocks whose trailing EC is removed (a truncated ExRec, Def. 10;
measurement ExRecs have no trailing EC, so for them the hypothesis is void), and every Pauli
fault arrangement `F` with at most `t` faults in the remaining locations (good, Def. 10), the
truncated ExRec is correct for the ideal decoder, and it is correct for every *-decoder `W` of
the ideal decoder. -/
theorem good_truncated_exRec_correct (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (trunc : Finset (Fin κ.trailCount)) (htrunc : trunc.Nonempty)
    (hgood : F.count P trunc ≤ P.t) :
    ExRecCorrect P κ F trunc ∧
      ∀ (σ : ℕ) (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ), IsStarDecoder P.dec W →
        ExRecCorrectStar P W κ F trunc := by
  sorry

end QAlgorithms.GottesmanIntro
