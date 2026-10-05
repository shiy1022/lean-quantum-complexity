import «AMPUNI-layout-residual-exact»
import «AMPUNI-readout-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Turing Turing.TM2
namespace ShiTMReadoutLookup
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev core (k : Fin 14) : TopK := .inl (.inl k)
abbrev destination := ShiTMReadout.wire

inductive Label where
  | wire | afterPiece | afterBase | finishPiece | finishBase | finished
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList
  [.wire, .afterPiece, .afterBase, .finishPiece, .finishBase, .finished]
  (by intro l; cases l <;> simp)

/-- The destructive layout lookup, specialized to write directly into a
readout register. Its discarded marks go to stack 10, avoiding all four
readout registers. Other completed readout values therefore remain intact. -/
def machine (h : Fin 4) : Label → Stmt TopGam Label Sig
  | .wire => .pop (core 1) pop (.branch isMark
      (.pop (core 0) pop (.branch isSome
        (.push (core 3) (cst .mark) (.goto (fun _ => .wire)))
        (.goto (fun _ => .finishPiece))))
      (.goto (fun _ => .afterPiece)))
  | .afterPiece => .pop (core 3) pop (.branch isSome
      (.push (core 10) get (.goto (fun _ => .afterPiece)))
      (.goto (fun _ => .afterBase)))
  | .afterBase => .pop (core 2) pop (.branch isMark
      (.push (core 10) get (.goto (fun _ => .afterBase)))
      (.goto (fun _ => .wire)))
  | .finishPiece => .pop (core 2) pop (.branch isMark
      (.push (destination h) get (.goto (fun _ => .finishPiece)))
      (.goto (fun _ => .finishBase)))
  | .finishBase => .pop (core 3) pop (.branch isSome
      (.push (destination h) get (.goto (fun _ => .finishBase)))
      (.goto (fun _ => .finished)))
  | .finished => .halt

def run (h : Fin 4) : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step (machine h))

def finiteMachine (h : Fin 4) : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := core 0
  k₁ := destination h
  Γ := TopGam
  Λ := Label
  main := .wire
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine h

private theorem destination_ne (h : Fin 4) (k : Fin 14)
    (hk : k.val < 4 ∨ 7 < k.val) : destination h ≠ core k := by
  intro he
  have hv := congrArg (fun j : TopK => match j with
    | .inl (.inl i) => i.val
    | _ => 0) he
  change h.val+4 = k.val at hv
  omega

/-- Reuse the same published WIRE-2 contract as the existing circuit parser,
with only its output and discard registers changed. -/
noncomputable def lookupRunner (h : Fin 4) := by
  have hs := Classical.choose_spec
    (Classical.choose_spec ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact)
  exact hs.2.2.2.2.1 (machine h)
    (kv := core 0) (kl := core 1) (kb := core 2) (kd := core 3)
    (ku := destination h) (kr := core 10)
    (l1 := .wire) (la := .afterPiece) (la2 := .afterBase)
    (lf := .finishPiece) (lo := .finishBase) (lend := .finished)
    (mv := .mark) (ml := .mark) (dl := .delim)
    (mb := .mark) (db := .delim) (mdc := .mark) (m := .mark)
    (by decide) (by decide) (by decide) (Ne.symm (destination_ne h 0 (by decide))) (by decide)
    (by decide) (by decide) (Ne.symm (destination_ne h 1 (by decide))) (by decide)
    (by decide) (Ne.symm (destination_ne h 2 (by decide))) (by decide)
    (Ne.symm (destination_ne h 3 (by decide))) (by decide) (destination_ne h 10 (by decide))
    rfl rfl rfl rfl rfl
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl)
    rfl rfl
    depth cost (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (pieceCells Prod.fst) (pieceCells Prod.snd)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl

/-- Lookup preserves every stack outside its six explicitly named ports.
In particular, other readout registers, the output accumulator, and all
retained headers and archive are unchanged. -/
theorem lookup_run (h : Fin 4) (ps : List (Nat × Nat)) (w : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hw : w < (ps.map Prod.fst).sum)
    (h0 : S (core 0) = List.replicate w Cell.mark)
    (h1 : S (core 1) = pieceCells Prod.fst ps)
    (h2 : S (core 2) = pieceCells Prod.snd ps)
    (h3 : S (core 3) = []) :
    ∃ (v' : Sig) (U : ∀ k, List (TopGam k)),
      (run h)^[cost ps w] (some ⟨some .wire, v, S⟩) =
        some ⟨some .finished, v', U⟩
      ∧ U (destination h) = List.replicate (depth ps w) Cell.mark ++ S (destination h)
      ∧ U (core 0) = [] ∧ U (core 3) = []
      ∧ (U (core 1)).length ≤ (S (core 1)).length
      ∧ (U (core 2)).length ≤ (S (core 2)).length
      ∧ ∀ k, k ≠ core 0 → k ≠ core 1 → k ≠ core 2 → k ≠ core 3 →
          k ≠ destination h → k ≠ core 10 → U k = S k := by
  obtain ⟨v', U, hr, hd, hi, ht, _, _, _, _, hlen1, hlen2, hf⟩ :=
    lookupRunner h ps w v S hw h0 h1 h2 h3
  exact ⟨v', U, hr, hd, hi, ht, hlen1, hlen2, hf⟩

end ShiTMReadoutLookup
