import «BQP-closed-references»
import «BQP-canonical-paths»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow

abbrev BranchState := ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool

def StepLaws (sTr : BranchState → ℕ → BranchState) : Prop :=
∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
        sTr (ph, tl, tr, ct, de, bd, w) 0 = (ph, tl.tail, tl.headI :: tr, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 1 = (ph, tr.headI :: tl, tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 2
          = (ph + (if tr.headI && w.headI then 4 else 0), tl, w.headI :: tr.tail, ct, de,
              bd || w.isEmpty, w.tail)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 3
          = (ph + (if tr.headI then 1 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 4
          = (ph + (if tr.headI then 2 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 5 = (ph, tl, (!tr.headI) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 6 = (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 7
          = (ph, tl, (xor tr.headI ct) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 8
          = (ph, tl, tr.headI :: tr.tail, ct, de || !tr.headI, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 9 = (ph, tl, tr.headI :: tr.tail, ct, de, true, w)
      ∧ (∀ c : ℕ, sTr (ph, tl, tr, ct, de, bd, w) c
            = sTr (ph, tl, tr, ct, de, bd, w) (c % 16))

/-- One coherent machine/evaluator witness from the rebuilt single-run theorem. -/
structure Checker where
  step : BranchState → ℕ → BranchState
  encode : List ℕ → PvsNP.Str
  count : List ℕ → ℕ
  eval : List ℕ → List Bool → Option ℕ
  relation : ZMod 8 → PvsNP.Str × PvsNP.Str → Bool
  step_laws : StepLaws step
  encode_nil : encode [] = []
  encode_cons : ∀ c P, encode (c :: P) = encode P ++
    [decide (c / 8 % 2 = 1), decide (c / 4 % 2 = 1),
     decide (c / 2 % 2 = 1), decide (c % 2 = 1)]
  encode_length : ∀ P, (encode P).length = 4 * P.length
  count_nil : count [] = 0
  count_cons : ∀ c P, count (c :: P) = (if c % 16 = 2 then 1 else 0) + count P
  eval_fold : ∀ P bs, eval P bs =
    match P.foldl step (0, [], [], false, false, false, bs) with
    | (ph, _, _, _, de, bd, w) => if de || bd || !w.isEmpty then none else some ph.val
  polyTime : ∀ d, PvsNP.PolyTimeChecker (relation d)
  relation_eval : ∀ d Q w, relation d (encode Q, w) = decide (eval Q w = some d.val)
  count_eval : ∀ d Q, ShiClassPP.countAccept (relation d) (encode Q) (count Q) =
    (Finset.univ.filter (fun b : Fin (count Q) → Bool => eval Q (List.ofFn b) = some d.val)).card

 theorem checker_nonempty : Nonempty Checker := by
  obtain ⟨sTr, enc, hc, ev, R, pol, hstep, hen0, henc, hlen, hc0, hcc, hev,
    hcadd, hencadd, hfold, hPT, hM, hpol, h16, hR, hcount, hrest⟩ := BQPChecked.reference19
  exact ⟨{
    step := sTr
    encode := enc
    count := hc
    eval := ev
    relation := R
    step_laws := hstep
    encode_nil := hen0
    encode_cons := henc
    encode_length := hlen
    count_nil := hc0
    count_cons := hcc
    eval_fold := hev
    polyTime := hPT
    relation_eval := hR
    count_eval := hcount }⟩

noncomputable def checker : Checker := Classical.choice checker_nonempty

def wrap (i : ℕ) (body : List ℕ) : List ℕ :=
  List.replicate i 1 ++ (body ++ List.replicate i 0)

def gateBlock {n : ℕ} : Instr n → List ℕ
  | .h i => wrap i [2]
  | .s i => wrap i [4]
  | .t i => wrap i [3]
  | .x i => wrap i [5]
  | .cnot i j _ =>
    if (i : ℕ) < (j : ℕ) then
      wrap i ([6] ++ (List.replicate ((j : ℕ) - i) 1 ++
        ([7] ++ List.replicate ((j : ℕ) - i) 0)))
    else wrap j (List.replicate ((i : ℕ) - j) 1 ++
      ([6] ++ (List.replicate ((i : ℕ) - j) 0 ++ [7])))

def adjointBlock {n : ℕ} (g : Instr n) : List ℕ :=
  match g with
  | .s i => wrap i [4,4,4]
  | .t i => wrap i [3,3,3,3,3,3,3]
  | _ => gateBlock g

def forwardBody {n : ℕ} (gs : List (Instr n)) : List ℕ := (gs.map gateBlock).flatten

def adjointBody {n : ℕ} (gs : List (Instr n)) : List ℕ :=
  (gs.reverse.map adjointBlock).flatten

def load : List Bool → List ℕ
  | [] => []
  | b :: l => (if b then [5,1] else [1]) ++ load l

def endpoint : List Bool → List ℕ
  | [] => []
  | b :: l => (if b then [8,1] else [5,8,5,1]) ++ endpoint l

def paddedInput {n : ℕ} (m : ℕ) (x : Bits n) : List Bool :=
  List.ofFn (Fin.append x (fun _ : Fin m => false))

/-- Load input, run the forward circuit, test the output, run the adjoint,
then test return to the input basis state. -/
def compile {n m : ℕ} (gs : List (Instr (n + m))) (x : Bits n) (out : Fin (n + m)) : List ℕ :=
  load (paddedInput m x) ++ (List.replicate (n + m) 0 ++ (forwardBody gs ++
    (wrap out [8] ++ (adjointBody gs ++ (endpoint (paddedInput m x) ++
      List.replicate (n + m) 0)))))

end BQPProgram
