-- Local reference copy of the PUBLISHED platform definition bundle `PvsNPFrontier`,
-- fetched verbatim from prove2.me so that theorems citing it compile locally.
import Definitions.Def_PvsNP
set_option autoImplicit false

namespace PvsNP

abbrev DecisionProblem := Language Bool

def inputLength (w : Str) : ℕ := w.length

def PolynomialBound (t : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, t n ≤ p.eval n

def coP : Set DecisionProblem := {L | Lᶜ ∈ P}

def coNP : Set DecisionProblem := {L | Lᶜ ∈ NP}

def NPHard (L : DecisionProblem) : Prop := ∀ A ∈ NP, PReducible A L

def FiniteWorkAlphabets (M : Turing.FinTM2) : Prop :=
  ∀ k, Finite (M.Γ k)

def FinitePolyTime {α β U V : Type} (ei : α → List U) (eo : β → List V)
    (f : α → β) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime ei eo f, FiniteWorkAlphabets M.tm

def parseData : ℕ → Str → Option (Str × Str)
  | 0, _ => none
  | _ + 1, true :: false :: rest => some ([], rest)
  | fuel + 1, false :: b :: rest =>
      (parseData fuel rest).map fun p => (b :: p.1, p.2)
  | _ + 1, _ => none

def bitsValue : Str → ℕ
  | [] => 0
  | b :: rest => Nat.bit b (bitsValue rest)

def parseLiteral (w : Str) : Option (Literal × Str) :=
  match w with
  | false :: sign :: rest =>
      (parseData (rest.length + 1) rest).bind fun p =>
        let i := bitsValue p.1
        if Nat.bits i = p.1 then some ((sign, i), p.2) else none
  | _ => none

def parseClauseAux : ℕ → Str → Option (Clause × Str)
  | 0, _ => none
  | _ + 1, true :: true :: rest => some ([], rest)
  | fuel + 1, w =>
      (parseLiteral w).bind fun p =>
        (parseClauseAux fuel p.2).map fun q => (p.1 :: q.1, q.2)

def parseCNFAux : ℕ → Str → Option CNF
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, w@(_ :: _) =>
      (parseClauseAux (w.length + 1) w).bind fun p =>
        (parseCNFAux fuel p.2).map (p.1 :: ·)

def parseCNF (w : Str) : Option CNF := parseCNFAux (w.length + 1) w

def variableNames (F : CNF) : List ℕ := (F.flatten.map Prod.snd).eraseDups

def certificateAssignment (F : CNF) (y : Str) (i : ℕ) : Bool :=
  (((variableNames F).zip y).lookup i).getD false

def satVerifier (wy : Str × Str) : Bool :=
  match parseCNF wy.1 with
  | none => false
  | some F =>
      if wy.2.length = (variableNames F).length then
        evalCNF (certificateAssignment F wy.2) F
      else false

structure TableauSpec where
  steps : ℕ
  interior : ℕ
  symbols : ℕ
  initialAllowed : List (List ℕ)
  acceptingSymbols : List ℕ
  allowedWindows : List (List ℕ)

def tableauWidth (S : TableauSpec) : ℕ := S.interior + 2

def tableauAlphabet (S : TableauSpec) : ℕ := S.symbols + 1

def tableauVar (S : TableauSpec) (t c a : ℕ) : ℕ :=
  (t * tableauWidth S + c) * tableauAlphabet S + a

def cellClauses (S : TableauSpec) (t c : ℕ) : CNF :=
  let as := List.range (tableauAlphabet S)
  [as.map fun a => (true, tableauVar S t c a)] ++
    as.flatMap fun a =>
      (as.filter fun b => a < b).map fun b =>
        [(false, tableauVar S t c a), (false, tableauVar S t c b)]

def cellsCNF (S : TableauSpec) : CNF :=
  (List.range (S.steps + 1)).flatMap fun t =>
    (List.range (tableauWidth S)).flatMap fun c => cellClauses S t c

def initialCNF (S : TableauSpec) : CNF :=
  (List.range (tableauWidth S)).flatMap fun c =>
    ((List.range (tableauAlphabet S)).filter fun a =>
      !(S.initialAllowed[c]?.getD []).contains a).map fun a =>
        [(false, tableauVar S 0 c a)]

def boundaryCNF (S : TableauSpec) : CNF :=
  (List.range (S.steps + 1)).flatMap fun t =>
    [[(true, tableauVar S t 0 0)],
     [(true, tableauVar S t (S.interior + 1) 0)]]

def acceptingCNF (S : TableauSpec) : CNF :=
  [(List.range (tableauWidth S)).flatMap fun c =>
    ((List.range (tableauAlphabet S)).filter fun a =>
      S.acceptingSymbols.contains a).map fun a =>
        (true, tableauVar S S.steps c a)]

def wordsOfLength (alphabet : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range alphabet).flatMap fun a =>
      (wordsOfLength alphabet n).map (a :: ·)

def windowValues (T : ℕ → ℕ → ℕ) (t c : ℕ) : List ℕ :=
  [T t c, T t (c+1), T t (c+2),
   T (t+1) c, T (t+1) (c+1), T (t+1) (c+2)]

def forbiddenWindowClause (S : TableauSpec) (t c : ℕ) (v : List ℕ) : Clause :=
  [(t,c), (t,c+1), (t,c+2), (t+1,c), (t+1,c+1), (t+1,c+2)].zipWith
    (fun pos a => (false, tableauVar S pos.1 pos.2 a)) v

def transitionCNF (S : TableauSpec) : CNF :=
  (List.range S.steps).flatMap fun t =>
    (List.range S.interior).flatMap fun c =>
      ((wordsOfLength (tableauAlphabet S) 6).filter fun v =>
        !S.allowedWindows.contains v).map (forbiddenWindowClause S t c)

def tableauCNF (S : TableauSpec) : CNF :=
  cellsCNF S ++ initialCNF S ++ boundaryCNF S ++
    acceptingCNF S ++ transitionCNF S

def TableauEncoding (S : TableauSpec) (τ : ℕ → Bool) (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ t ≤ S.steps, ∀ c < tableauWidth S, T t c < tableauAlphabet S) ∧
  ∀ t ≤ S.steps, ∀ c < tableauWidth S, ∀ a < tableauAlphabet S,
    τ (tableauVar S t c a) = true ↔ T t c = a

def ValidTableau (S : TableauSpec) (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ t ≤ S.steps, ∀ c < tableauWidth S, T t c < tableauAlphabet S) ∧
  (∀ c < tableauWidth S, T 0 c ∈ (S.initialAllowed[c]?.getD [])) ∧
  (∀ t ≤ S.steps, T t 0 = 0 ∧ T t (S.interior + 1) = 0) ∧
  (∃ c < tableauWidth S, T S.steps c ∈ S.acceptingSymbols) ∧
  (∀ t < S.steps, ∀ c < S.interior,
    windowValues T t c ∈ S.allowedWindows)

def encodeTableauSpec (S : TableauSpec) : Str :=
  encodeCNF
    ([List.replicate S.steps (true, 0), List.replicate S.interior (true, 0),
      List.replicate S.symbols (true, 0),
      List.replicate S.initialAllowed.length (true, 0)] ++
     S.initialAllowed.map (fun xs => xs.map (fun a => (true, a))) ++
     [S.acceptingSymbols.map (fun a => (true, a))] ++
     S.allowedWindows.map (fun xs => xs.map (fun a => (true, a))))

def MachineTableauSpec (S : TableauSpec) : Prop :=
  0 < S.steps ∧ 0 < S.interior ∧ 0 ∉ S.acceptingSymbols ∧
  S.initialAllowed.length = tableauWidth S ∧
  (∀ xs ∈ S.initialAllowed, ∀ a ∈ xs, a < tableauAlphabet S) ∧
  (∀ a ∈ S.acceptingSymbols, a < tableauAlphabet S) ∧
  (∀ xs ∈ S.allowedWindows, xs.length = 6 ∧ ∀ a ∈ xs, a < tableauAlphabet S)

def EXPTIME : Set DecisionProblem :=
  {L | ∃ χ : Str → Bool,
    (∃ M : Turing.TM2ComputableInTime (id : Str → Str) Computability.encodeBool χ,
      ∃ p : Polynomial ℕ, ∀ n, M.time n ≤ 2 ^ p.eval n) ∧
    ∀ w, w ∈ L ↔ χ w = true}

end PvsNP
