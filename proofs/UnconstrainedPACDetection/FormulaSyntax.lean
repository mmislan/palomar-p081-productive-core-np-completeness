module

public import proofs.Complexitylib.SAT.Verifier
public import proofs.UnconstrainedPACDetection.VerifierFieldParser

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSyntax
open Complexity SAT

inductive Mode where
  | boundary | ready | literal | dead
  deriving DecidableEq, Repr

instance : Fintype Mode where
  elems := {.boundary,.ready,.literal,.dead}
  complete := fun q => by cases q <;> simp

def tokenStep : Mode → EncToken → Mode
  | .dead, _ => .dead
  | .literal, .bit true => .literal
  | .literal, .litSep => .ready
  | .literal, _ => .dead
  | _, .bit _ => .literal
  | _, .clauseSep => .boundary
  | _, .litSep => .dead

def runTokens : Mode → List EncToken → Bool
  | q, [] => decide (q = .boundary)
  | q, t::ts => runTokens (tokenStep q t) ts

theorem dead_run (ts : List EncToken) : runTokens .dead ts = false := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa [runTokens,tokenStep] using ih

/-- Abstract the parser's forward raw literal and reversed current clause. -/
def classify : List Bool → Clause → Mode
  | [], c => if c = [] then .boundary else .ready
  | _::bs, _ => if ∀ b ∈ bs, b = true then .literal else .dead

theorem classify_bit (raw : List Bool) (c : Clause) (b : Bool) :
    classify (raw ++ [b]) c = tokenStep (classify raw c) (.bit b) := by
  cases raw with
  | nil => cases c <;> cases b <;> simp [classify,tokenStep]
  | cons s bs =>
    by_cases h : false ∈ bs
    · cases b <;> simp [classify,tokenStep,h]
    · cases b <;> simp [classify,tokenStep,h]

theorem parser_correct (ts : List EncToken) (raw : List Bool) (c : Clause) (f : CNF) :
    runTokens (classify raw c) ts = (parseTokensAux ts raw.reverse c f).isSome := by
  induction ts generalizing raw c f with
  | nil => cases raw <;> cases c <;> simp [runTokens,classify,parseTokensAux] <;> split <;> simp
  | cons t ts ih =>
    cases t with
    | bit b =>
      simpa only [runTokens,← classify_bit,parseTokensAux,List.reverse_append,
        List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] using ih (raw ++ [b]) c f
    | litSep =>
      cases raw with
      | nil => cases c <;> simp [classify,runTokens,parseTokensAux,Lit.decodeRaw?,tokenStep,dead_run]
      | cons s bs =>
        by_cases h : false ∈ bs
        · simp [runTokens,classify,h,tokenStep,parseTokensAux,Lit.decodeRaw?,dead_run]
        · simpa [runTokens,classify,h,tokenStep,parseTokensAux,Lit.decodeRaw?] using
            ih [] ({sign:=s,var:=bs.length}::c) f
    | clauseSep =>
      cases raw with
      | nil =>
        have hi := ih [] [] (c.reverse::f)
        cases c <;> simpa [runTokens,classify,tokenStep,parseTokensAux] using hi
      | cons s bs =>
        by_cases h : false ∈ bs <;>
          simp [runTokens,classify,h,tokenStep,parseTokensAux,dead_run]

def token : Bool → Bool → EncToken
  | false,false => .bit false
  | true,true => .bit true
  | false,true => .litSep
  | true,false => .clauseSep

abbrev State := Mode × Option Bool

def next : State → Bool → State
  | (q,none), b => (q,some b)
  | (q,some a), b => (tokenStep q (token a b),none)

def finish (q : State) : Bool := decide (q = (.boundary,none))

def run : State → List Bool → Bool
  | q, [] => finish q
  | q, b::bs => run (next q b) bs

theorem bits_correct (q : Mode) (xs : List Bool) :
    run (q,none) xs = match tokenize? xs with
      | none => false
      | some ts => runTokens q ts := by
  cases xs with
  | nil => simp [run,finish,runTokens,tokenize?]
  | cons a xs =>
    cases xs with
    | nil => simp [run,next,finish,tokenize?]
    | cons b xs =>
      have ih := bits_correct (tokenStep q (token a b)) xs
      cases a <;> cases b <;>
        simp only [token] at ih <;>
        simp only [run,next,token,tokenize?] <;>
        rw [ih] <;> cases tokenize? xs <;> rfl
termination_by xs.length

theorem run_correct (xs : List Bool) :
    run (.boundary,none) xs = (CNF.decode? xs).isSome := by
  rw [bits_correct]
  unfold CNF.decode?
  cases h : tokenize? xs with
  | none => rfl
  | some ts => simpa [classify] using parser_correct ts [] [] []

end UnconstrainedPACDetection.FormulaSyntax

