module

public import proofs.IrrRAFEnumeration.CompletionQuery

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource

theorem unary_split (z : List Bool) :
    z = List.replicate (readUnary z).1 true ++ false :: (readUnary z).2 ∨
      z = List.replicate (readUnary z).1 true ∧ (readUnary z).2 = [] := by
  induction z with
  | nil => exact Or.inr ⟨rfl,rfl⟩
  | cons b z ih =>
    cases b with
    | false => exact Or.inl rfl
    | true =>
      rcases ih with h | ⟨h,ht⟩
      · left
        simpa [readUnary,List.replicate_succ] using congrArg (List.cons true) h
      · right
        constructor
        · simpa [readUnary,List.replicate_succ] using congrArg (List.cons true) h
        · exact ht

theorem unary_exact_of_bound (z : List Bool) (h : (readUnary z).1+1 ≤ z.length) :
    z = List.replicate (readUnary z).1 true ++ false :: (readUnary z).2 := by
  rcases unary_split z with he | ⟨he,_⟩
  · exact he
  · have hl := congrArg List.length he
    simp only [List.length_replicate] at hl
    omega

structure Parsed where
  knownCount : Nat
  moleculeCount : Nat
  reactionCount : Nat
  tail : List Bool

def parse (z : List Bool) : Parsed :=
  let p1 := readUnary z
  let p2 := readUnary p1.2
  let p3 := readUnary p2.2
  ⟨p1.1,p2.1,p3.1,p3.2⟩

theorem parse_headers (g d r : Nat) (tail : List Bool) :
    parse (headers g d r tail) = ⟨g,d,r,tail⟩ := by
  simp [parse,headers,readUnary_prefix]

/-- A total tolerant parser cannot pass even the header-length bound unless
all three real zero delimiters were present in the original input. -/
theorem parse_exact_of_bound (z : List Bool)
    (h : (parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount+3 ≤ z.length) :
    z = headers (parse z).knownCount (parse z).moleculeCount (parse z).reactionCount (parse z).tail := by
  let p1 := readUnary z
  let p2 := readUnary p1.2
  let p3 := readUnary p2.2
  change p1.1+p2.1+p3.1+3 ≤ z.length at h
  have e1 := unary_exact_of_bound z (by change p1.1+1 ≤ z.length; omega)
  have l1 := congrArg List.length e1
  change z.length = (List.replicate p1.1 true ++ false :: p1.2).length at l1
  simp only [List.length_append,List.length_replicate,List.length_cons] at l1
  have e2 := unary_exact_of_bound p1.2 (by change p2.1+1 ≤ p1.2.length; omega)
  have l2 := congrArg List.length e2
  change p1.2.length = (List.replicate p2.1 true ++ false :: p2.2).length at l2
  simp only [List.length_append,List.length_replicate,List.length_cons] at l2
  have e3 := unary_exact_of_bound p2.2 (by change p3.1+1 ≤ p2.2.length; omega)
  change z = headers p1.1 p2.1 p3.1 p3.2
  change z = List.replicate p1.1 true ++ false :: p1.2 at e1
  change p1.2 = List.replicate p2.1 true ++ false :: p2.2 at e2
  change p2.2 = List.replicate p3.1 true ++ false :: p3.2 at e3
  calc
    z = List.replicate p1.1 true ++ false :: p1.2 := e1
    _ = List.replicate p1.1 true ++ false ::
        (List.replicate p2.1 true ++ false :: p2.2) := congrArg (fun t => List.replicate p1.1 true ++ false :: t) e2
    _ = headers p1.1 p2.1 p3.1 p3.2 := congrArg
      (fun t => List.replicate p1.1 true ++ false :: (List.replicate p2.1 true ++ false :: t)) e3

def expectedBodyLength (p : Parsed) : Nat :=
  p.moleculeCount+3*p.reactionCount*p.moleculeCount+p.reactionCount+p.knownCount*p.reactionCount

def SizeCheck (z : List Bool) : Prop :=
  z.length = (parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount+3+expectedBodyLength (parse z)

theorem size_check_sound (z : List Bool) (h : SizeCheck z) :
    z = headers (parse z).knownCount (parse z).moleculeCount (parse z).reactionCount (parse z).tail ∧
      (parse z).tail.length = expectedBodyLength (parse z) := by
  have he := parse_exact_of_bound z (by unfold SizeCheck at h; omega)
  refine ⟨he,?_⟩
  have hl := congrArg List.length he
  simp only [headers,List.length_append,List.length_replicate,List.length_cons] at hl
  unfold SizeCheck at h
  omega

theorem bits_size_check {d r : Nat} (Q : RAF.CRS (Fin d) (Fin r))
    (C : RAF.Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) : SizeCheck (bits Q C G U) := by
  unfold SizeCheck
  rw [bits_length,bits_headers,parse_headers]
  dsimp only [expectedBodyLength]
  omega

end IrrRAFEnumeration.CompletionQuery
