module

public import proofs.UnconstrainedPACDetection.FormulaLookupBoundary
public import proofs.UnconstrainedPACDetection.VerifierEqualityFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupMatching
open Complexity SAT FormulaLookupScan

def marked (xs : List Bool) : List Bool := xs ++ [true]

theorem marked_positive (xs : List Bool) : 0 < BinaryFields.readNat (marked xs) := by
  induction xs with
  | nil => simp [marked,BinaryFields.readNat,Nat.bit]
  | cons b xs ih =>
    cases b <;> simp [marked,BinaryFields.readNat,Nat.bit] at *
    omega

theorem marked_injective (xs ys : List Bool) :
    BinaryFields.readNat (marked xs) = BinaryFields.readNat (marked ys) ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons b ys =>
      have hp := marked_positive ys
      cases b <;> simp [marked,BinaryFields.readNat,Nat.bit] at * <;> omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hp := marked_positive xs
      cases a <;> simp [marked,BinaryFields.readNat,Nat.bit] at *
      omega
    | cons b ys =>
      have ht := ih ys
      cases a <;> cases b <;>
        simp only [marked,List.cons_append,BinaryFields.readNat,Nat.bit] at * <;>
        simp_all <;> omega

theorem marked_compare (xs ys : List Bool) :
    VerifierBinaryEquality.compare true (marked xs) (marked ys) = decide (xs = ys) := by
  apply Bool.eq_iff_iff.mpr
  simp only [VerifierBinaryEquality.equality_iff,decide_eq_true_eq,marked_injective]
  exact eq_comm

theorem raw_lookup (φ : CNF) (i c : Nat) :
    (run none i φ.encode).raw =
      (((FormulaOccurrenceLookup.indexedFrom c φ)[i]?).map (fun z => z.2.encodeRaw)).getD [] := by
  induction φ generalizing i c with
  | nil => simp [run,FormulaOccurrenceLookup.indexedFrom]
  | cons ls φ ih =>
    simp only [CNF.encode_cons,List.append_assoc,clause,
      FormulaOccurrenceLookup.indexedFrom,List.getElem?_append,List.length_map]
    by_cases hi : i < ls.length
    · simp [hi]
    · simp only [dite_eq_right hi,ite_eq_right hi,List.cons_append,List.nil_append,run,event,
        Bool.true_eq_false,↓reduceIte]
      exact ih (i-ls.length) (c+1)

theorem literal_raw_injective (l k : Lit) : l.encodeRaw = k.encodeRaw ↔ l = k := by
  constructor
  · intro h
    have he := congrArg Lit.decodeRaw? h
    simpa using he
  · rintro rfl
    rfl

def target (v : Nat) (b : Bool) : List Bool := (⟨!b,v⟩ : Lit).encodeRaw

/-- The exact comparison consumed by the coefficient machine, including the dummy none case. -/
theorem blocking_compare (φ : CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (b : Bool) :
    VerifierBinaryEquality.compare true (marked (run none i.val φ.encode).raw)
      (marked (target v.val b)) = FormulaWiring.blocked φ i v b := by
  rw [marked_compare,raw_lookup φ i.val 0,FormulaOccurrenceLookup.occurrences_eq]
  change decide (((FormulaWiring.lookup φ i).map (fun z => z.2.encodeRaw)).getD [] = target v.val b) = _
  cases he : FormulaWiring.lookup φ i with
  | none => simp [he,FormulaWiring.blocked,target,Lit.encodeRaw]
  | some z =>
    obtain ⟨j,l⟩ := z
    simp only [Option.map_some,Option.getD_some,target,literal_raw_injective]
    obtain ⟨s,w⟩ := l
    cases s <;> cases b <;> simp [FormulaWiring.blocked,he]
    all_goals exact Bool.eq_iff_iff.mpr (by simp)

end UnconstrainedPACDetection.FormulaLookupMatching
