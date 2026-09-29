module

public import proofs.UnconstrainedPACDetection.BinarySourceData
public import proofs.UnconstrainedPACDetection.BinaryWitnessData
public import Mathlib.Data.List.GetD

@[expose] public section

/-! Exact canonical source and witness field positions for a common reaction. -/
namespace UnconstrainedPACDetection.VerifierCanonicalCoordinates

theorem encoded_split (fs : List (List Bool)) (i : ℕ) (hi : i < fs.length) :
    BinaryFields.encode fs = BinaryFields.encode (fs.take i) ++
      (BinaryFields.encodeField fs[i] ++ BinaryFields.encode (fs.drop (i+1))) := by
  have h : fs = fs.take i ++ fs[i] :: fs.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hi]
    exact (List.take_append_drop i fs).symm
  have he := congrArg BinaryFields.encode h
  simpa only [BinaryFields.encode,List.flatMap_append,List.flatMap_cons] using he

theorem mapped_split {α : Type} (f : α → List Bool) (xs : List α) (i : ℕ) (d : α)
    (hi : i < xs.length) :
    BinaryFields.encode (xs.map f) = BinaryFields.encode ((xs.take i).map f) ++
      (BinaryFields.encodeField (f (xs.getD i d)) ++ BinaryFields.encode ((xs.drop (i+1)).map f)) := by
  have h := encoded_split (xs.map f) i (by simpa using hi)
  rw [List.getD_eq_getElem xs d hi]
  simpa using h

def valueIndex (s : BinarySourceData.DenseSource) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) : ℕ :=
  (if isRight then s.entities*s.reactions else 0)+r.val*s.entities+x.val

def coefficient (s : BinarySourceData.DenseSource) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) : ℕ :=
  if isRight then s.toSource.right r x else s.toSource.left r x

theorem valueIndex_lt (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) : valueIndex s isRight r x < s.values.length := by
  have hr := Nat.mul_le_mul_right s.entities (Nat.succ_le_of_lt r.isLt)
  have hx := x.isLt
  have hb : r.val*s.entities+x.val < s.entities*s.reactions := by nlinarith
  change s.values.length = 2*(s.entities*s.reactions) at hs
  cases isRight <;> simp only [valueIndex,Bool.false_eq_true,↓reduceIte,zero_add] <;> omega

theorem coefficient_getD (s : BinarySourceData.DenseSource) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) :
    coefficient s isRight r x = s.values.getD (valueIndex s isRight r x) 0 := by
  cases isRight <;> simp [coefficient,valueIndex,BinarySourceData.DenseSource.toSource]

def sourcePrefix (s : BinarySourceData.DenseSource) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) : List (List Bool) :=
  s.entities.bits :: s.reactions.bits :: (s.values.take (valueIndex s isRight r x)).map Nat.bits

def sourceSuffix (s : BinarySourceData.DenseSource) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) : List Bool :=
  BinaryFields.encode ((s.values.drop (valueIndex s isRight r x+1)).map Nat.bits)

theorem source_split (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) :
    s.encode = BinaryFields.encode (sourcePrefix s isRight r x) ++
      (BinaryFields.encodeField (coefficient s isRight r x).bits ++ sourceSuffix s isRight r x) := by
  have h := mapped_split Nat.bits s.values (valueIndex s isRight r x) 0 (valueIndex_lt s hs isRight r x)
  change BinaryFields.encodeField s.entities.bits ++
    (BinaryFields.encodeField s.reactions.bits ++ BinaryFields.encode (s.values.map Nat.bits)) = _
  rw [h]
  simp [sourcePrefix,sourceSuffix,BinaryFields.encode,coefficient_getD,List.append_assoc]

theorem sourcePrefix_length (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (isRight : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) :
    (sourcePrefix s isRight r x).length = 2+valueIndex s isRight r x := by
  have h := valueIndex_lt s hs isRight r x
  simp [sourcePrefix,List.length_take,min_eq_left (Nat.le_of_lt h)]
  omega

def witnessPrefix (w : BinaryWitnessData.Witness) (r : ℕ) : List (List Bool) :=
  w.mask :: (w.flow.take r).map BinaryFields.writeInt
def witnessSuffix (w : BinaryWitnessData.Witness) (r : ℕ) : List Bool :=
  BinaryFields.encode ((w.flow.drop (r+1)).map BinaryFields.writeInt)

theorem witness_split (w : BinaryWitnessData.Witness) (r : ℕ) (hr : r < w.flow.length) :
    w.encode = BinaryFields.encode (witnessPrefix w r) ++
      (BinaryFields.encodeField (BinaryFields.writeInt (w.flow.getD r 0)) ++ witnessSuffix w r) := by
  have h := mapped_split BinaryFields.writeInt w.flow r 0 hr
  change BinaryFields.encodeField w.mask ++ BinaryFields.encode (w.flow.map BinaryFields.writeInt) = _
  rw [h]
  simp [witnessPrefix,witnessSuffix,BinaryFields.encode,List.append_assoc]

theorem witnessPrefix_length (w : BinaryWitnessData.Witness) (r : ℕ) (hr : r < w.flow.length) :
    (witnessPrefix w r).length = 1+r := by
  simp [witnessPrefix,List.length_take,min_eq_left (Nat.le_of_lt hr)]
  omega

end UnconstrainedPACDetection.VerifierCanonicalCoordinates
