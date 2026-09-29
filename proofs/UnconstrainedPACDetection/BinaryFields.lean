module

public import Mathlib.Data.Nat.Size
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A field consists of doubled data tokens `true,b`, followed by `false`.
Parsing consumes actual input bits, never a claimed numeric length. -/

namespace UnconstrainedPACDetection.BinaryFields

def encodeField : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodeField bs

def encode (fields : List (List Bool)) : List Bool := fields.flatMap encodeField

def decode : List Bool → Option (List (List Bool))
  | [] => some []
  | false :: rest => (List.cons []) <$> decode rest
  | [true] => none
  | true :: b :: rest => do
      let fields ← decode rest
      match fields with
      | [] => none
      | field :: fields => some ((b :: field) :: fields)

theorem decode_field_append (field suffix : List Bool) (fields : List (List Bool))
    (h : decode suffix = some fields) :
    decode (encodeField field ++ suffix) = some (field :: fields) := by
  induction field with
  | nil => simp [encodeField, decode, h]
  | cons b field ih => simp [encodeField, decode, ih]

@[simp] theorem decode_encode (fields : List (List Bool)) : decode (encode fields) = some fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    exact decode_field_append field (encode fields) fields ih

theorem encodeField_length (field : List Bool) : (encodeField field).length = 2 * field.length + 1 := by
  induction field with
  | nil => rfl
  | cons b field ih => simp [encodeField, ih]; omega

theorem encode_length (fields : List (List Bool)) :
    (encode fields).length = (fields.map (fun f => 2 * f.length + 1)).sum := by
  simp [encode, List.length_flatMap, encodeField_length]

def readNat : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (readNat bs)

@[simp] theorem readNat_bits (n : ℕ) : readNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp [Nat.bits_append_bit n b h, readNat, ih]

def writeInt (z : ℤ) : List Bool := decide (z < 0) :: z.natAbs.bits

def readInt : List Bool → Option ℤ
  | [] => none
  | sign :: bits => some (if sign then -(readNat bits : ℤ) else (readNat bits : ℤ))

@[simp] theorem readInt_writeInt (z : ℤ) : readInt (writeInt z) = some z := by
  by_cases h : z < 0
  · simp [writeInt, readInt, h, abs_of_neg h]
  · simp [writeInt, readInt, h, abs_of_nonneg (le_of_not_gt h)]

def readInts : List (List Bool) → Option (List ℤ)
  | [] => some []
  | f :: fs => do
      let z ← readInt f
      let zs ← readInts fs
      pure (z :: zs)

@[simp] theorem readInts_writeInts (zs : List ℤ) : readInts (zs.map writeInt) = some zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [readInts, ih]

end UnconstrainedPACDetection.BinaryFields
