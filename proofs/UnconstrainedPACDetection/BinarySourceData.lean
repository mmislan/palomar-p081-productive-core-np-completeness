module

public import proofs.UnconstrainedPACDetection.BinaryFields
public import proofs.UnconstrainedPACDetection.Source

@[expose] public section

namespace UnconstrainedPACDetection.BinarySourceData

structure DenseSource where
  entities : ℕ
  reactions : ℕ
  values : List ℕ
  deriving DecidableEq

def DenseSource.WellFormed (s : DenseSource) : Prop :=
  s.values.length = 2 * (s.entities * s.reactions)

def DenseSource.toSource (s : DenseSource) : ReversibleSource (Fin s.entities) (Fin s.reactions) where
  left r x := s.values.getD (r.val * s.entities + x.val) 0
  right r x := s.values.getD (s.entities * s.reactions + r.val * s.entities + x.val) 0

def DenseSource.encode (s : DenseSource) : List Bool :=
  BinaryFields.encode (s.entities.bits :: s.reactions.bits :: s.values.map Nat.bits)

def decode (bits : List Bool) : Option DenseSource := do
  let fields ← BinaryFields.decode bits
  match fields with
  | m :: n :: values =>
      let s : DenseSource := ⟨BinaryFields.readNat m, BinaryFields.readNat n,
        values.map BinaryFields.readNat⟩
      if s.values.length = 2 * (s.entities * s.reactions) ∧ s.encode = bits then some s else none
  | _ => none

@[simp] theorem decode_encode (s : DenseSource) (h : s.WellFormed) : decode s.encode = some s := by
  cases s with
  | mk m n values =>
    simp [decode, DenseSource.encode, DenseSource.WellFormed, List.map_map, Function.comp_def] at h ⊢
    exact h

theorem decode_wellFormed {bits : List Bool} {s : DenseSource} (h : decode bits = some s) :
    s.WellFormed := by
  unfold decode at h
  cases hf : BinaryFields.decode bits with
  | none => simp [hf] at h
  | some fields =>
    simp only [hf] at h
    cases fields with
    | nil => simp at h
    | cons m fields =>
      cases fields with
      | nil => simp at h
      | cons n values =>
        dsimp at h
        split_ifs at h with hs
        · cases h
          exact hs.1

theorem decode_reencode {bits : List Bool} {s : DenseSource} (h : decode bits = some s) :
    s.encode = bits := by
  unfold decode at h
  cases hf : BinaryFields.decode bits with
  | none => simp [hf] at h
  | some fields =>
    simp only [hf] at h
    cases fields with
    | nil => simp at h
    | cons m fields =>
      cases fields with
      | nil => simp at h
      | cons n values =>
        dsimp at h
        split_ifs at h with hs
        · cases h
          exact hs.2

end UnconstrainedPACDetection.BinarySourceData
