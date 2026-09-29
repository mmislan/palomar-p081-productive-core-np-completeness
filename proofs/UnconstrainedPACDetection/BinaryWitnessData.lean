module

public import proofs.UnconstrainedPACDetection.BinaryFields
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace UnconstrainedPACDetection.BinaryWitnessData

structure Witness where
  mask : List Bool
  flow : List ℤ
  deriving DecidableEq

def Witness.encode (w : Witness) : List Bool :=
  BinaryFields.encode (w.mask :: w.flow.map BinaryFields.writeInt)

def decode (bits : List Bool) : Option Witness := do
  let fields ← BinaryFields.decode bits
  match fields with
  | [] => none
  | mask :: fields =>
      let flow ← BinaryFields.readInts fields
      pure ⟨mask, flow⟩

@[simp] theorem decode_encode (w : Witness) : decode w.encode = some w := by
  cases w
  simp [decode, Witness.encode]

def Witness.entities (w : Witness) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun x => w.mask.getD x.val false = true

def Witness.values (w : Witness) (n : ℕ) : Fin n → ℤ :=
  fun r => w.flow.getD r.val 0

def fromCandidate {m n : ℕ} (X : Finset (Fin m)) (flow : Fin n → ℤ) : Witness :=
  ⟨List.ofFn (fun x : Fin m => decide (x ∈ X)), List.ofFn flow⟩

@[simp] theorem fromCandidate_mask_length {m n : ℕ} (X : Finset (Fin m)) (flow : Fin n → ℤ) :
    (fromCandidate X flow).mask.length = m := by simp [fromCandidate]

@[simp] theorem fromCandidate_flow_length {m n : ℕ} (X : Finset (Fin m)) (flow : Fin n → ℤ) :
    (fromCandidate X flow).flow.length = n := by simp [fromCandidate]

@[simp] theorem fromCandidate_entities {m n : ℕ} (X : Finset (Fin m)) (flow : Fin n → ℤ) :
    (fromCandidate X flow).entities m = X := by
  ext x
  simp [fromCandidate, Witness.entities, List.getD]

@[simp] theorem fromCandidate_values {m n : ℕ} (X : Finset (Fin m)) (flow : Fin n → ℤ) :
    (fromCandidate X flow).values n = flow := by
  funext r
  simp [fromCandidate, Witness.values, List.getD]

end UnconstrainedPACDetection.BinaryWitnessData
