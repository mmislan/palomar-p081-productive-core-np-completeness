module

public import proofs.UnconstrainedPACDetection.VerifierPreparedCertificate

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessGrammar
open Complexity Complexity.TM

inductive Phase where
  | maskMarker | maskPayload | flowMarker | signPayload
  | magnitudeMarker (valid : Bool) | magnitudePayload | bad | done
  deriving DecidableEq, Fintype

/-- Emissions count actual payloads/fields, never a claimed binary dimension. -/
def next (q : Phase) (b : Bool) : Phase × Bool × Bool :=
  match q with
  | .maskMarker => (if b then .maskPayload else .flowMarker,false,false)
  | .maskPayload => (.maskMarker,true,false)
  | .flowMarker => (if b then .signPayload else .bad,false,false)
  | .signPayload => (.magnitudeMarker (!b),false,false)
  | .magnitudeMarker valid =>
      if b then (.magnitudePayload,false,false)
      else (if valid then .flowMarker else .bad,false,valid)
  | .magnitudePayload => (.magnitudeMarker b,false,false)
  | .bad => (.bad,false,false)
  | .done => (.done,false,false)

def accept (q : Phase) : Bool := decide (q = .flowMarker)

def run (q : Phase) : List Bool → Phase × ℕ × ℕ
  | [] => (q,0,0)
  | b :: bs =>
      let a := next q b
      let r := run a.1 bs
      (r.1, (if a.2.1 then 1 else 0)+r.2.1, (if a.2.2 then 1 else 0)+r.2.2)

theorem run_append (q : Phase) (xs ys : List Bool) :
    run q (xs++ys) = let a := run q xs; let b := run a.1 ys;
      (b.1,a.2.1+b.2.1,a.2.2+b.2.2) := by
  induction xs generalizing q with
  | nil => simp [run]
  | cons x xs ih => simp [run,ih,Nat.add_assoc]

theorem mask_run (xs : List Bool) :
    run .maskMarker (BinaryFields.encodeField xs) = (.flowMarker,xs.length,0) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [BinaryFields.encodeField,run,next,ih,Nat.add_comm]

def lastBit : List Bool → Bool → Bool
  | [], a => a
  | b :: bs, _ => lastBit bs b

theorem magnitude_run (bits : List Bool) (a : Bool) :
    run (.magnitudeMarker a) (BinaryFields.encodeField bits) =
      (if lastBit bits a then .flowMarker else .bad,0,if lastBit bits a then 1 else 0) := by
  induction bits generalizing a with
  | nil => cases a <;> rfl
  | cons b bs ih =>
    simp only [BinaryFields.encodeField,run,next]
    unfold lastBit
    simp only [ite_true,Bool.false_eq_true,ite_false,Nat.zero_add]
    exact ih b

theorem bits_valid (n : ℕ) (a : Bool) (hn : n ≠ 0) : lastBit n.bits a = true := by
  induction n using Nat.binaryRec' generalizing a with
  | zero => contradiction
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    change lastBit n.bits b = true
    by_cases hz : n = 0
    · subst n
      cases b <;> simp_all [lastBit,Nat.bit]
    · exact ih b hz

theorem integer_run (z : ℤ) :
    run .flowMarker (BinaryFields.encodeField (BinaryFields.writeInt z)) = (.flowMarker,0,1) := by
  by_cases hz : z = 0
  · subst z; rfl
  have hn : z.natAbs ≠ 0 := by simpa using hz
  simp only [BinaryFields.writeInt,BinaryFields.encodeField,run,next,↓reduceIte]
  rw [magnitude_run,bits_valid _ _ hn]
  rfl

theorem flows_run (zs : List ℤ) :
    run .flowMarker (BinaryFields.encode (zs.map BinaryFields.writeInt)) = (.flowMarker,0,zs.length) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    change run .flowMarker (BinaryFields.encodeField (BinaryFields.writeInt z) ++
      BinaryFields.encode (zs.map BinaryFields.writeInt)) = _
    rw [run_append,integer_run]
    simp [ih,Nat.add_comm]

theorem witness_run (w : BinaryWitnessData.Witness) :
    run .maskMarker w.encode = (.flowMarker,w.mask.length,w.flow.length) := by
  change run .maskMarker (BinaryFields.encodeField w.mask ++
    BinaryFields.encode (w.flow.map BinaryFields.writeInt)) = _
  rw [run_append,mask_run]
  simp [flows_run]

theorem emission_bound (q : Phase) (bits : List Bool) :
    (run q bits).2.1+(run q bits).2.2 ≤ bits.length := by
  induction bits generalizing q with
  | nil => simp [run]
  | cons b bs ih =>
    have h := ih (next q b).1
    have he : (if (next q b).2.1 then 1 else 0)+(if (next q b).2.2 then 1 else 0) ≤ 1 := by
      cases q <;> cases b <;> simp [next]
      split <;> decide
    simp only [run,List.length_cons]
    omega

end UnconstrainedPACDetection.VerifierWitnessGrammar
