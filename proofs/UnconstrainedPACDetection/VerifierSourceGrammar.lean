module

public import proofs.UnconstrainedPACDetection.VerifierWitnessSoundness

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceGrammar
open VerifierWitnessGrammar (lastBit)

inductive Phase where
  | boundary | marker (valid : Bool) | payload | bad | done
  deriving DecidableEq, Fintype

def next (q : Phase) (b : Bool) : Phase × Bool × Bool :=
  match q with
  | .boundary => if b then (.payload,false,false) else (.boundary,true,false)
  | .marker valid => if b then (.payload,false,false)
      else (if valid then .boundary else .bad,valid,false)
  | .payload => (.marker b,false,false)
  | .bad => (.bad,false,false)
  | .done => (.done,false,false)

def accept (q : Phase) : Bool := decide (q = .boundary)

def run (q : Phase) : List Bool → Phase × ℕ × ℕ
  | [] => (q,0,0)
  | b :: bs =>
      let a := next q b
      let r := run a.1 bs
      (r.1,(if a.2.1 then 1 else 0)+r.2.1,(if a.2.2 then 1 else 0)+r.2.2)

def wire (ns : List ℕ) := BinaryFields.encode (ns.map Nat.bits)

theorem run_append (q : Phase) (xs ys : List Bool) :
    run q (xs++ys) = let a := run q xs; let b := run a.1 ys;
      (b.1,a.2.1+b.2.1,a.2.2+b.2.2) := by
  induction xs generalizing q with
  | nil => simp [run]
  | cons x xs ih => simp [run,ih,Nat.add_assoc]

theorem magnitude_run (bits : List Bool) (a : Bool) :
    run (.marker a) (BinaryFields.encodeField bits) =
      (if lastBit bits a then .boundary else .bad,if lastBit bits a then 1 else 0,0) := by
  induction bits generalizing a with
  | nil => cases a <;> rfl
  | cons b bs ih =>
    simp only [BinaryFields.encodeField,run,next]
    unfold lastBit
    simp only [ite_true,Bool.false_eq_true,ite_false,Nat.zero_add]
    exact ih b

theorem boundary_run (bits : List Bool) :
    run .boundary (BinaryFields.encodeField bits) = run (.marker true) (BinaryFields.encodeField bits) := by
  cases bits <;> rfl

theorem field_run (n : ℕ) : run .boundary (BinaryFields.encodeField n.bits) = (.boundary,1,0) := by
  rw [boundary_run,magnitude_run]
  by_cases hn : n = 0
  · subst n; rfl
  · rw [VerifierWitnessGrammar.bits_valid n true hn]; rfl

theorem wire_run (ns : List ℕ) : run .boundary (wire ns) = (.boundary,ns.length,0) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    change run .boundary (BinaryFields.encodeField n.bits ++ wire ns) = _
    rw [run_append,field_run]
    simp [ih,Nat.add_comm]

def residual (q : Phase) (bits : List Bool) : Prop :=
  match q with
  | .boundary => ∃ ns, bits = wire ns
  | .marker valid => ∃ mag ns, lastBit mag valid = true ∧ bits = BinaryFields.encodeField mag ++ wire ns
  | .payload => ∃ b mag ns, lastBit mag b = true ∧ bits = b :: (BinaryFields.encodeField mag ++ wire ns)
  | .bad | .done => False

theorem residual_step (q : Phase) (b : Bool) (bits : List Bool)
    (h : residual (next q b).1 bits) : residual q (b::bits) := by
  cases q with
  | boundary =>
    cases b
    · obtain ⟨ns,hb⟩ := h
      exact ⟨0::ns,congrArg (List.cons false) hb⟩
    · obtain ⟨bit,mag,ns,hvalid,hb⟩ := h
      obtain ⟨n,hn⟩ := VerifierWitnessSoundness.magnitude_canonical (bit::mag) true hvalid
      refine ⟨n::ns,?_⟩
      change true :: bits = BinaryFields.encodeField n.bits ++ wire ns
      rw [hn]
      exact congrArg (List.cons true) hb
  | marker valid =>
    cases b
    · cases valid
      · exact h.elim
      · obtain ⟨ns,hb⟩ := h
        exact ⟨[],ns,rfl,congrArg (List.cons false) hb⟩
    · obtain ⟨bit,mag,ns,hvalid,hb⟩ := h
      exact ⟨bit::mag,ns,hvalid,by simp [BinaryFields.encodeField,hb]⟩
  | payload =>
    obtain ⟨mag,ns,hvalid,hb⟩ := h
    exact ⟨b,mag,ns,hvalid,congrArg (List.cons b) hb⟩
  | bad => exact h.elim
  | done => exact h.elim

theorem accepted_iff (bits : List Bool) :
    accept (run .boundary bits).1 = true ↔ ∃ ns : List ℕ, wire ns = bits := by
  have sound : ∀ q, accept (run q bits).1 = true → residual q bits := by
    induction bits with
    | nil =>
      intro q h
      cases q <;> simp [run,accept] at h
      change ∃ ns, [] = wire ns
      exact ⟨[],rfl⟩
    | cons b bs ih =>
      intro q h
      exact residual_step q b bs (ih (next q b).1 h)
  constructor
  · intro h
    obtain ⟨ns,hn⟩ := sound .boundary h
    exact ⟨ns,hn.symm⟩
  · rintro ⟨ns,rfl⟩
    simp [wire_run,accept]

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

theorem spare_zero (q : Phase) (bits : List Bool) : (run q bits).2.2 = 0 := by
  induction bits generalizing q with
  | nil => rfl
  | cons b bs ih =>
    have h : (next q b).2.2 = false := by cases q <;> cases b <;> simp [next]
    simp [run,h,ih]

end UnconstrainedPACDetection.VerifierSourceGrammar
