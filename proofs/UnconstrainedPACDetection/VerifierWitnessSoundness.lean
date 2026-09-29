module

public import proofs.UnconstrainedPACDetection.VerifierWitnessPrepare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessSoundness
open VerifierWitnessGrammar (Phase next run accept lastBit)

theorem magnitude_canonical (bits : List Bool) (a : Bool) (h : lastBit bits a = true) :
    ∃ n : ℕ, n.bits = bits := by
  induction bits generalizing a with
  | nil => exact ⟨0,rfl⟩
  | cons b bs ih =>
    obtain ⟨n,hn⟩ := ih b h
    refine ⟨Nat.bit b n,?_⟩
    rw [Nat.bits_append_bit n b ?_,hn]
    intro hz
    subst n
    have he : bs = [] := hn.symm
    simpa [he,lastBit] using h

theorem signed_canonical (sign : Bool) (bits : List Bool) (h : lastBit bits (!sign) = true) :
    ∃ z : ℤ, BinaryFields.writeInt z = sign :: bits := by
  obtain ⟨n,hn⟩ := magnitude_canonical bits (!sign) h
  cases sign
  · exact ⟨(n : ℤ),by simp [BinaryFields.writeInt,hn]⟩
  · have hpos : 0 < n := by
      by_contra hnon
      have hz : n = 0 := by omega
      subst n
      have he : bits = [] := hn.symm
      simp [he,lastBit] at h
    refine ⟨-(n : ℤ),?_⟩
    simp [BinaryFields.writeInt,hpos,hn]

def flows (zs : List ℤ) : List Bool := BinaryFields.encode (zs.map BinaryFields.writeInt)

/-- Canonical continuations of each finite parser state. -/
def residual (q : Phase) (bits : List Bool) : Prop :=
  match q with
  | .maskMarker => ∃ mask zs, bits = BinaryFields.encodeField mask ++ flows zs
  | .maskPayload => ∃ b mask zs, bits = b :: (BinaryFields.encodeField mask ++ flows zs)
  | .flowMarker => ∃ zs, bits = flows zs
  | .signPayload => ∃ sign mag zs, lastBit mag (!sign) = true ∧
      bits = sign :: (BinaryFields.encodeField mag ++ flows zs)
  | .magnitudeMarker valid => ∃ mag zs, lastBit mag valid = true ∧
      bits = BinaryFields.encodeField mag ++ flows zs
  | .magnitudePayload => ∃ b mag zs, lastBit mag b = true ∧
      bits = b :: (BinaryFields.encodeField mag ++ flows zs)
  | .bad | .done => False

theorem residual_step (q : Phase) (b : Bool) (bits : List Bool)
    (h : residual (next q b).1 bits) : residual q (b :: bits) := by
  cases q with
  | maskMarker =>
    cases b
    · obtain ⟨zs,hb⟩ := h
      exact ⟨[],zs,by simpa [BinaryFields.encodeField] using congrArg (List.cons false) hb⟩
    · obtain ⟨bit,mask,zs,hb⟩ := h
      exact ⟨bit::mask,zs,by simp [BinaryFields.encodeField,hb]⟩
  | maskPayload =>
    obtain ⟨mask,zs,hb⟩ := h
    exact ⟨b,mask,zs,by rw [hb]⟩
  | flowMarker =>
    cases b
    · exact h.elim
    · obtain ⟨sign,mag,zs,hvalid,hb⟩ := h
      obtain ⟨z,hz⟩ := signed_canonical sign mag hvalid
      refine ⟨z::zs,?_⟩
      change true :: bits = BinaryFields.encodeField (BinaryFields.writeInt z) ++ flows zs
      rw [hz]
      exact congrArg (List.cons true) hb
  | signPayload =>
    obtain ⟨mag,zs,hvalid,hb⟩ := h
    exact ⟨b,mag,zs,hvalid,by rw [hb]⟩
  | magnitudeMarker valid =>
    cases b
    · cases valid
      · exact h.elim
      · obtain ⟨zs,hb⟩ := h
        exact ⟨[],zs,rfl,by simpa [BinaryFields.encodeField] using congrArg (List.cons false) hb⟩
    · obtain ⟨bit,mag,zs,hvalid,hb⟩ := h
      exact ⟨bit::mag,zs,hvalid,by simp [BinaryFields.encodeField,hb]⟩
  | magnitudePayload =>
    obtain ⟨mag,zs,hvalid,hb⟩ := h
    exact ⟨b,mag,zs,hvalid,by rw [hb]⟩
  | bad => exact h.elim
  | done => exact h.elim

theorem residual_of_accept (bits : List Bool) (q : Phase)
    (h : accept (run q bits).1 = true) : residual q bits := by
  induction bits generalizing q with
  | nil =>
    cases q <;> simp [run,accept] at h
    change ∃ zs, [] = flows zs
    exact ⟨[],rfl⟩
  | cons b bs ih =>
    apply residual_step q b bs
    exact ih (next q b).1 h

theorem accepted_iff (bits : List Bool) :
    accept (run .maskMarker bits).1 = true ↔ ∃ w : BinaryWitnessData.Witness, w.encode = bits := by
  constructor
  · intro h
    obtain ⟨mask,zs,hbits⟩ := residual_of_accept bits .maskMarker h
    exact ⟨⟨mask,zs⟩,hbits.symm⟩
  · rintro ⟨w,rfl⟩
    simp [VerifierWitnessGrammar.witness_run,accept]

theorem accepted_counts (bits : List Bool) (h : accept (run .maskMarker bits).1 = true) :
    ∃ w : BinaryWitnessData.Witness, w.encode = bits ∧
      (run .maskMarker bits).2.1 = w.mask.length ∧ (run .maskMarker bits).2.2 = w.flow.length := by
  obtain ⟨w,rfl⟩ := (accepted_iff bits).1 h
  exact ⟨w,rfl,congrArg (fun r => r.2.1) (VerifierWitnessGrammar.witness_run w),
    congrArg (fun r => r.2.2) (VerifierWitnessGrammar.witness_run w)⟩

theorem validation_hoare (bits : List Bool) : VerifierWitnessPrepare.machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧
      work = (fun _ => VerifierBufferedProduct.wordTape []) ∧ out = VerifierBufferedProduct.wordTape [])
    (fun inp work out => inp.HasBinarySuffix [] ∧ ∃ b m n,
      (work 0).HasBinaryPrefix (List.replicate m true) ∧
      (work 1).HasBinaryPrefix (List.replicate n true) ∧ out.HasBinaryPrefix [b] ∧
      m+n ≤ bits.length ∧
      (b = true ↔ ∃ w : BinaryWitnessData.Witness, w.encode = bits) ∧
      (b = true → ∃ w : BinaryWitnessData.Witness,
        w.encode = bits ∧ m = w.mask.length ∧ n = w.flow.length)) (bits.length+1) := by
  intro inp work out hp
  obtain ⟨d,t,ht,hd,hh,hdi,hd0,hd1,hdo⟩ := VerifierWitnessPrepare.raw_hoare bits inp work out hp
  exact ⟨d,t,ht,hd,hh,hdi,accept (run .maskMarker bits).1,
    (run .maskMarker bits).2.1,(run .maskMarker bits).2.2,hd0,hd1,hdo,
    VerifierWitnessGrammar.emission_bound _ _,accepted_iff bits,accepted_counts bits⟩

end UnconstrainedPACDetection.VerifierWitnessSoundness
