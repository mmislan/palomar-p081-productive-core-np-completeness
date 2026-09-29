module

public import proofs.UnconstrainedPACDetection.VerifierKernelEntry

@[expose] public section

namespace UnconstrainedPACDetection.VerifierValidatedEntry
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

def rawWork (work : Fin 30 → Tape) : Fin 11 → Tape := fun j => work (placeWorkIdx 18 1 j)

theorem source_cursor_bound (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hm : 0 < s.entities) (hn : 0 < s.reactions) (inp : Tape)
    (hi : inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)))
    (hc : inp.cells = (wordTape s.encode).cells) : inp.head ≤ s.encode.length+1 := by
  have hlen : 0 < s.values.length := by
    have hw : s.values.length = 2*(s.entities*s.reactions) := hs
    nlinarith [Nat.mul_pos hm hn]
  have hne : BinaryFields.encode (s.values.map Nat.bits) ≠ [] := by
    cases hv : s.values with
    | nil => simp [hv] at hlen
    | cons v vs =>
      have hfield := BinaryFields.encodeField_length v.bits
      intro he
      have hzero := congrArg List.length he
      change (BinaryFields.encodeField v.bits ++ BinaryFields.encode (vs.map Nat.bits)).length = 0 at hzero
      simp only [List.length_append] at hzero
      omega
  cases he : BinaryFields.encode (s.values.map Nat.bits) with
  | nil => exact (hne he).elim
  | cons b bs =>
    rw [he] at hi
    have hr := hi.read_cons
    by_contra hb
    have hblank := (Tape.init_move_right_hasBinaryString s.encode).2.2
      (inp.head-1) (by omega)
    change (wordTape s.encode).cells (inp.head-1+1) = Γ.blank at hblank
    have hhead : inp.head-1+1 = inp.head := by omega
    rw [hhead] at hblank
    change inp.cells inp.head = Γ.ofBool b at hr
    rw [hc,hblank] at hr
    cases b <;> cases hr

def before (src wit : List Bool) (B : Nat) : Complexity.TM.TapePred 30 := fun inp work out =>
  VerifierRawCardinality.after src wit inp (rawWork work) (work 29) ∧
  work 29 = one .start true ∧
  (∀ j : Fin 30, j.val < 18 → work j = regTape 0) ∧
  inp.cells = (wordTape src).cells ∧ (work 27).head ≤ B ∧ OutAcc [] out

def after (src wit : List Bool) : Complexity.TM.TapePred 30 := fun inp work out =>
  ∃ s : BinarySourceData.DenseSource, ∃ w : BinaryWitnessData.Witness,
    BinarySourceData.decode src = some s ∧ BinaryWitnessData.decode wit = some w ∧
    s.WellFormed ∧ 0 < s.entities ∧ 0 < s.reactions ∧
    w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = wit ∧
    VerifierPreparedCertificate.pre s w inp (fun j => work (placeWorkIdx 0 12 j)) out ∧
    ∀ j, Parked (work j)

theorem entry_hoare (src wit : List Bool) (B : Nat) :
    VerifierKernelEntry.machine.HoareTime (before src wit B) (after src wit)
      (B+6*wit.length+23+100*(2*wit.length+1)^2) := by
  rintro inp work out ⟨hraw,ho29,hzero,hcells,hbound,hout⟩
  rw [ho29] at hraw
  obtain ⟨s,w,hs,hw,he,hm,hn,hem,hrn,hwf,hcursor,h5,h8,h9,hpark⟩ :=
    VerifierRawFrame.accepted_frame src wit hraw
  have hsrc := BinarySourceData.decode_reencode hs
  have hi : Parked inp := ⟨hcursor.1,hcursor.2.2.2⟩
  have hp : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j.val < 18
    · rw [hzero j hj]; exact parked_regTape 0
    · by_cases hk : j.val < 29
      · let k : Fin 11 := ⟨j.val-18,by omega⟩
        have hjk : placeWorkIdx 18 1 k = j := by apply Fin.ext; dsimp [placeWorkIdx,k]; omega
        have h := hpark k
        change Parked (work (placeWorkIdx 18 1 k)) at h
        rwa [hjk] at h
      · have hj29 : j = 29 := by apply Fin.ext; have := j.isLt; omega
        subst j
        rw [ho29]
        exact (VerifierFieldCardinality.one_acc true).parked
  have hwlen : w.mask.length ≤ w.encode.length := by
    have hf := BinaryFields.encodeField_length w.mask
    change w.mask.length ≤ (BinaryFields.encodeField w.mask ++
      BinaryFields.encode (w.flow.map BinaryFields.writeInt)).length
    simp only [List.length_append]; omega
  have hrlen := VerifierEncodingBounds.reaction_count w
  have hcounts : s.entities+s.reactions ≤ 2*wit.length := by rw [hem,hrn,← he]; omega
  have h9' : (work 27).cells = (wordTape w.encode).cells := by
    rw [← he] at h9
    change (work 27).cells = (wordTape w.encode).cells at h9
    exact h9
  have hd := VerifierKernelEntry.entry_hoare s w inp work B hi hp
    h9' hbound h5 h8 hzero
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := hd inp work out ⟨rfl,rfl,hout⟩
  have hprefix := VerifierKernelEntry.final_prefix work s w hzero
  have hpFinal : ∀ j, Parked (VerifierKernelEntry.finalWork work s w j) := by
    intro j
    by_cases hj : j.val < 18
    · let k : Fin 18 := ⟨j.val,hj⟩
      have hjk : placeWorkIdx 0 12 k = j := by apply Fin.ext; simp [placeWorkIdx,k]
      rw [← hjk,hprefix]
      exact VerifierPreparedLayout.join_parked _ _
        (VerifierPreparedCertificate.frame_parked s w 2)
        (VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked [])) k
    · have hne (v : Fin 30) (hv : v.val < 18) : j ≠ v := by intro he'; subst j; omega
      by_cases hj27 : j = 27
      · subst j
        change Parked (wordTape w.encode)
        exact VerifierReactionLoop.word_parked _
      · simpa [VerifierKernelEntry.finalWork,VerifierKernelRegisters.finalWork,
          VerifierWitnessPlacement.placed,VerifierWitnessPlacement.restored,
          Function.update_of_ne (hne 1 (by decide)),Function.update_of_ne (hne 4 (by decide)),
          Function.update_of_ne (hne 9 (by decide)),Function.update_of_ne (hne 10 (by decide)),
          Function.update_of_ne (hne 12 (by decide)),Function.update_of_ne (hne 13 (by decide)),
          Function.update_of_ne (hne 14 (by decide)),Function.update_of_ne (hne 16 (by decide)),hj27] using hp j
  refine ⟨d,t,?_,hd,hh,s,w,hs,hw,hwf,hm,hn,hem.symm,hrn.symm,he,?_,?_⟩
  · have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hcounts 1) 2
    rw [he] at ht
    omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · rwa [hdi]
    · rw [hdi,hcells,hsrc]
    · rw [hdi]
      exact source_cursor_bound s hwf hm hn inp hcursor (by rwa [hsrc])
    · funext j
      rw [hdw]
      exact hprefix j
    · exact hdo.eq (VerifierActivationProduce.ended_acc [])
  · rw [hdw]; exact hpFinal

end UnconstrainedPACDetection.VerifierValidatedEntry
