module

public import proofs.UnconstrainedPACDetection.VerifierMaskRestore
public import proofs.UnconstrainedPACDetection.BinaryWitnessData

@[expose] public section

/-! A uniform mask reader with reusable input and index tapes. -/
namespace UnconstrainedPACDetection.VerifierMaskAccess
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter exhausted)

def positioned (src : List Bool) (x : ℕ) : Tape := ⟨2*x+2,(wordTape src).cells⟩
def pred (inp₀ wt : Tape) (emitted : List Bool) : Complexity.TM.TapePred 1 :=
  fun inp work out => inp = inp₀ ∧ work = (fun _ => wt) ∧ out.HasBinaryPrefix emitted

theorem raw_hoare (pre rest suffix emitted : List Bool) (b : Bool) :
    VerifierMaskReader.machine.HoareTime
      (pred (wordTape (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix))
        (counter (2+pre.length)) emitted)
      (pred (positioned (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix) pre.length)
        (exhausted (2+pre.length)) (emitted ++ [b])) (2*pre.length+4) := by
  rintro inp work out ⟨rfl,rfl,hout⟩
  let c : Cfg 1 (Fin 6) :=
    ⟨0,wordTape (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix),
      fun _ => counter (2+pre.length),out⟩
  obtain ⟨d,hd,hh,_hi,_hw,hih,hwh,hic,hwc,ho⟩ :=
    VerifierMaskReader.read_run pre rest suffix emitted b c rfl
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix hout
  refine ⟨d,_,le_rfl,hd,hh,?_,?_,ho⟩
  · apply Tape.ext
    · change d.input.head = 2*pre.length+2
      change d.input.head = 1+2*pre.length+1 at hih
      omega
    · exact hic
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    apply Tape.ext
    · change (d.work 0).head = 2+pre.length+1
      change (d.work 0).head = 1+2+pre.length at hwh
      omega
    · exact hwc

theorem positioned_suffix (pre rest suffix : List Bool) (b : Bool) :
    (positioned (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix) pre.length).HasBinarySuffix
      (b :: (BinaryFields.encodeField rest ++ suffix)) := by
  let c : Cfg 1 (Fin 6) :=
    ⟨0,wordTape (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix),
      fun _ => counter (2+pre.length),wordTape []⟩
  obtain ⟨d,_hd,_hh,hi,_hw,hih,_hwh,hic,_hwc,_ho⟩ :=
    VerifierMaskReader.read_run pre rest suffix [] b c rfl
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix
      Tape.init_nil_move_right_hasBinaryPrefix_nil
  have he : d.input = positioned (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix) pre.length := by
    apply Tape.ext
    · change d.input.head = 2*pre.length+2
      change d.input.head = 1+2*pre.length+1 at hih
      omega
    · exact hic
  rwa [he] at hi

def machine : TM 1 := seqTM VerifierMaskReader.machine VerifierMaskRestore.machine

/-- After reading, both caller tapes are exactly restored. Runtime is linear
in the selected index, not in any binary-encoded numerical value. -/
theorem access_hoare (pre rest suffix emitted : List Bool) (b : Bool) :
    machine.HoareTime
      (pred (wordTape (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix))
        (counter (2+pre.length)) emitted)
      (pred (wordTape (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix))
        (counter (2+pre.length)) (emitted ++ [b])) (5*pre.length+15) := by
  let src := BinaryFields.encodeField (pre ++ b :: rest) ++ suffix
  have hi := (positioned_suffix pre rest suffix b).read_ne_start
  have second : VerifierMaskRestore.machine.HoareTime
      (pred (positioned src pre.length) (exhausted (2+pre.length)) (emitted ++ [b]))
      (pred (wordTape src) (counter (2+pre.length)) (emitted ++ [b])) (3*pre.length+10) := by
    rintro inp work out ⟨rfl,rfl,hout⟩
    obtain ⟨d,t,ht,hd,hh,hin,hw,ho⟩ := VerifierMaskRestore.restore_hoare src
      (2+pre.length) (positioned src pre.length) out rfl hi
      (by rw [hout.read_blank]; decide) (by rw [hout.1]; omega)
      _ _ _ ⟨rfl,rfl,rfl⟩
    refine ⟨d,t,?_,hd,hh,hin,hw,?_⟩
    · change t ≤ 2*pre.length+2+(2+pre.length)+6 at ht
      omega
    · rw [ho]; exact hout
  have stable : ∀ inp work out,
      pred (positioned src pre.length) (exhausted (2+pre.length)) (emitted ++ [b]) inp work out →
      pred (positioned src pre.length) (exhausted (2+pre.length)) (emitted ++ [b])
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,hout⟩
    obtain ⟨hin,hw,ho⟩ := phaseTransition_eq_self_of_reads_ne_start hi
      (fun _ => VerifierIndexedField.exhausted_off _) (by rw [hout.read_blank]; decide)
    exact ⟨hin,hw,by rwa [ho]⟩
  have h := seqTM_hoareTime _ _ (raw_hoare pre rest suffix emitted b) stable second
  exact h.mono_bound (by omega)

theorem witness_hoare (w : BinaryWitnessData.Witness) (x : ℕ) (hx : x < w.mask.length)
    (emitted : List Bool) : machine.HoareTime
      (pred (wordTape w.encode) (counter (2+x)) emitted)
      (pred (wordTape w.encode) (counter (2+x)) (emitted ++ [w.mask.getD x false]))
      (5*x+15) := by
  have hsplit : w.mask = w.mask.take x ++ w.mask[x] :: w.mask.drop (x+1) := by
    conv_lhs => rw [← List.take_append_drop x w.mask, List.drop_eq_getElem_cons hx]
  have hlen : (w.mask.take x).length = x := by simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hx)]
  have h := access_hoare (w.mask.take x) (w.mask.drop (x+1))
    (BinaryFields.encode (w.flow.map BinaryFields.writeInt)) emitted w.mask[x]
  rw [hlen,← hsplit] at h
  simpa [BinaryWitnessData.Witness.encode,BinaryFields.encode,List.getD,hx] using h

end UnconstrainedPACDetection.VerifierMaskAccess

