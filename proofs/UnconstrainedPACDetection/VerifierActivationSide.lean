module

public import proofs.UnconstrainedPACDetection.VerifierActivationScan

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationSide
open Complexity Complexity.TM VerifierActivationScan

def hit (es : List (List Bool × Bool)) (a : Bool) : Bool :=
  es.foldl (fun acc e => acc || (e.2 && !e.1.isEmpty)) a

theorem run (es : List (List Bool × Bool)) (srcTail witTail : List Bool)
    (c : Cfg 1 (Fin 5)) (m : Γ) (a : Bool) (hq : c.state = 0)
    (hi : c.input.HasBinarySuffix (BinaryFields.encode (es.map Prod.fst) ++ srcTail))
    (hw : (c.work 0).HasBinarySuffix (BinaryFields.encodeField (es.map Prod.snd) ++ witTail))
    (ho : c.output = flag m a) :
    ∃ d, machine.reachesIn ((BinaryFields.encode (es.map Prod.fst)).length + 2*es.length+1) c d ∧
      d.state = (4 : Fin 5) ∧ d.input.HasBinarySuffix srcTail ∧
      d.input.head = c.input.head + (BinaryFields.encode (es.map Prod.fst)).length ∧
      d.input.cells = c.input.cells ∧
      (d.work 0).HasBinarySuffix (false :: witTail) ∧
      (d.work 0).head = (c.work 0).head + 2*es.length ∧
      (∀ j, (d.work j).cells = (c.work j).cells) ∧
      d.output = VerifierVerdictAnd.one m (hit es a) := by
  induction es generalizing c a with
  | nil =>
    have hw' : (c.work 0).HasBinarySuffix (false :: witTail) := hw
    have hs := finish_step c m a hq hi.read_ne_start (by simpa [Γ.ofBool] using hw'.read_cons) ho
    refine ⟨⟨(4 : Fin 5),c.input,c.work,VerifierVerdictAnd.one m a⟩,.step hs .zero,rfl,hi,?_,rfl,hw',?_,?_,rfl⟩
    · rfl
    · rfl
    · intro j; rfl
  | cons e es ih =>
    let rest := BinaryFields.encode (es.map Prod.fst) ++ srcTail
    have hi' : c.input.HasBinarySuffix (BinaryFields.encodeField e.1 ++ rest) := by
      simpa [rest,BinaryFields.encode,List.flatMap_cons,List.append_assoc] using hi
    have hw' : (c.work 0).HasBinarySuffix
        (true :: e.2 :: (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) := hw
    have hor : c.output.read ≠ .start := by rw [ho,flag_read]; cases a <;> decide
    let c1 := moved c 1 .stay .right
    have hs1 := step_keep c 1 .stay .right (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start hor (by simp [action,hq,hw'.read_cons,Γ.ofBool])
    have hw1 : (c1.work 0).HasBinarySuffix
        (e.2 :: (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) := hw'.move_right_cons
    let b := a || (e.2 && !e.1.isEmpty)
    let c2 : Cfg 1 (Fin 5) := ⟨2,c1.input,fun j => (c1.work j).move .right,flag m b⟩
    have hs2 : machine.step c1 = some c2 := by
      have h := select_step c1 m a e.2 rfl hi.read_ne_start hw1.read_cons ho
      have hp := field_positive c1.input e.1 rest hi'
      unfold c2 b
      rw [hp] at h
      exact h
    have hw2 : (c2.work 0).HasBinarySuffix (BinaryFields.encodeField (es.map Prod.snd) ++ witTail) := hw1.move_right_cons
    have ho2 : c2.output.read ≠ .start := by change Γ.ofBool b ≠ .start; cases b <;> decide
    obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdw,hdo⟩ := field_run e.1 rest c2 rfl hi' hw2.read_ne_start ho2
    obtain ⟨f,hf,hfq,hfi,hfh,hfc,hfw,hfwh,hfwc,hfo⟩ :=
      ih d b hdq hdi (by rw [hdw]; exact hw2) hdo
    refine ⟨f,?_,hfq,hfi,?_,?_,hfw,?_,?_,hfo⟩
    · have h := machine.reachesIn_trans (TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd)) hf
      have ht : (BinaryFields.encode ((e :: es).map Prod.fst)).length +
          2*(e :: es).length+1 =
          2*e.1.length+1+1+1+
            ((BinaryFields.encode (es.map Prod.fst)).length+2*es.length+1) := by
        simp only [List.map_cons,BinaryFields.encode,List.flatMap_cons,List.length_append,
          BinaryFields.encodeField_length,List.length_cons]
        omega
      rw [ht]
      exact h
    · simp only [List.map_cons,BinaryFields.encode,List.flatMap_cons,List.length_append,
          BinaryFields.encodeField_length]
      rw [hfh,hdh]
      simp only [c2,c1,moved,Tape.move,BinaryFields.encode]
      omega
    · exact hfc.trans hdc
    · rw [hfwh,hdw]
      simp only [c2,c1,moved,Tape.move,List.length_cons]; omega
    · intro j; rw [hfwc,hdw]; rfl

end UnconstrainedPACDetection.VerifierActivationSide
