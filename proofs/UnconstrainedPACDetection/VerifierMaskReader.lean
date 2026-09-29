module

public import proofs.UnconstrainedPACDetection.VerifierSourceStride

@[expose] public section

/-! Uniform access to a doubled-bit mask using the existing offset-two index.
This component preserves input/index cells. Restoration and physical placement
are separate obligations. -/
namespace UnconstrainedPACDetection.VerifierMaskReader
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)

def action (q : Fin 6) (w : Γ) : Fin 6 × Dir3 × Dir3 :=
  if q = 0 then (1,.stay,.right)
  else if q = 1 then (2,.stay,.right)
  else if q = 2 then (if w = .one then 3 else 4,.right,.stay)
  else if q = 3 then (2,.right,.right)
  else (5,.stay,.stay)

def machine : TM 1 where
  Q := Fin 6
  qstart := 0
  qhalt := 5
  δ := fun q i w o =>
    let a := action q (w 0)
    (a.1,fun j => readBackWrite (w j),if q = 4 then readBackWrite i else readBackWrite o,
      markerDir i a.2.1,fun j => markerDir (w j) a.2.2,
      if q = 4 then .right else idleDir o)
  δ_right_of_start := by
    intro q i w o
    refine ⟨fun h => by simp [markerDir,h],fun j h => by simp [markerDir,h],?_⟩
    split
    · intro _; rfl
    · exact idleDir_right_of_start

def moved (c : Cfg 1 (Fin 6)) (q : Fin 6) (di dw : Dir3) : Cfg 1 (Fin 6) :=
  ⟨q,c.input.move di,fun j => (c.work j).move dw,c.output⟩

theorem step_move (c : Cfg 1 (Fin 6)) (q : Fin 6) (di dw : Dir3)
    (hn : c.state ≠ 5) (he : c.state ≠ 4) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read ≠ .start) (ho : c.output.read ≠ .start)
    (ha : action c.state (c.work 0).read = (q,di,dw)) :
    machine.step c = some (moved c q di dw) := by
  have hw' : ∀ j, (c.work j).read ≠ .start := by intro j; fin_cases j; exact hw
  simp only [TM.step,machine,hn,↓reduceIte,ha,he]
  simp only [markerDir,ite_eq_right hi,ite_eq_right (hw' _)]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact writeAndMove_readBack _ (hw' j) dw
  · exact transitionTape_eq_self ho

theorem prefix_run (pre rest suffix : List Bool) (c : Cfg 1 (Fin 6))
    (hq : c.state = 2)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField (pre ++ rest) ++ suffix))
    (hw : (c.work 0).HasBinarySuffix (List.replicate pre.length true))
    (ho : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn (2*pre.length) c d ∧ d.state = (2 : Fin 6) ∧
      d.input.HasBinarySuffix (BinaryFields.encodeField rest ++ suffix) ∧
      (d.work 0).HasBinarySuffix [] ∧
      d.input.head = c.input.head+2*pre.length ∧
      (d.work 0).head = (c.work 0).head+pre.length ∧
      d.input.cells = c.input.cells ∧ (d.work 0).cells = (c.work 0).cells ∧ d.output = c.output := by
  induction pre generalizing c with
  | nil => exact ⟨c,.zero,hq,hi,hw,by simp,by simp,rfl,rfl,rfl⟩
  | cons b pre ih =>
    have hin : c.input.HasBinarySuffix
        (true :: b :: (BinaryFields.encodeField (pre ++ rest) ++ suffix)) := hi
    have hwork : (c.work 0).HasBinarySuffix (true :: List.replicate pre.length true) := by
      simpa only [List.length_cons,List.replicate_succ] using hw
    let c1 := moved c 3 .right .stay
    have hs1 := step_move c 3 .right .stay (by rw [hq]; decide) (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start ho (by simp [action,hq,hwork.read_cons,Γ.ofBool])
    have hi1 : c1.input.HasBinarySuffix
        (b :: (BinaryFields.encodeField (pre ++ rest) ++ suffix)) := hin.move_right_cons
    let c2 := moved c1 2 .right .right
    have hs2 := step_move c1 2 .right .right
      (by change (3 : Fin 6) ≠ 5; decide) (by change (3 : Fin 6) ≠ 4; decide)
      hi1.read_ne_start hw.read_ne_start ho (by simp [c1,moved,action])
    obtain ⟨d,hd,hdq,hdi,hdw,hdih,hdwh,hdic,hdwc,hdo⟩ :=
      ih c2 rfl hi1.move_right_cons hwork.move_right_cons ho
    refine ⟨d,?_,hdq,hdi,hdw,?_,?_,hdic,hdwc,hdo⟩
    · convert TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd) using 1
    · simp only [c2,c1,moved,Tape.move] at hdih
      simp only [List.length_cons]; omega
    · simp only [c2,c1,moved,Tape.move] at hdwh
      simp only [List.length_cons]; omega

theorem emit_run (b : Bool) (rest emitted : List Bool) (c : Cfg 1 (Fin 6))
    (hq : c.state = 4) (hi : c.input.HasBinarySuffix (b :: rest))
    (hw : (c.work 0).read ≠ .start) (ho : c.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn 1 c d ∧ machine.halted d ∧ d.input = c.input ∧
      d.work = c.work ∧ d.output.HasBinaryPrefix (emitted ++ [b]) := by
  let d : Cfg 1 (Fin 6) :=
    ⟨5,c.input,c.work,c.output.writeAndMove (Γ.ofBool b) .right⟩
  have hw' : ∀ j, (c.work j).read ≠ .start := by intro j; fin_cases j; exact hw
  have hs : machine.step c = some d := by
    simp only [TM.step,machine,hq,show (4 : Fin 6) ≠ 5 by decide,↓reduceIte]
    simp only [action,show (4 : Fin 6) ≠ 0 by decide,show (4 : Fin 6) ≠ 1 by decide,
      show (4 : Fin 6) ≠ 2 by decide,show (4 : Fin 6) ≠ 3 by decide,↓reduceIte]
    simp only [markerDir,ite_eq_right hi.read_ne_start,ite_eq_right (hw' _)]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; exact writeAndMove_readBack _ (hw' j) .stay
    · change c.output.writeAndMove (readBackWrite c.input.read).toΓ .right = _
      cases b <;> simp [hi.read_cons,Γ.ofBool,readBackWrite,d]
  exact ⟨d,.step hs .zero,rfl,rfl,rfl,Tape.hasBinaryPrefix_write_bit b ho⟩

/-- The offset-two reader emits the selected bit in exactly 2*x+4 steps.
The masks before and after that bit are arbitrary, and all input/index cells
are preserved. The final heads are explicit for the restoration consumer. -/
theorem read_run (pre rest suffix emitted : List Bool) (b : Bool) (c : Cfg 1 (Fin 6))
    (hq : c.state = 0)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField (pre ++ b :: rest) ++ suffix))
    (hw : (c.work 0).HasBinarySuffix (List.replicate (2+pre.length) true))
    (ho : c.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (2*pre.length+4) c d ∧ machine.halted d ∧
      d.input.HasBinarySuffix (b :: (BinaryFields.encodeField rest ++ suffix)) ∧
      (d.work 0).HasBinarySuffix [] ∧
      d.input.head = c.input.head+2*pre.length+1 ∧
      (d.work 0).head = (c.work 0).head+2+pre.length ∧
      d.input.cells = c.input.cells ∧ (d.work 0).cells = (c.work 0).cells ∧
      d.output.HasBinaryPrefix (emitted ++ [b]) := by
  have hoff : c.output.read ≠ .start := by rw [ho.read_blank]; decide
  have hw0 : (c.work 0).HasBinarySuffix
      (true :: true :: List.replicate pre.length true) := by
    simpa [Nat.add_comm,List.replicate_succ] using hw
  let c1 := moved c 1 .stay .right
  have hs1 := step_move c 1 .stay .right (by rw [hq]; decide) (by rw [hq]; decide)
    hi.read_ne_start hw.read_ne_start hoff (by simp [action,hq])
  have hw1 : (c1.work 0).HasBinarySuffix (true :: List.replicate pre.length true) :=
    hw0.move_right_cons
  let c2 := moved c1 2 .stay .right
  have hs2 := step_move c1 2 .stay .right
    (by change (1 : Fin 6) ≠ 5; decide) (by change (1 : Fin 6) ≠ 4; decide)
    hi.read_ne_start hw1.read_ne_start hoff (by simp [action,c1,moved])
  obtain ⟨d,hd,hdq,hdi,hdw,hdih,hdwh,hdic,hdwc,hdo⟩ :=
    prefix_run pre (b :: rest) suffix c2 rfl hi hw1.move_right_cons hoff
  have hdi' : d.input.HasBinarySuffix (true :: b :: (BinaryFields.encodeField rest ++ suffix)) := hdi
  let e := moved d 4 .right .stay
  have hs3 := step_move d 4 .right .stay (by rw [hdq]; decide) (by rw [hdq]; decide)
    hdi.read_ne_start hdw.read_ne_start (by simpa [hdo,c2,c1,moved] using hoff)
    (by simp [action,hdq,hdw.read_nil])
  obtain ⟨f,hf,hfh,hfi,hfw,hfo⟩ := emit_run b (BinaryFields.encodeField rest ++ suffix)
    emitted e rfl hdi'.move_right_cons hdw.read_ne_start
      (by simpa [e,moved,hdo,c2,c1] using ho)
  refine ⟨f,?_,hfh,?_,?_,?_,?_,?_,?_,hfo⟩
  · have h := machine.reachesIn_trans (TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd))
      (TM.reachesIn.step hs3 hf)
    convert h using 1
  · simpa [hfi,e,moved] using hdi'.move_right_cons
  · simpa [hfw,e,moved,Tape.move] using hdw
  · rw [hfi]
    simp only [e,moved,Tape.move,c2,c1] at hdih ⊢
    omega
  · rw [hfw]
    simp only [e,moved,Tape.move,c2,c1] at hdwh ⊢
    omega
  · simpa only [hfi,e,moved,Tape.move,c2,c1] using hdic
  · simpa only [hfw,e,moved,Tape.move,c2,c1] using hdwc

end UnconstrainedPACDetection.VerifierMaskReader

