module

public import proofs.UnconstrainedPACDetection.VerifierEntityOuterSemantics

@[expose] public section

/-! A linear sequential scan of one literal reaction side against the mask.
Positive canonical natural fields begin with one; zero has an empty payload. -/
namespace UnconstrainedPACDetection.VerifierActivationScan
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)

def action (q : Fin 5) (i w o : Γ) : Fin 5 × Dir3 × Dir3 × Γw × Dir3 :=
  if q = 0 then
    if w = .one then (1,.stay,.right,readBackWrite o,idleDir o)
    else (4,.stay,.stay,if w = .zero then readBackWrite o else .zero,.right)
  else if q = 1 then
    (2,.stay,.right,readBackWrite (Γ.ofBool (decide (o = .one) ||
      (decide (w = .one) && decide (i = .one)))),idleDir o)
  else if q = 2 then
    if i = .zero then (0,.right,.stay,readBackWrite o,idleDir o)
    else if i = .one then (3,.right,.stay,readBackWrite o,idleDir o)
    else (4,.stay,.stay,.zero,.right)
  else if q = 3 then (2,.right,.stay,readBackWrite o,idleDir o)
  else (4,.stay,.stay,readBackWrite o,idleDir o)

def machine : TM 1 where
  Q := Fin 5
  qstart := 0
  qhalt := 4
  δ := fun q i w o =>
    let a := action q i (w 0) o
    (a.1,fun j => readBackWrite (w j),a.2.2.2.1,markerDir i a.2.1,
      fun j => markerDir (w j) a.2.2.1,a.2.2.2.2)
  δ_right_of_start := by
    intro q i w o
    refine ⟨fun h => by simp [markerDir,h],fun j h => by simp [markerDir,h],?_⟩
    intro ho
    subst o
    simp only [action]
    split_ifs <;> rfl

def moved (c : Cfg 1 (Fin 5)) (q : Fin 5) (di dw : Dir3) : Cfg 1 (Fin 5) :=
  ⟨q,c.input.move di,fun j => (c.work j).move dw,c.output⟩

theorem step_keep (c : Cfg 1 (Fin 5)) (q : Fin 5) (di dw : Dir3)
    (hn : c.state ≠ 4) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read ≠ .start) (ho : c.output.read ≠ .start)
    (ha : action c.state c.input.read (c.work 0).read c.output.read =
      (q,di,dw,readBackWrite c.output.read,idleDir c.output.read)) :
    machine.step c = some (moved c q di dw) := by
  have hw' : ∀ j, (c.work j).read ≠ .start := by intro j; fin_cases j; exact hw
  simp only [TM.step,machine,hn,↓reduceIte,ha]
  simp only [markerDir,ite_eq_right hi,ite_eq_right (hw' _)]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact writeAndMove_readBack _ (hw' j) dw
  · exact transitionTape_eq_self ho

theorem field_run (field suffix : List Bool) (c : Cfg 1 (Fin 5))
    (hq : c.state = 2)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField field ++ suffix))
    (hw : (c.work 0).read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn (2*field.length+1) c d ∧ d.state = (0 : Fin 5) ∧
      d.input.HasBinarySuffix suffix ∧ d.input.head = c.input.head+2*field.length+1 ∧
      d.input.cells = c.input.cells ∧ d.work = c.work ∧ d.output = c.output := by
  induction field generalizing c with
  | nil =>
    have hi' : c.input.HasBinarySuffix (false :: suffix) := hi
    have hs := step_keep c 0 .right .stay (by rw [hq]; decide)
      hi.read_ne_start hw ho (by simp [action,hq,hi'.read_cons,Γ.ofBool])
    exact ⟨moved c 0 .right .stay,.step hs .zero,rfl,hi'.move_right_cons,rfl,rfl,rfl,rfl⟩
  | cons b field ih =>
    have hi' : c.input.HasBinarySuffix (true :: b :: (BinaryFields.encodeField field ++ suffix)) := hi
    let c1 := moved c 3 .right .stay
    have hs1 := step_keep c 3 .right .stay (by rw [hq]; decide)
      hi.read_ne_start hw ho (by simp [action,hq,hi'.read_cons,Γ.ofBool])
    have hi1 : c1.input.HasBinarySuffix (b :: (BinaryFields.encodeField field ++ suffix)) := hi'.move_right_cons
    let c2 := moved c1 2 .right .stay
    have hs2 := step_keep c1 2 .right .stay (by change (3 : Fin 5) ≠ 4; decide)
      hi1.read_ne_start hw ho (by simp [action,c1,moved])
    obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdw,hdo⟩ := ih c2 rfl hi1.move_right_cons hw ho
    refine ⟨d,?_,hdq,hdi,?_,hdc,hdw,hdo⟩
    · convert TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd) using 1
    · simp only [c2,c1,moved,Tape.move] at hdh
      simp only [List.length_cons]; omega

def flag (marker : Γ) (b : Bool) : Tape :=
  {VerifierVerdictAnd.one marker b with head := 1}

theorem flag_write (m : Γ) (a b : Bool) :
    (flag m a).writeAndMove (Γ.ofBool b) .stay = flag m b := by
  apply Tape.ext
  · rfl
  · funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [flag,Tape.writeAndMove,Tape.write,Tape.move,VerifierVerdictAnd.one,h0,h1]

theorem flag_read (m : Γ) (a : Bool) : (flag m a).read = Γ.ofBool a := rfl

theorem select_step (c : Cfg 1 (Fin 5)) (m : Γ) (a b : Bool)
    (hq : c.state = 1) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read = Γ.ofBool b) (ho : c.output = flag m a) :
    machine.step c = some ⟨(2 : Fin 5),c.input,fun j => (c.work j).move .right,
      flag m (a || (b && decide (c.input.read = .one)))⟩ := by
  have hw' : ∀ j, (c.work j).read ≠ .start := by
    intro j; fin_cases j; change (c.work 0).read ≠ .start; rw [hw]; cases b <;> decide
  simp only [TM.step,machine,↓reduceIte,action,hq]
  simp only [show (1 : Fin 5) ≠ 0 by decide,show (1 : Fin 5) ≠ 4 by decide,
    ↓reduceIte,hw,ho,flag_read]
  have ha : decide (Γ.ofBool a = .one) = a := by cases a <;> rfl
  have hb : decide (Γ.ofBool b = .one) = b := by cases b <;> rfl
  simp only [ha,hb,markerDir,ite_eq_right hi,ite_eq_right (hw' _)]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact writeAndMove_readBack _ (hw' j) .right
  · have hz := flag_write m a (a || (b && decide (c.input.read = .one)))
    cases a <;> cases b <;> cases h : decide (c.input.read = .one) <;>
      simpa [idleDir,Γ.ofBool,readBackWrite,h] using hz

theorem field_positive (t : Tape) (field suffix : List Bool)
    (h : t.HasBinarySuffix (BinaryFields.encodeField field ++ suffix)) :
    decide (t.read = .one) = !field.isEmpty := by
  cases field with
  | nil => have h' : t.HasBinarySuffix (false :: suffix) := h
           rw [h'.read_cons]; rfl
  | cons b bs =>
    have h' : t.HasBinarySuffix (true :: b :: (BinaryFields.encodeField bs ++ suffix)) := h
    rw [h'.read_cons]; rfl

theorem finish_step (c : Cfg 1 (Fin 5)) (m : Γ) (a : Bool)
    (hq : c.state = 0) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read = .zero) (ho : c.output = flag m a) :
    machine.step c = some ⟨(4 : Fin 5),c.input,c.work,VerifierVerdictAnd.one m a⟩ := by
  have hw' : ∀ j, (c.work j).read ≠ .start := by
    intro j; fin_cases j; change (c.work 0).read ≠ .start; rw [hw]; decide
  simp only [TM.step,machine,action,hq,hw,ho]
  simp only [show (0 : Fin 5) ≠ 4 by decide,↓reduceIte,flag_read,markerDir,ite_eq_right hi,ite_eq_right (hw' _)]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact writeAndMove_readBack _ (hw' j) .stay
  · have hz := VerifierVerdictAnd.write_one m a a
    cases a <;> simpa [flag,Γ.ofBool,readBackWrite] using hz

end UnconstrainedPACDetection.VerifierActivationScan
