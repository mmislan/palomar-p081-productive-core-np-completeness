module

public import proofs.UnconstrainedPACDetection.VerifierActivationDock

@[expose] public section

namespace UnconstrainedPACDetection.VerifierMaskNonempty
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)
open VerifierActivationScan (flag)
open VerifierVerdictAnd (one)

inductive Phase where
  | enter
  | marker (seen : Bool)
  | payload (seen : Bool)
  | done
  deriving DecidableEq, Fintype

def action (q : Phase) (i o : Γ) : Phase × Dir3 × Γw × Dir3 :=
  match q with
  | .enter => (.marker false,.stay,readBackWrite o,.left)
  | .marker seen => if i = .zero then
      (.done,.right,readBackWrite (Γ.ofBool (decide (o = .one) && seen)),.right)
    else (.payload seen,.right,readBackWrite o,.stay)
  | .payload seen => (.marker (seen || decide (i = .one)),.right,readBackWrite o,.stay)
  | .done => (.done,.stay,readBackWrite o,.stay)

def machine : TM 0 where
  Q := Phase
  qstart := .enter
  qhalt := .done
  δ := fun q i _ o =>
    let a := action q i o
    (a.1,fun j => Fin.elim0 j,a.2.2.1,markerDir i a.2.1,fun j => Fin.elim0 j,markerDir o a.2.2.2)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir,h],fun j => Fin.elim0 j,fun h => by simp [markerDir,h]⟩

def moved (c : Cfg 0 Phase) (q : Phase) : Cfg 0 Phase := ⟨q,c.input.move .right,c.work,c.output⟩

theorem step_keep (c : Cfg 0 Phase) (q : Phase) (hn : c.state ≠ .done)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start)
    (ha : action c.state c.input.read c.output.read = (q,.right,readBackWrite c.output.read,.stay)) :
    machine.step c = some (moved c q) := by
  simp only [TM.step,machine,hn,↓reduceIte,ha,markerDir,ite_eq_right hi,ite_eq_right ho]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact Fin.elim0 j
  · exact writeAndMove_readBack _ ho .stay

theorem finish_step (c : Cfg 0 Phase) (m : Γ) (a seen : Bool)
    (hq : c.state = .marker seen) (hi : c.input.read = .zero) (ho : c.output = flag m a) :
    machine.step c = some ⟨Phase.done,c.input.move .right,c.work,one m (a && seen)⟩ := by
  simp only [TM.step,machine,action,hq,hi,ho]
  simp only [reduceCtorEq,↓reduceIte,VerifierActivationScan.flag_read,markerDir,ite_self]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact Fin.elim0 j
  · have hz := VerifierVerdictAnd.write_one m a (a && seen)
    cases a <;> cases seen <;> simpa [flag,Γ.ofBool,readBackWrite] using hz

theorem scan_run (mask tail : List Bool) (c : Cfg 0 Phase) (m : Γ) (a seen : Bool)
    (hq : c.state = .marker seen)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField mask ++ tail)) (ho : c.output = flag m a) :
    ∃ d, machine.reachesIn (2*mask.length+1) c d ∧ d.state = Phase.done ∧
      d.input.HasBinarySuffix tail ∧ d.input.head = c.input.head+2*mask.length+1 ∧
      d.input.cells = c.input.cells ∧ d.output = one m (a && (seen || mask.any id)) := by
  induction mask generalizing c seen with
  | nil =>
    have hi' : c.input.HasBinarySuffix (false :: tail) := hi
    have hs := finish_step c m a seen hq (by simpa [Γ.ofBool] using hi'.read_cons) ho
    exact ⟨_,.step hs .zero,rfl,hi'.move_right_cons,rfl,rfl,by simp⟩
  | cons b mask ih =>
    have hi' : c.input.HasBinarySuffix (true :: b :: (BinaryFields.encodeField mask ++ tail)) := hi
    have hor : c.output.read ≠ .start := by rw [ho,VerifierActivationScan.flag_read]; cases a <;> decide
    let c1 := moved c (.payload seen)
    have hs1 := step_keep c (.payload seen) (by rw [hq]; exact Phase.noConfusion) hi.read_ne_start hor
      (by simp [action,hq,hi'.read_cons,Γ.ofBool])
    have hi1 : c1.input.HasBinarySuffix (b :: (BinaryFields.encodeField mask ++ tail)) := hi'.move_right_cons
    let c2 := moved c1 (.marker (seen || b))
    have hs2 := step_keep c1 (.marker (seen || b)) (by exact Phase.noConfusion) hi1.read_ne_start hor
      (by
        change action (.payload seen) c1.input.read c1.output.read = _
        rw [hi1.read_cons]
        cases b <;> simp [action,Γ.ofBool])
    obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdo⟩ := ih c2 (seen || b) rfl hi1.move_right_cons ho
    refine ⟨d,?_,hdq,hdi,?_,hdc,?_⟩
    · convert TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd) using 1
    · simp only [c2,c1,moved,Tape.move] at hdh
      simp only [List.length_cons]; omega
    · simpa [List.any_cons,Bool.or_assoc] using hdo

theorem run (mask tail : List Bool) (c : Cfg 0 Phase) (m : Γ) (a : Bool)
    (hq : c.state = .enter)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField mask ++ tail)) (ho : c.output = one m a) :
    ∃ d, machine.reachesIn (2*mask.length+2) c d ∧ d.state = Phase.done ∧
      d.input.HasBinarySuffix tail ∧ d.input.head = c.input.head+2*mask.length+1 ∧
      d.input.cells = c.input.cells ∧ d.output = one m (a && mask.any id) := by
  let mid : Cfg 0 Phase := ⟨.marker false,c.input,c.work,flag m a⟩
  have hs : machine.step c = some mid := by
    have hir := hi.read_ne_start
    simp only [TM.step,machine,action,hq,ho]
    simp only [reduceCtorEq,↓reduceIte,markerDir,ite_eq_right hir]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; exact Fin.elim0 j
    · have hor : (one m a).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
      exact writeAndMove_readBack _ hor .left
  obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdo⟩ := scan_run mask tail mid m a false rfl hi rfl
  exact ⟨d,by convert TM.reachesIn.step hs hd using 1,hdq,hdi,hdh,hdc,by simpa using hdo⟩

end UnconstrainedPACDetection.VerifierMaskNonempty
