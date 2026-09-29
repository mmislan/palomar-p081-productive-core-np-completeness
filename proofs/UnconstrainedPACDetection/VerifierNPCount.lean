module

public import proofs.UnconstrainedPACDetection.VerifierPairRestore
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.UnaryLength.Defs

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPCount
open Complexity Complexity.TM

abbrev scanner : TM 0 := unaryLengthTM
def noWork : Fin 0 → Tape := fun j => Fin.elim0 j

/-- Strong accumulator contract for the existing unary scanner, retaining
all blank tail cells needed by register arithmetic. -/
theorem scan (xs : List Bool) : ∀ (inp out : Tape) (acc : List Bool),
    inp.HasBinarySuffix xs → OutAcc acc out →
    ∃ d, scanner.reachesIn (xs.length+1) ⟨scanner.qstart,inp,noWork,out⟩ d ∧
      scanner.halted d ∧ d.input.HasBinarySuffix [] ∧
      OutAcc (acc ++ List.replicate xs.length true) d.output := by
  induction xs with
  | nil =>
    intro inp out acc hi ho
    let d : Cfg 0 scanner.Q := ⟨.done,inp,noWork,out⟩
    have hs : scanner.step ⟨scanner.qstart,inp,noWork,out⟩ = some d := by
      unfold scanner unaryLengthTM
      simp only [TM.step,show UnaryLengthPhase.copying ≠ .done from by decide,
        ite_false,hi.read_nil]
      congr 1
      apply Cfg.ext
      · rfl
      · simp [d,idleDir,Tape.move]
      · funext j; exact Fin.elim0 j
      · exact ho.parked.writeAndMove_readBack_idle
    exact ⟨d,.step hs .zero,rfl,hi,by simpa using ho⟩
  | cons bit xs ih =>
    intro inp out acc hi ho
    let next : Cfg 0 scanner.Q :=
      ⟨scanner.qstart,inp.move .right,noWork,out.writeAndMove .one .right⟩
    have hs : scanner.step ⟨scanner.qstart,inp,noWork,out⟩ = some next := by
      unfold scanner unaryLengthTM
      cases bit
      · simp [TM.step,hi.read_cons,Γ.ofBool,next,noWork]
        congr 1
        apply Cfg.ext
        · rfl
        · rfl
        · funext j; exact Fin.elim0 j
        · rfl
      · simp [TM.step,hi.read_cons,Γ.ofBool,next,noWork]
        congr 1
        apply Cfg.ext
        · rfl
        · rfl
        · funext j; exact Fin.elim0 j
        · rfl
    obtain ⟨d,hd,hh,hinput,hout⟩ := ih (inp.move .right) (out.writeAndMove .one .right)
      (acc ++ [true]) hi.move_right_cons (outAcc_append_bit ho true)
    refine ⟨d,.step hs hd,hh,hinput,?_⟩
    simpa only [List.length_cons,List.replicate_succ,List.append_assoc,List.singleton_append] using hout

def machine : TM 0 := seqTM (emitBitsTM [true]) scanner

theorem count_hoare (xs : List Bool) : machine.HoareTime
    (fun inp _ out => inp.HasBinarySuffix xs ∧ OutAcc [] out)
    (fun inp _ out => inp.HasBinarySuffix [] ∧ OutAcc (List.replicate (xs.length+1) true) out)
    (xs.length+3) := by
  have hfirst : (emitBitsTM (n := 0) [true]).HoareTime
      (fun inp _ out => inp.HasBinarySuffix xs ∧ OutAcc [] out)
      (fun inp _ out => inp.HasBinarySuffix xs ∧ OutAcc [true] out) 1 := by
    intro inp work out ⟨hi,ho⟩
    have hw : ∀ j, Parked (work j) := fun j => Fin.elim0 j
    have h := emitBitsTM_hoareTime [true] inp work [] ⟨hi.1,hi.2.2.2⟩ hw
    obtain ⟨d,t,ht,hd,hh,hdi,_,hout⟩ := h inp work out ⟨rfl,rfl,ho⟩
    exact ⟨d,t,ht,hd,hh,hdi ▸ hi,by simpa using hout⟩
  have hstable : ∀ inp (_work : Fin 0 → Tape) out, inp.HasBinarySuffix xs ∧ OutAcc [true] out →
      (transitionInput inp).HasBinarySuffix xs ∧ OutAcc [true] (transitionTape out) := by
    intro inp _ out ⟨hi,ho⟩
    rw [transitionInput_eq_self hi.read_ne_start,transitionTape_eq_self ho.parked.read_ne_start]
    exact ⟨hi,ho⟩
  have hsecond : scanner.HoareTime
      (fun inp _ out => inp.HasBinarySuffix xs ∧ OutAcc [true] out)
      (fun inp _ out => inp.HasBinarySuffix [] ∧ OutAcc (List.replicate (xs.length+1) true) out)
      (xs.length+1) := by
    intro inp work out ⟨hi,ho⟩
    have hw : work = noWork := funext fun j => Fin.elim0 j
    subst work
    obtain ⟨d,hd,hh,hinput,hout⟩ := scan xs inp out [true] hi ho
    exact ⟨d,xs.length+1,le_rfl,hd,hh,hinput,by simpa [List.replicate_succ] using hout⟩
  have h := seqTM_hoareTime _ _ hfirst hstable hsecond
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierNPCount
