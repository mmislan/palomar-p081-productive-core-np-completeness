module

public import proofs.UnconstrainedPACDetection.VerifierNPPrepare
public import proofs.UnconstrainedPACDetection.VerifierNPEvaluate
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.GuessBounded

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPGuess
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def machine : NTM 33 := NTM.guessBoundedNTM 27 31
def bound (N : Nat) : Nat := NTM.guessBoundedTime (VerifierNPBound.cap N) 0

theorem prepared_witness (N : Nat) : VerifierNPPrepare.preparedWork N 27 = word [] := by
  simp [VerifierNPPrepare.preparedWork,VerifierNPBound.finalWork,VerifierNPPrepare.countedWork]

theorem prepared_counter (N : Nat) :
    VerifierNPPrepare.preparedWork N 31 = regTape (VerifierNPBound.cap N) := by
  simp [VerifierNPPrepare.preparedWork,VerifierNPBound.finalWork]

theorem prepared_prefix (N : Nat) (j : Fin 30) :
    VerifierNPPrepare.preparedWork N (placeWorkIdx 0 3 j) = word [] := by
  have hj : (placeWorkIdx 0 3 j).val < 30 := by simp [placeWorkIdx]
  have h30 : placeWorkIdx 0 3 j ≠ 30 := by intro h; rw [h] at hj; contradiction
  rw [VerifierNPPrepare.preparedWork,VerifierNPBound.evaluator_frame N _ _ hj]
  simp only [VerifierNPPrepare.countedWork,Function.update_of_ne h30]

def framed (src : List Bool) : NTM.TapePred 33 := fun inp work out =>
  inp = word src ∧ out = word [] ∧
  (∀ j, j ≠ 27 → j ≠ 31 → work j = VerifierNPPrepare.preparedWork src.length j) ∧
  ∃ wit : List Bool, wit.length ≤ VerifierNPBound.cap src.length ∧ work 27 = word wit

theorem framed_hoare (src : List Bool) : machine.HoareTime
    (EmitPred (word src) (VerifierNPPrepare.preparedWork src.length) [])
    (framed src) (bound src.length) := by
  have h := NTM.guessBoundedNTM_hoareTime_init_move_right_frame
    (27 : Fin 33) 31 (by decide) (VerifierNPBound.cap src.length) (word src) (word [])
    (VerifierNPPrepare.preparedWork src.length) (word_parked src).read_ne_start
    (word_parked []).read_ne_start (fun j _ _ => (VerifierNPPrepare.prepared_parked src.length j).read_ne_start)
  apply h.weaken_pre
  rintro inp work out ⟨hi,hw,ho⟩
  subst inp; subst work
  have hout : out = word [] := ho.eq outAcc_nil_init
  subst out
  refine ⟨rfl,rfl,fun _ _ _ => rfl,?_,?_,?_⟩
  · rw [prepared_witness]
    exact ⟨rfl,(Tape.init_move_right_hasBinaryString []).2⟩
  · rw [prepared_witness]; rfl
  · rw [prepared_counter]; exact (reg_regT _).hasUnaryCounter

theorem framed_before (src wit : List Bool) (inp : Tape) (work : Fin 33 → Tape) (out : Tape)
    (hi : inp = word src) (ho : out = word [])
    (hf : ∀ j, j ≠ 27 → j ≠ 31 → work j = VerifierNPPrepare.preparedWork src.length j)
    (hw : work 27 = word wit) : VerifierNPEvaluate.before src wit inp work out := by
  refine ⟨hi,?_,?_⟩
  · intro j
    by_cases hj : j = 27
    · subst j; exact hw
    · have h27 : placeWorkIdx 0 3 j ≠ 27 := by
        intro h
        apply hj
        apply Fin.ext
        have hh := congrArg (fun i : Fin 33 => i.val) h
        simpa [placeWorkIdx] using hh
      have h31 : placeWorkIdx 0 3 j ≠ 31 := by
        intro h
        have hh : j.val = 31 := by simpa [placeWorkIdx] using congrArg (fun i : Fin 33 => i.val) h
        have := j.isLt
        omega
      rw [hf _ h27 h31,prepared_prefix]
      simp only [VerifierRawStage.initialWork,ite_eq_right hj]
      rfl
  · rw [ho]; exact outAcc_nil_init

def after (src : List Bool) : NTM.TapePred 33 := fun inp work out =>
  ∃ wit, wit.length ≤ VerifierNPBound.cap src.length ∧ VerifierNPEvaluate.before src wit inp work out

theorem guess_hoare (src : List Bool) : machine.HoareTime
    (EmitPred (word src) (VerifierNPPrepare.preparedWork src.length) [])
    (after src) (bound src.length) := by
  apply (framed_hoare src).strengthen_post
  rintro inp work out ⟨hi,ho,hf,wit,hlen,hw⟩
  exact ⟨wit,hlen,framed_before src wit inp work out hi ho hf hw⟩

def initial (src : List Bool) : Cfg 33 machine.Q :=
  ⟨machine.qstart,word src,VerifierNPPrepare.preparedWork src.length,word []⟩

/-- Every particular short certificate is generated on some branch, while
retaining the exact evaluator input frame, not just its witness contents. -/
theorem generates (src wit : List Bool) (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (bound src.length) → Bool,
      let d := machine.trace (bound src.length) choices (initial src)
      machine.halted d ∧ VerifierNPEvaluate.before src wit d.input d.work d.output := by
  obtain ⟨choices,hh,hw⟩ := NTM.guessBoundedNTM_choose_generates_witness_initTape_move_right
    (27 : Fin 33) 31 (by decide) (VerifierNPBound.cap src.length) [] wit (initial src) hlen rfl
    (by rw [show (initial src).work 27 = word [] from prepared_witness src.length]
        exact ⟨rfl,(Tape.init_move_right_hasBinaryString []).2⟩)
    (by rw [show (initial src).work 27 = word [] from prepared_witness src.length]; rfl)
    (by rw [show (initial src).work 31 = regTape (VerifierNPBound.cap src.length) from prepared_counter src.length]
        exact (reg_regT _).hasUnaryCounter)
  have hframe := (framed_hoare src) (word src) (VerifierNPPrepare.preparedWork src.length) (word [])
    ⟨rfl,rfl,outAcc_nil_init⟩ choices
  obtain ⟨hi,ho,hf,_⟩ := hframe.2
  change (machine.trace (bound src.length) choices (initial src)).work 27 = word wit at hw
  exact ⟨choices,hh,framed_before src wit _ _ _ hi ho hf hw⟩

end UnconstrainedPACDetection.VerifierNPGuess
