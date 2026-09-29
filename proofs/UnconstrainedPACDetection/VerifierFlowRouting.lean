module

public import proofs.UnconstrainedPACDetection.VerifierFlowPrepared
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowRouting
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

abbrev reader := VerifierFlowPrepared.machine
def buffered : TM 2 := retargetInput reader
def placed : TM 4 := placeWorkTM 0 2 buffered
def permutation : Equiv.Perm (Fin 4) := (Equiv.swap 0 3).trans (Equiv.swap 1 0)
def machine : TM 4 := VerifierTapePermutation.machine placed permutation

theorem retarget_run {t : ℕ} {c d : Cfg 1 reader.Q}
    (h : reader.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap reader realInput c) (retargetWrap reader realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have step := retargetInput_step_commute reader hs realInput hi
    rw [hidle] at step
    exact .step step (ih hi')

def embed (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 1 reader.Q) : Cfg 4 machine.Q :=
  VerifierTapePermutation.wrap placed permutation
    (placeWorkCfg buffered 0 2 (fun j => frame (permutation j)) (retargetWrap reader inp c))

theorem embed_flags (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 1 reader.Q) :
    (embed frame inp c).work 3 = c.work 0 := by
  simp [embed,VerifierTapePermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
    retargetWrap,permutation,Equiv.swap_apply_def]

theorem embed_witness (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 1 reader.Q) :
    (embed frame inp c).work 0 = c.input := by
  simp [embed,VerifierTapePermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
    retargetWrap,permutation,Equiv.swap_apply_def]

theorem embed_other (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 1 reader.Q)
    (j : Fin 4) (h0 : j ≠ 0) (h3 : j ≠ 3) : (embed frame inp c).work j = frame j := by
  fin_cases j <;> first | exact (h0 rfl).elim | exact (h3 rfl).elim | rfl

theorem check_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (frame : Fin 4 → Tape) (inp₀ : Tape)
    (h0 : frame 0 = wordTape w.encode) (h3 : frame 3 = wordTape (VerifierActivationSource.flags s w))
    (hf : ∀ j, (frame j).read ≠ .start) (hi : inp₀.read ≠ .start) :
    machine.HoareTime (VerifierTapeCleanup.frame frame inp₀ (one .start true))
      (fun inp work out => inp = inp₀ ∧
        work 0 = VerifierFlowPassHoare.ended w.encode ∧
        work 3 = VerifierFlowPassHoare.advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions) ∧
        (∀ j, j ≠ 0 → j ≠ 3 → work j = frame j) ∧
        out = one .start (VerifierFlowBothSource.result s w)) (6*w.encode.length+12) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  let c : Cfg 1 reader.Q := ⟨reader.qstart,wordTape w.encode,
    fun _ => wordTape (VerifierActivationSource.flags s w),one .start true⟩
  obtain ⟨d,t,ht,hd,hh,hdin,hdw,hdo⟩ := VerifierFlowPrepared.check_hoare s w hw
    c.input c.work c.output ⟨rfl,rfl,rfl⟩
  have hret := retarget_run hd ((Tape.StartInvariant.init_ofBool w.encode).move .right) inp₀ hi
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal buffered 0 2
    (fun j => frame (permutation j)) hret (by intro j _; exact hf _)
  have hperm := VerifierTapePermutation.run placed permutation hp
  have he : embed frame inp₀ c = (⟨machine.qstart,inp₀,frame,one .start true⟩ : Cfg 4 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      change (embed frame inp₀ c).work j = frame j
      by_cases hj0 : j = 0
      · subst j; rw [embed_witness,h0]
      by_cases hj3 : j = 3
      · subst j; rw [embed_flags,h3]
      exact embed_other frame inp₀ c j hj0 hj3
    · rfl
  refine ⟨embed frame inp₀ d,t,ht,?_,hh,rfl,?_,?_,?_,hdo⟩
  · change machine.reachesIn t (embed frame inp₀ c) (embed frame inp₀ d) at hperm
    simpa only [he] using hperm
  · rw [embed_witness]; exact hdin
  · rw [embed_flags,hdw]
  · intro j hj0 hj3; exact embed_other frame inp₀ d j hj0 hj3

end UnconstrainedPACDetection.VerifierFlowRouting
