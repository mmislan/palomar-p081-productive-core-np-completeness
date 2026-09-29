module

public import proofs.UnconstrainedPACDetection.VerifierSeparatedMachine
public import proofs.UnconstrainedPACDetection.VerifierPairRestore

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPEvaluate
open Complexity Complexity.TM
open VerifierPairRestore (word)

abbrev original := VerifierSeparatedMachine.machine
def machine : TM 33 := placeWorkTM 0 3 original

/-- The evaluator ignores the three setup tapes. They may contain a consumed
counter or other scratch data; their idle motion is explicitly tracked. -/
theorem run {t : Nat} {c d : Cfg 30 original.Q} (h : original.reachesIn t c d)
    (frame : Fin 33 → Tape) :
    ∃ frame', machine.reachesIn t (placeWorkCfg original 0 3 frame c)
      (placeWorkCfg original 0 3 frame' d) := by
  induction h generalizing frame with
  | zero => exact ⟨frame,.zero⟩
  | @step c _ _ _ hs _ ih =>
    obtain ⟨frame',hr⟩ := ih (placeWorkFrameStep (pre := 0) (n := 30) (post := 3) frame)
    have hstep := placeWorkTM_step_placeWorkCfg_internal original 0 3 frame c
    rw [hs] at hstep
    exact ⟨frame',.step hstep hr⟩

def before (src wit : List Bool) : Complexity.TM.TapePred 33 := fun inp work out =>
  inp = word src ∧
  (∀ j : Fin 30, work (placeWorkIdx 0 3 j) = VerifierRawStage.initialWork wit j) ∧ OutAcc [] out

theorem evaluate_hoare (src wit : List Bool) : machine.HoareTime (before src wit)
    (fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (VerifierSeparatedMachine.budget src wit) := by
  rintro inp work out ⟨rfl,hw,ho⟩
  have hout : out = word [] := ho.eq outAcc_nil_init
  subst out
  obtain ⟨d,t,ht,hd,hh,hout⟩ := VerifierSeparatedMachine.verification_hoare src wit
    (word src) (VerifierRawStage.initialWork wit) (word []) ⟨rfl,rfl,rfl⟩
  obtain ⟨frame',hr⟩ := run hd work
  have hstart : placeWorkCfg original 0 3 work
      (⟨original.qstart,word src,VerifierRawStage.initialWork wit,word []⟩ : Cfg 30 original.Q) =
      (⟨machine.qstart,word src,work,word []⟩ : Cfg 33 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : placeWorkInMiddle 0 30 (post := 3) j
      · simp only [placeWorkCfg,dite_eq_left hj]
        have h := hw (placeWorkCoord 0 30 j hj)
        rw [placeWorkIdx_placeWorkCoord] at h
        exact h.symm
      · simp only [placeWorkCfg,dite_eq_right hj]
    · rfl
  rw [hstart] at hr
  exact ⟨_,t,ht,hr,hh,hout⟩

end UnconstrainedPACDetection.VerifierNPEvaluate
