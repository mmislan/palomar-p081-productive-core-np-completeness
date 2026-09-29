module

public import proofs.UnconstrainedPACDetection.VerifierValidatedEntry
public import proofs.UnconstrainedPACDetection.VerifierPreparedAcceptance

@[expose] public section

namespace UnconstrainedPACDetection.VerifierValidatedRun
open Complexity Complexity.TM

def kernel : TM 30 := placeWorkTM 0 12 VerifierPreparedCertificate.machine

theorem kernel_hoare (src wit : List Bool) : kernel.HoareTime
    (VerifierValidatedEntry.after src wit)
    (fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (22000*(src.length+3*wit.length+2)^4) := by
  rintro inp work out ⟨s,w,hs,hw,hwf,hm0,hn,hm,hr,he,hpre,hpark⟩
  obtain ⟨d,t,ht,hd,hh,hpost⟩ := VerifierPreparedAcceptance.check_hoare s hwf hm0 hn w hm hr
    inp (fun j => work (placeWorkIdx 0 12 j)) out hpre
  have hrun := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierPreparedCertificate.machine 0 12 work hd (fun j _ => (hpark j).read_ne_start)
  have hstart : placeWorkCfg VerifierPreparedCertificate.machine 0 12 work
      ⟨VerifierPreparedCertificate.machine.qstart,inp,fun j => work (placeWorkIdx 0 12 j),out⟩ =
      (⟨kernel.qstart,inp,work,out⟩ : Cfg 30 kernel.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [hstart] at hrun
  have hsrc := BinarySourceData.decode_reencode hs
  obtain ⟨_,a,_,_,hout⟩ := hpost
  refine ⟨placeWorkCfg VerifierPreparedCertificate.machine 0 12 work d,t,?_,hrun,hh,?_⟩
  · simpa only [hsrc,he] using ht
  · change OutAcc [BinaryIntegerVerifier.verify src wit] d.output
    simpa only [hsrc,he] using hout

theorem entry_stable (src wit : List Bool) : ∀ inp work out,
    VerifierValidatedEntry.after src wit inp work out →
    VerifierValidatedEntry.after src wit (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hcopy := h
  obtain ⟨s,w,_,_,_,_,_,_,_,_,hpre,hpark⟩ := hcopy
  have ho : out.read ≠ .start := by rw [hpre.2.2.2.2]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hpre.1.read_ne_start
    (fun j => (hpark j).read_ne_start) ho
  simpa only [hi',hw',ho'] using h

def machine : TM 30 := seqTM VerifierKernelEntry.machine kernel

/-- Actual complete accepting branch: raw validation's physical postcondition,
charged kernel initialization, and the existing total binary integer verifier. -/
theorem verification_hoare (src wit : List Bool) (B : Nat) : machine.HoareTime
    (VerifierValidatedEntry.before src wit B)
    (fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (B+6*wit.length+24+100*(2*wit.length+1)^2+22000*(src.length+3*wit.length+2)^4) := by
  have h := seqTM_hoareTime _ _ (VerifierValidatedEntry.entry_hoare src wit B)
    (entry_stable src wit) (kernel_hoare src wit)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierValidatedRun
