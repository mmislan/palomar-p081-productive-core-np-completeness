module

public import proofs.UnconstrainedPACDetection.VerifierRawBranch

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawDecision
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierValidatedEntry (rawWork)

theorem raw_status (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierRawCardinality.after src wit inp work out) :
    Parked inp ∧ (∀ j, Parked (work j)) ∧ ∃ v, out = one .start v := by
  rcases h with ⟨hprep,ho⟩ | ⟨base,q,m,n,hprep,_,hcheck⟩
  · obtain ⟨hi,hp,_⟩ := VerifierCardinalityData.parked src wit hprep
    exact ⟨hi,hp,false,ho⟩
  · obtain ⟨hi,hp,_⟩ := VerifierCardinalityData.parked src wit hprep
    obtain ⟨_,a,b,ha,hb,_,_,hwork,hout⟩ := hcheck
    refine ⟨hi,?_,_,hout⟩
    rw [hwork]
    intro j
    fin_cases j
    · exact ⟨ha.1,ha.2.2.2⟩
    · exact hp 1
    · exact hp 2
    · exact hp 3
    · exact parked_regTape 0
    · exact hp 5
    · exact hp 6
    · exact hp 7
    · exact hp 8
    · exact hp 9
    · exact ⟨hb.1,hb.2.2.2⟩

def ready (src wit : List Bool) (B : Nat) : Complexity.TM.TapePred 30 := fun inp work out =>
  VerifierRawCardinality.after src wit inp (rawWork work) (work 29) ∧
  (∀ j : Fin 30, j.val < 18 → work j = regTape 0) ∧
  inp.cells = (wordTape src).cells ∧ (work 27).head ≤ B ∧ OutAcc [] out

theorem decision_hoare (src wit : List Bool) (B : Nat) : VerifierRawBranch.machine.HoareTime
    (ready src wit B) (fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (B+6*wit.length+26+100*(2*wit.length+1)^2+22000*(src.length+3*wit.length+2)^4) := by
  rintro inp work out ⟨hraw,hzero,hcells,hbound,hout⟩
  obtain ⟨hi,hpark,v,hv⟩ := raw_status src wit hraw
  have hp : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j.val < 18
    · rw [hzero j hj]; exact parked_regTape 0
    · by_cases hk : j.val < 29
      · let k : Fin 11 := ⟨j.val-18,by omega⟩
        have hjk : placeWorkIdx 18 1 k = j := by apply Fin.ext; dsimp [placeWorkIdx,k]; omega
        have h := hpark k
        change Parked (work (placeWorkIdx 18 1 k)) at h
        rwa [hjk] at h
      · have hj29 : j = 29 := by apply Fin.ext; have := j.isLt; omega
        subst j
        rw [hv]
        exact (VerifierFieldCardinality.one_acc v).parked
  have ho : out = wordTape [] := hout.eq (VerifierActivationProduce.ended_acc [])
  subst out
  cases v with
  | false =>
    have hfalse := VerifierRawRejection.rejected_verifier src wit (hv ▸ hraw)
    have hr := VerifierRawBranch.enter inp work false hi.read_ne_start hp hv
    refine ⟨_,2,by omega,hr,rfl,?_⟩
    rw [hfalse]
    exact VerifierFieldCardinality.one_acc false
  | true =>
    obtain ⟨d,t,ht,hr,hh,hpost⟩ := VerifierValidatedRun.verification_hoare src wit B inp work (wordTape [])
      ⟨hraw,hv,hzero,hcells,hbound,VerifierActivationProduce.ended_acc []⟩
    have he := VerifierRawBranch.enter inp work true hi.read_ne_start hp hv
    have hrun := reachesIn_trans VerifierRawBranch.machine he (VerifierRawBranch.run_embed hr)
    exact ⟨VerifierRawBranch.embed d,2+t,by omega,hrun,congrArg Sum.inr hh,hpost⟩

end UnconstrainedPACDetection.VerifierRawDecision
