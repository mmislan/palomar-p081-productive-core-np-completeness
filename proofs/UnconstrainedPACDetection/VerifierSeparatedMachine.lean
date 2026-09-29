module

public import proofs.UnconstrainedPACDetection.VerifierRawStage

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSeparatedMachine
open Complexity Complexity.TM
open VerifierVerdictAnd (one)

theorem ready_stable (src wit : List Bool) (B : Nat) : ∀ inp work out,
    VerifierRawDecision.ready src wit B inp work out →
    VerifierRawDecision.ready src wit B (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hcopy := h
  obtain ⟨hraw,hzero,_,_,hout⟩ := hcopy
  obtain ⟨hi,hpark,v,hv⟩ := VerifierRawDecision.raw_status src wit hraw
  have hp : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j.val < 18
    · rw [hzero j hj]; exact parked_regTape 0
    · by_cases hk : j.val < 29
      · let k : Fin 11 := ⟨j.val-18,by omega⟩
        have hjk : placeWorkIdx 18 1 k = j := by apply Fin.ext; dsimp [placeWorkIdx,k]; omega
        have hp' := hpark k
        change Parked (work (placeWorkIdx 18 1 k)) at hp'
        rwa [hjk] at hp'
      · have hj29 : j = 29 := by apply Fin.ext; have := j.isLt; omega
        subst j
        rw [hv]
        exact (VerifierFieldCardinality.one_acc v).parked
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (hp j).read_ne_start) hout.parked.read_ne_start
  simpa only [hi',hw',ho'] using h

def machine : TM 30 := seqTM VerifierRawStage.machine VerifierRawBranch.machine

def budget (src wit : List Bool) : Nat :=
  2*VerifierRawStage.budget src wit+6*wit.length+28+100*(2*wit.length+1)^2+
    22000*(src.length+3*wit.length+2)^4

/-- Both branches on arbitrary source/witness strings, starting from the
separated physical layout. Ordinary paired-input parsing remains separate. -/
theorem verification_hoare (src wit : List Bool) : machine.HoareTime
    (VerifierRawStage.initial src wit)
    (fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out) (budget src wit) := by
  have h := seqTM_hoareTime _ _ (VerifierRawStage.stage_hoare src wit)
    (ready_stable src wit (VerifierRawStage.budget src wit+1))
    (VerifierRawDecision.decision_hoare src wit (VerifierRawStage.budget src wit+1))
  exact h.mono_bound (by dsimp [budget]; omega)

/-- The charged bound is a fixed polynomial in the actual two wire lengths. -/
theorem budget_polynomial (src wit : List Bool) :
    budget src wit = 26*src.length+84*(wit.length+1)^2+14*wit.length+232+
      256*(2*(wit.length+1)^2+2)^3+100*(2*wit.length+1)^2+
      22000*(src.length+3*wit.length+2)^4 := by
  unfold budget VerifierRawStage.budget opBudget
  ring

end UnconstrainedPACDetection.VerifierSeparatedMachine
