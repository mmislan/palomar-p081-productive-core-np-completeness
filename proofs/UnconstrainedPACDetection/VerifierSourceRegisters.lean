module

public import proofs.UnconstrainedPACDetection.VerifierSourcePrepare
public import proofs.UnconstrainedPACDetection.VerifierWitnessRegisters

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceRegisters
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierFlowPassHoare (ended)
open VerifierVerdictAnd (one)
open VerifierWitnessRegisters (pair ended_parked)

def Meaning (bits : List Bool) (count : ℕ) (b : Bool) : Prop :=
  count ≤ bits.length ∧
    (b = true ↔ ∃ ns : List ℕ, VerifierSourceGrammar.wire ns = bits) ∧
    (b = true → ∃ ns : List ℕ, VerifierSourceGrammar.wire ns = bits ∧ ns.length = count)

def stage (bits : List Bool) (ready : Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ ∃ count b, Meaning bits count b ∧
    work = pair (if ready then wordTape (List.replicate count true) else ended (List.replicate count true))
      (wordTape []) ∧ out = one .start b

theorem scan_hoare (bits : List Bool) : VerifierSourcePrepare.machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits false) (bits.length+1) := by
  rintro inp work out ⟨hi,hwork,hout⟩
  subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hdi,count,b,hd0,hd1,hdo,hc,hacc,hcounts⟩ :=
    VerifierSourcePrepare.validation_hoare bits inp (fun _ => wordTape []) (wordTape []) ⟨hi,rfl,rfl⟩
  have h0 := work_cells_zero_eq_start_of_reachesIn 0 hd rfl
  have h1 := work_cells_zero_eq_start_of_reachesIn 1 hd rfl
  have ho := output_cells_zero_eq_start_of_reachesIn hd rfl
  refine ⟨d,t,ht,hd,hh,hdi,count,b,⟨hc,hacc,hcounts⟩,?_,?_⟩
  · funext j
    fin_cases j
    · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hd0 h0).eq (VerifierActivationProduce.ended_acc _)
    · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hd1 h1).eq outAcc_nil_init
  · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hdo ho).eq
      (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl)

def machine : TM 2 := seqTM VerifierSourcePrepare.machine (rewindWorkTM 0)

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits true) (2*bits.length+5) := by
  have stable : ∀ inp work out, stage bits false inp work out →
      stage bits false (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    have horig := h
    obtain ⟨hi,count,b,_,hwork,hout⟩ := h
    have hp : ∀ j, (work j).read ≠ .start := by
      rw [hwork]
      intro j
      fin_cases j
      · exact (ended_parked _).read_ne_start
      · exact (VerifierReactionLoop.word_parked _).read_ne_start
    have ho : out.read ≠ .start := by rw [hout]; change Γ.blank ≠ Γ.start; decide
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp ho
    simpa only [hi',hw',ho'] using horig
  have second : (rewindWorkTM (0 : Fin 2)).HoareTime (stage bits false) (stage bits true) (bits.length+3) := by
    rintro inp work out ⟨hi,count,b,hmeaning,hwork,hout⟩
    subst work; subst out
    let base := pair (ended (List.replicate count true)) (wordTape [])
    have hp : ∀ j, Parked (base j) := by
      intro j
      fin_cases j
      · exact ended_parked _
      · exact VerifierReactionLoop.word_parked _
    have ho : Parked (one .start b) :=
      (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl).parked
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierWitnessRegisters.rewind_one 0
      (List.replicate count true) base inp (one .start b) rfl hp hi.read_ne_start ho _ _ _ ⟨rfl,rfl,rfl⟩
    refine ⟨d,t,?_,hd,hh,by rwa [hdi],count,b,hmeaning,?_,hdo⟩
    · simp only [List.length_replicate] at ht
      have := hmeaning.1
      omega
    · rw [hdw]
      funext j
      fin_cases j <;> rfl
  have h := seqTM_hoareTime _ _ (scan_hoare bits) stable second
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierSourceRegisters
