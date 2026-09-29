module

public import proofs.UnconstrainedPACDetection.VerifierWitnessSoundness

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessRegisters
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierFlowPassHoare (ended)
open VerifierVerdictAnd (one)

def pair (a b : Tape) : Fin 2 → Tape := ![a,b]

theorem ended_parked (bits : List Bool) : Parked (ended bits) :=
  ⟨by change 1 ≤ bits.length+1; omega,((Tape.StartInvariant.init_ofBool bits).move .right).2⟩

theorem rewind_one (idx : Fin 2) (bits : List Bool) (base : Fin 2 → Tape)
    (inp out : Tape) (hb : base idx = ended bits) (hp : ∀ j, Parked (base j))
    (hi : inp.read ≠ .start) (ho : Parked out) :
    (rewindWorkTM idx).HoareTime (VerifierTapeCleanup.frame base inp out)
      (VerifierTapeCleanup.frame (Function.update base idx (wordTape bits)) inp out) (bits.length+3) := by
  let P : Complexity.TM.TapePred 2 := fun i ws o => i = inp ∧ o = out ∧
    (ws idx).cells = (wordTape bits).cells ∧ ∀ j, j ≠ idx → ws j = base j
  have hr := rewindWorkTM_hoareTime_frame idx (bits.length+1) (P := P) (by
    rintro i ws o i' ws' o' ⟨hin,hout,hc,hf⟩ hc' _ hf' hi' hoc hoh
    exact ⟨hi'.trans hin,(Tape.ext hoh hoc).trans hout,hc'.trans hc,
      fun j hj => (hf' j hj).trans (hf j hj)⟩)
  rintro i ws o ⟨hin,hws,hout⟩
  subst i; subst ws; subst o
  have hm := (Tape.StartInvariant.init_ofBool bits).move .right
  obtain ⟨d,t,ht,hd,hh,hdh,hdi,hdo,hdc,hdf⟩ := hr inp base out
    ⟨by rw [hb]; exact hm.1,by intro j hj; rw [hb]; exact hm.2 j hj,
      by rw [hb]; exact le_rfl,hi,ho.read_ne_start,ho.1,
      fun j _ => ⟨(hp j).read_ne_start,(hp j).1⟩,rfl,rfl,by rw [hb]; rfl,fun _ _ => rfl⟩
  refine ⟨d,t,ht,hd,hh,hdi,?_,hdo⟩
  funext j
  by_cases hj : j = idx
  · subst j
    rw [Function.update_self]
    exact Tape.ext hdh hdc
  · rw [Function.update_of_ne hj]
    exact hdf j hj

@[reducible] def reset : TM 2 := seqTM (rewindWorkTM 0) (rewindWorkTM 1)

theorem reset_hoare (m n : ℕ) (inp out : Tape) (hi : inp.read ≠ .start) (ho : Parked out) :
    reset.HoareTime
      (VerifierTapeCleanup.frame (pair (ended (List.replicate m true)) (ended (List.replicate n true))) inp out)
      (VerifierTapeCleanup.frame (pair (wordTape (List.replicate m true)) (wordTape (List.replicate n true))) inp out)
      (m+n+7) := by
  let start := pair (ended (List.replicate m true)) (ended (List.replicate n true))
  let mid := Function.update start 0 (wordTape (List.replicate m true))
  have hs : ∀ j, Parked (start j) := by
    intro j; fin_cases j <;> exact ended_parked _
  have hm : ∀ j, Parked (mid j) := by
    intro j
    fin_cases j
    · exact VerifierReactionLoop.word_parked _
    · exact ended_parked _
  have stable : ∀ i ws o, VerifierTapeCleanup.frame mid inp out i ws o →
      VerifierTapeCleanup.frame mid inp out (transitionInput i)
        (fun j => transitionTape (ws j)) (transitionTape o) := by
    rintro i ws o ⟨hin,hws,hout⟩
    subst i; subst ws; subst o
    exact phaseTransition_eq_self_of_reads_ne_start hi (fun j => (hm j).read_ne_start) ho.read_ne_start
  have h := seqTM_hoareTime _ _
    (rewind_one 0 _ start inp out rfl hs hi ho) stable (rewind_one 1 _ mid inp out rfl hm hi ho)
  have he : Function.update mid 1 (wordTape (List.replicate n true)) =
      pair (wordTape (List.replicate m true)) (wordTape (List.replicate n true)) := by
    funext j; fin_cases j <;> rfl
  simpa only [he,List.length_replicate,start,show m+3+1+(n+3) = m+n+7 by omega] using h

def Meaning (bits : List Bool) (m n : ℕ) (b : Bool) : Prop :=
  m+n ≤ bits.length ∧
    (b = true ↔ ∃ w : BinaryWitnessData.Witness, w.encode = bits) ∧
    (b = true → ∃ w : BinaryWitnessData.Witness, w.encode = bits ∧ m = w.mask.length ∧ n = w.flow.length)

def stage (bits : List Bool) (ready : Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ ∃ m n b, Meaning bits m n b ∧
    work = pair (if ready then wordTape (List.replicate m true) else ended (List.replicate m true))
      (if ready then wordTape (List.replicate n true) else ended (List.replicate n true)) ∧ out = one .start b

theorem scan_hoare (bits : List Bool) : VerifierWitnessPrepare.machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits false) (bits.length+1) := by
  rintro inp work out ⟨hi,hwork,hout⟩
  subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hdi,b,m,n,hd0,hd1,hdo,hm,hacc,hcounts⟩ :=
    VerifierWitnessSoundness.validation_hoare bits inp (fun _ => wordTape []) (wordTape []) ⟨hi,rfl,rfl⟩
  have h0 := work_cells_zero_eq_start_of_reachesIn 0 hd rfl
  have h1 := work_cells_zero_eq_start_of_reachesIn 1 hd rfl
  have ho := output_cells_zero_eq_start_of_reachesIn hd rfl
  refine ⟨d,t,ht,hd,hh,hdi,m,n,b,⟨hm,hacc,hcounts⟩,?_,?_⟩
  · funext j
    fin_cases j
    · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hd0 h0).eq (VerifierActivationProduce.ended_acc _)
    · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hd1 h1).eq (VerifierActivationProduce.ended_acc _)
  · exact (VerifierEntityLoopBody.acc_of_prefix _ _ hdo ho).eq
      (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl)

@[reducible] def machine : TM 2 := seqTM VerifierWitnessPrepare.machine reset

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits true) (2*bits.length+9) := by
  have stable : ∀ inp work out, stage bits false inp work out →
      stage bits false (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    have horig := h
    obtain ⟨hi,m,n,b,_,hwork,hout⟩ := h
    have hp : ∀ j, (work j).read ≠ .start := by
      rw [hwork]; intro j; fin_cases j <;> exact (ended_parked _).read_ne_start
    have ho : out.read ≠ .start := by rw [hout]; change Γ.blank ≠ Γ.start; decide
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp ho
    simpa only [hi',hw',ho'] using horig
  have second : reset.HoareTime (stage bits false) (stage bits true) (bits.length+7) := by
    rintro inp work out ⟨hi,m,n,b,hmeaning,hwork,hout⟩
    subst work; subst out
    have ho : Parked (one .start b) :=
      (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl).parked
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := reset_hoare m n inp (one .start b) hi.read_ne_start ho
      _ _ _ ⟨rfl,rfl,rfl⟩
    exact ⟨d,t,by have := hmeaning.1; omega,hd,hh,by rwa [hdi],m,n,b,hmeaning,hdw,hdo⟩
  have h := seqTM_hoareTime _ _ (scan_hoare bits) stable second
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierWitnessRegisters
