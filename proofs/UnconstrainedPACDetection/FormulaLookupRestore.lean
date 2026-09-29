module

public import proofs.UnconstrainedPACDetection.FormulaLookupFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupRestore
open Complexity Complexity.TM
open FormulaLookupScan
open VerifierPairRestore (word word_parked)

def middle (src : List Bool) (i : Nat) : Complexity.TM.TapePred 2 := fun inp work out =>
  inp = word src ∧ OutAcc (run none i src).raw out ∧
  OutAcc (List.replicate (run none i src).clauses true) (work 1) ∧
  (work 0).cells = (word (List.replicate i true)).cells ∧
  Parked (work 0) ∧ (work 0).head ≤ src.length+2

theorem input_hoare (src : List Bool) (i : Nat) :
    (rewindInputTM (n := 2)).HoareTime (FormulaLookupFrame.exit src i)
      (middle src i) (src.length+4) := by
  let P : Complexity.TM.TapePred 2 := fun inp work out =>
    inp.cells = (word src).cells ∧ OutAcc (run none i src).raw out ∧
    OutAcc (List.replicate (run none i src).clauses true) (work 1) ∧
    (work 0).cells = (word (List.replicate i true)).cells ∧
    Parked (work 0) ∧ (work 0).head ≤ src.length+2
  have h := rewindInputTM_hoareTime_frame (src.length+2) (P := P) (by
    rintro inp work out inp' work' out' ⟨hc,hr,hn,hq,hp,hb⟩ he _ rfl rfl
    exact ⟨he.trans hc,hr,hn,hq,hp,hb⟩)
  apply h.consequence
  · rintro inp work out ⟨ho,hc,hq,hqc,hic,his,hib,hqb⟩
    have hp : Parked (work 0) := ⟨hq.1,hq.2.2.2⟩
    refine ⟨his.1,his.2,hib,ho.parked.read_ne_start,ho.parked.1,?_,
      hic,ho,hc,hqc,hp,hqb⟩
    intro j
    fin_cases j
    · exact ⟨hp.read_ne_start,hp.1⟩
    · exact ⟨hc.parked.read_ne_start,hc.parked.1⟩
  · rintro inp work out ⟨hh,hc,hr,hn,hq,hp,hb⟩
    exact ⟨Tape.ext hh hc,hr,hn,hq,hp,hb⟩
  · omega

def restored (src : List Bool) (i : Nat) : Complexity.TM.TapePred 2 := fun inp work out =>
  inp = word src ∧ (work 0) = word (List.replicate i true) ∧
  OutAcc (List.replicate (run none i src).clauses true) (work 1) ∧
  OutAcc (run none i src).raw out

theorem query_hoare (src : List Bool) (i : Nat) :
    (rewindWorkTM (0 : Fin 2)).HoareTime (middle src i)
      (restored src i) (src.length+4) := by
  let P : Complexity.TM.TapePred 2 := fun inp work out =>
    inp = word src ∧ (work 0).cells = (word (List.replicate i true)).cells ∧
    OutAcc (List.replicate (run none i src).clauses true) (work 1) ∧
    OutAcc (run none i src).raw out
  have h := rewindWorkTM_hoareTime_frame (0 : Fin 2) (src.length+2) (P := P) (by
    rintro inp work out inp' work' out' ⟨hi,hq,hc,ho⟩ he _ hw rfl hoc hoh
    refine ⟨hi,he.trans hq,?_,?_⟩
    · rw [hw 1 (by decide)]; exact hc
    · exact (Tape.ext hoh hoc).symm ▸ ho)
  apply h.consequence
  · rintro inp work out ⟨rfl,ho,hc,hq,hp,hb⟩
    refine ⟨?_,hp.2,hb,(word_parked src).read_ne_start,ho.parked.read_ne_start,
      ho.parked.1,?_,rfl,hq,hc,ho⟩
    · rw [hq]; rfl
    · intro j hj
      have he : j = 1 := by fin_cases j <;> simp_all
      subst j
      exact ⟨hc.parked.read_ne_start,hc.parked.1⟩
  · rintro inp work out ⟨hh,hi,hq,hc,ho⟩
    exact ⟨hi,Tape.ext hh hq,hc,ho⟩
  · omega

theorem middle_stable (src : List Bool) (i : Nat) : ∀ inp work out,
    middle src i inp work out → middle src i (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out h
  have hold := h
  obtain ⟨hi,ho,hc,_,hp,_⟩ := h
  have hw : ∀ j, Parked (work j) := by
    intro j
    fin_cases j
    · exact hp
    · exact hc.parked
  obtain ⟨he,hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hw j).read_ne_start)
    ho.parked.read_ne_start
  simpa only [he,hw',ho'] using hold

def machine : TM 2 := seqTM rewindInputTM (rewindWorkTM 0)

/-- The actual two-phase rewind retains the literal and clause accumulators. -/
theorem restore_hoare (src : List Bool) (i : Nat) :
    machine.HoareTime (FormulaLookupFrame.exit src i) (restored src i) (2*src.length+9) := by
  have h := seqTM_hoareTime _ _ (input_hoare src i) (middle_stable src i) (query_hoare src i)
  exact h.mono_bound (by omega)

theorem exit_stable (src : List Bool) (i : Nat) : ∀ inp work out,
    FormulaLookupFrame.exit src i inp work out →
    FormulaLookupFrame.exit src i (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨ho,hc,hq,hqc,hic,his,hib,hqb⟩
  have hp : Parked (work 0) := ⟨hq.1,hq.2.2.2⟩
  have hw : ∀ j, Parked (work j) := by
    intro j
    fin_cases j
    · exact hp
    · exact hc.parked
  have hwork : (fun j => transitionTape (work j)) = work :=
    funext (fun j => transitionTape_eq_self (hw j).read_ne_start)
  rw [hwork,transitionTape_eq_self ho.parked.read_ne_start]
  refine ⟨ho,hc,hq,hqc,?_,?_,?_,hqb⟩
  · exact (Tape.move_cells _ _).trans hic
  · exact his.move _
  · by_cases hr : inp.read = Γ.start
    · have hz : inp.head = 0 := by
        by_contra hn
        exact his.read_ne_start (by omega) hr
      simp [transitionInput,idleDir,hr,Tape.move,hz]
    · simpa [transitionInput,idleDir,hr,Tape.move] using hib

def lookup : TM 2 := seqTM FormulaLookupScan.machine machine

/-- One actual scan followed by both rewinds, ready for the marked comparison. -/
theorem lookup_hoare (src : List Bool) (i : Nat) : lookup.HoareTime
    (EmitPred (word src) (FormulaLookupFrame.initial src i).work [])
    (restored src i) (3*src.length+11) := by
  have h := seqTM_hoareTime _ _ (FormulaLookupFrame.prepared_hoare src i)
    (exit_stable src i) (restore_hoare src i)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaLookupRestore
