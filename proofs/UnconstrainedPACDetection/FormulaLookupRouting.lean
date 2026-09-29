module

public import proofs.UnconstrainedPACDetection.FormulaLookupRestore
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupRouting
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def initialWork (i : Nat) : Fin 3 → Tape :=
  fun j => if j = 0 then word (List.replicate i true) else word []

def result (src : List Bool) (i : Nat) (raw emitted : List Bool) :
    Complexity.TM.TapePred 3 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  OutAcc (List.replicate (FormulaLookupScan.run none i src).clauses true) (work 1) ∧
  OutAcc raw (work 2) ∧ OutAcc emitted out

@[reducible] def routed : TM 3 := FormulaLookupRestore.lookup.retargetOutput

theorem routed_hoare (src : List Bool) (i : Nat) (emitted : List Bool) :
    routed.HoareTime (EmitPred (word src) (initialWork i) emitted)
      (result src i (FormulaLookupScan.run none i src).raw emitted) (3*src.length+11) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hd,hh,hi,hq,hc,hl⟩ := FormulaLookupRestore.lookup_hoare src i
    (word src) (FormulaLookupFrame.initial src i).work (word []) ⟨rfl,rfl,outAcc_nil_init⟩
  have hr := VerifierOutputRouting.run_frame _ out ho.parked.read_ne_start hd
  refine ⟨VerifierOutputRouting.wrap _ out d,t,ht,?_,hh,hi,?_,?_,?_,ho⟩
  · change FormulaLookupRestore.lookup.retargetOutput.reachesIn t _ _
    have he :
        (⟨routed.qstart,word src,initialWork i,out⟩ : Cfg 3 routed.Q) =
        VerifierOutputRouting.wrap FormulaLookupRestore.lookup out
          ⟨FormulaLookupRestore.lookup.qstart,word src,
            (FormulaLookupFrame.initial src i).work,word []⟩ := by
      apply Cfg.ext
      · rfl
      · rfl
      · funext j
        fin_cases j <;> rfl
      · rfl
    rw [he]
    exact hr
  · exact hq
  · exact hc
  · exact hl

@[reducible] def mark : TM 3 := (emitBitsTM (n := 2) [true]).retargetOutput

theorem mark_hoare (src : List Bool) (i : Nat) (raw emitted : List Bool) :
    mark.HoareTime (result src i raw emitted) (result src i (raw ++ [true]) emitted) 1 := by
  rintro inp work out ⟨rfl,hq,hc,hl,ho⟩
  let small : Fin 2 → Tape := fun j => work (Fin.castSucc j)
  have hp : ∀ j, Parked (small j) := by
    intro j
    fin_cases j
    · change Parked (work 0)
      rw [hq]; exact word_parked _
    · exact hc.parked
  obtain ⟨d,hd,hh,hi,hw,hout⟩ := emitBitsTM_reachesIn_frame [true]
    (word src) small (work 2) raw (word_parked src) hp hl
  have hr := VerifierOutputRouting.run_frame _ out ho.parked.read_ne_start hd
  refine ⟨VerifierOutputRouting.wrap _ out d,1,le_rfl,?_,hh,hi,?_,?_,?_,ho⟩
  · change (emitBitsTM (n := 2) [true]).retargetOutput.reachesIn ([true].length) _ _
    have he :
        (⟨mark.qstart,word src,work,out⟩ : Cfg 3 mark.Q) =
        VerifierOutputRouting.wrap (emitBitsTM (n := 2) [true]) out
          ⟨(emitBitsTM (n := 2) [true]).qstart,word src,small,work 2⟩ := by
      apply Cfg.ext
      · rfl
      · rfl
      · funext j
        fin_cases j <;> rfl
      · rfl
    rw [he]
    exact hr
  · change d.work 0 = _
    rw [hw]; exact hq
  · change OutAcc _ (d.work 1)
    rw [hw]; exact hc
  · exact hout

theorem result_stable (src : List Bool) (i : Nat) (raw emitted : List Bool) :
    ∀ inp work out, result src i raw emitted inp work out →
      result src i raw emitted (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out h
  have hold := h
  obtain ⟨hi,hq,hc,hl,ho⟩ := h
  have hp : ∀ j, Parked (work j) := by
    intro j
    fin_cases j
    · change Parked (work 0)
      rw [hq]; exact word_parked _
    · exact hc.parked
    · exact hl.parked
  obtain ⟨he,hw,heout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start)
    ho.parked.read_ne_start
  simpa only [he,hw,heout] using hold

@[reducible] def machine : TM 3 := seqTM routed mark

/-- The scanner's result is marked in scratch tape 2; caller output is preserved. -/
theorem marked_hoare (src : List Bool) (i : Nat) (emitted : List Bool) :
    machine.HoareTime (EmitPred (word src) (initialWork i) emitted)
      (result src i ((FormulaLookupScan.run none i src).raw ++ [true]) emitted)
      (3*src.length+13) := by
  have h := seqTM_hoareTime _ _ (routed_hoare src i emitted)
    (result_stable src i _ emitted) (mark_hoare src i _ emitted)
  exact h.mono_bound (by omega)

def ready (src : List Bool) (i : Nat) (raw emitted : List Bool) :
    Complexity.TM.TapePred 3 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  OutAcc (List.replicate (FormulaLookupScan.run none i src).clauses true) (work 1) ∧
  work 2 = word raw ∧ OutAcc emitted out

theorem rewind_hoare (src : List Bool) (i : Nat) (raw emitted : List Bool) :
    (rewindWorkTM (2 : Fin 3)).HoareTime (result src i raw emitted)
      (ready src i raw emitted) (raw.length+3) := by
  rintro inp work out ⟨rfl,hq,hc,hl,ho⟩
  have hp : ∀ j, Parked (work j) := by
    intro j
    fin_cases j
    · change Parked (work 0)
      rw [hq]; exact word_parked _
    · exact hc.parked
    · exact hl.parked
  obtain ⟨d,t,ht,hd,hh,hi,hw,hout⟩ :=
    VerifierPairRestore.restore_word (2 : Fin 3) raw emitted (word src) work
      (word_parked src) hp hl _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hd,hh,hi,?_,?_,?_,hout⟩
  · rw [hw]; simpa using hq
  · rw [hw]; simpa using hc
  · rw [hw]; simp

theorem raw_length_bound (src : List Bool) (i : Nat) :
    (FormulaLookupScan.run none i src).raw.length ≤ src.length+1 := by
  obtain ⟨d,t,ht,hr,_,ho,_⟩ := FormulaLookupFrame.prepared_run src i
  have h := (head_le_start_add_of_reachesIn FormulaLookupScan.machine hr).2.1
  change d.output.head ≤ 1+t at h
  rw [ho.1] at h
  omega

@[reducible] def prepared : TM 3 := seqTM machine (rewindWorkTM 2)

/-- The marked literal is ready for comparison, with caller output untouched. -/
theorem ready_hoare (src : List Bool) (i : Nat) (emitted : List Bool) :
    prepared.HoareTime (EmitPred (word src) (initialWork i) emitted)
      (ready src i ((FormulaLookupScan.run none i src).raw ++ [true]) emitted)
      (4*src.length+19) := by
  have h := seqTM_hoareTime _ _ (marked_hoare src i emitted)
    (result_stable src i _ emitted) (rewind_hoare src i _ emitted)
  apply h.mono_bound
  have hb := raw_length_bound src i
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

end UnconstrainedPACDetection.FormulaLookupRouting
