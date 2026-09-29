module

public import proofs.UnconstrainedPACDetection.FormulaClauseGuard
public import proofs.UnconstrainedPACDetection.VerifierFieldCardinalityCheck

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseCompare
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bank (a b : Nat) (raw : List Bool) : Fin 4 → Tape :=
  ![regTape a,regTape b,word [],word raw]
def bit (a b : Nat) : Bool := VerifierBinaryEquality.compare true
  (List.replicate b true) (List.replicate a true)

theorem bit_eq (a b : Nat) : bit a b = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bit,VerifierBinaryEquality.equality_iff,
    VerifierFieldCardinalityCheck.unary_value_injective,decide_eq_true_eq]

theorem bank_parked (a b : Nat) (raw : List Bool) : ∀ j, Parked (bank a b raw j) := by
  intro j; fin_cases j
  · exact parked_regTape _
  · exact parked_regTape _
  · exact word_parked _
  · exact word_parked _

def scan : TM 4 := placeWorkTM 0 1 FormulaComparisonScan.base
def post (a b : Nat) (raw ys : List Bool) (inp : Tape) : Complexity.TM.TapePred 4 :=
  fun i w o => i = inp ∧
    (w 0).HasBinarySuffix [] ∧ (w 1).HasBinarySuffix [] ∧
    (w 0).cells = (regTape a).cells ∧ (w 1).cells = (regTape b).cells ∧
    OutAcc [bit a b] (w 2) ∧ w 3 = word raw ∧ OutAcc ys o

theorem scan_hoare (a b : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    scan.HoareTime (EmitPred inp (bank a b raw) ys) (post a b raw ys inp)
      (max a b+1) := by
  rintro i w o ⟨hin,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,h0,h1,hc0,hc1,hv,hout⟩ :=
    FormulaComparisonScan.base_hoare (List.replicate b true) (List.replicate a true)
      inp ys hi _ _ o ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaComparisonScan.base
    0 1 (bank a b raw) hr (by intro j _; exact (bank_parked a b raw j).read_ne_start)
  refine ⟨placeWorkCfg _ 0 1 (bank a b raw) d,t,?_,?_,hh,hdi,h0,h1,?_,?_,hv,rfl,hout⟩
  · simpa [List.length_replicate,Nat.max_comm] using ht
  · unfold scan
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;>
        simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,bank,FormulaEndpointRegisters.unary_word]
    · rfl
  · change (d.work 0).cells = (regTape a).cells
    simpa only [FormulaEndpointRegisters.unary_word] using hc0
  · change (d.work 1).cells = (regTape b).cells
    simpa only [FormulaEndpointRegisters.unary_word] using hc1

theorem post_parked (a b : Nat) (raw ys : List Bool) (inp : Tape) {i w o}
    (h : post a b raw ys inp i w o) : ∀ j, Parked (w j) := by
  obtain ⟨_,h0,h1,hc0,hc1,hv,h3,_⟩ := h
  intro j; fin_cases j
  · change Parked (w 0)
    exact ⟨h0.1,by rw [hc0]; exact (parked_regTape a).2⟩
  · change Parked (w 1)
    exact ⟨h1.1,by rw [hc1]; exact (parked_regTape b).2⟩
  · exact hv.parked
  · change Parked (w 3); rw [h3]; exact word_parked _

def guarded : TM 4 := placeWorkTM 2 0 FormulaClauseGuard.machine
def clearedPost (a b : Nat) (raw ys : List Bool) (inp : Tape) : Complexity.TM.TapePred 4 :=
  fun i w o => i = inp ∧
    (w 0).HasBinarySuffix [] ∧ (w 1).HasBinarySuffix [] ∧
    (w 0).cells = (regTape a).cells ∧ (w 1).cells = (regTape b).cells ∧
    w 2 = word [] ∧ w 3 = word raw ∧ OutAcc ys o

theorem guard_hoare (a b : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    guarded.HoareTime (post a b raw ys inp)
      (clearedPost a b raw (ys ++ [bit a b && !raw.isEmpty]) inp) 2 := by
  intro i w o h
  have hp := post_parked a b raw ys inp h
  obtain ⟨hin,h0,h1,hc0,hc1,hv,h3,ho⟩ := h
  subst i
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ :=
    FormulaClauseGuard.emit_hoare inp hi (bit a b) raw ys
      inp ![w 2,w 3] o ⟨rfl,hv,h3,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaClauseGuard.machine
    2 0 w hr (by intro j _; exact (hp j).read_ne_start)
  refine ⟨placeWorkCfg FormulaClauseGuard.machine 2 0 w d,t,ht,?_,hh,hdi,h0,h1,hc0,hc1,?_,?_,hdo⟩
  · unfold guarded
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · change d.work 0 = _; rw [hdw]; rfl
  · change d.work 1 = _; rw [hdw]; rfl

def first : TM 4 := seqTM scan guarded

/-- Physical equality and literal-presence guard; register restoration follows. -/
theorem guarded_scan (a b : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    first.HoareTime (EmitPred inp (bank a b raw) ys)
      (clearedPost a b raw (ys ++ [decide (a=b) && !raw.isEmpty]) inp)
      (max a b+4) := by
  have hs : ∀ i w o, post a b raw ys inp i w o →
      post a b raw ys inp (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
    intro i w o h
    obtain ⟨hei,hew,heo⟩ := phaseTransition_eq_self_of_reads_ne_start
      (h.1 ▸ hi.read_ne_start) (fun j => (post_parked a b raw ys inp h j).read_ne_start)
      h.2.2.2.2.2.2.2.parked.read_ne_start
    simpa only [hei,hew,heo] using h
  have h := seqTM_hoareTime _ _ (scan_hoare a b raw ys inp hi) hs
    (guard_hoare a b raw ys inp hi)
  simpa only [first, bit_eq,Nat.add_assoc] using h

theorem rewind_emit {n : Nat} (j : Fin n) (v : Nat) (ys : List Bool)
    (inp : Tape) (w : Fin n → Tape) (hi : Parked inp) (hp : ∀ k, Parked (w k))
    (hc : (w j).cells = (regTape v).cells) :
    (rewindWorkTM j).HoareTime (EmitPred inp w ys)
      (EmitPred inp (Function.update w j (regTape v)) ys) ((w j).head+2) := by
  rintro i ws o ⟨hin,hw,ho⟩
  subst i; subst ws
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierTapeCleanup.rewind_hoare j w inp o
    (by rw [hc]; rfl) (by rw [hc]; exact (parked_regTape v).2)
    (fun k => ⟨(hp k).read_ne_start,(hp k).1⟩)
    hi.read_ne_start ho.parked.read_ne_start ho.parked.1 inp w o ⟨rfl,rfl,rfl⟩
  refine ⟨d,t,ht,hr,hh,hdi,?_,hdo ▸ ho⟩
  rw [hdw]
  funext k
  by_cases hk : k = j
  · subst k
    simp only [VerifierTapeCleanup.restored,Function.update_self]
    exact Tape.ext rfl hc
  · simp [VerifierTapeCleanup.restored,Function.update_of_ne hk]

theorem cleared_parked (a b : Nat) (raw ys : List Bool) (inp : Tape) {i w o}
    (h : clearedPost a b raw ys inp i w o) : ∀ j, Parked (w j) := by
  obtain ⟨_,h0,h1,hc0,hc1,h2,h3,_⟩ := h
  intro j; fin_cases j
  · change Parked (w 0)
    exact ⟨h0.1,by rw [hc0]; exact (parked_regTape a).2⟩
  · change Parked (w 1)
    exact ⟨h1.1,by rw [hc1]; exact (parked_regTape b).2⟩
  · change Parked (w 2); rw [h2]; exact word_parked _
  · change Parked (w 3); rw [h3]; exact word_parked _

def restore : TM 4 := seqTM (rewindWorkTM 0) (rewindWorkTM 1)

theorem restore_hoare (a b : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    restore.HoareTime
      (fun i w o => clearedPost a b raw ys inp i w o ∧ ∀ j, (w j).head ≤ max a b+5)
      (EmitPred inp (bank a b raw) ys) (2*max a b+15) := by
  rintro i w o ⟨h,hheads⟩
  have hp := cleared_parked a b raw ys inp h
  obtain ⟨hin,_,_,hc0,hc1,h2,h3,ho⟩ := h
  subst i
  have hfirst := rewind_emit 0 a ys inp w hi hp hc0
  have hp' : ∀ j, Parked (Function.update w 0 (regTape a) j) := by
    intro j
    by_cases hj : j = 0
    · subst j; simpa using parked_regTape a
    · simpa only [Function.update_of_ne hj] using hp j
  have hsecond := rewind_emit 1 b ys inp (Function.update w 0 (regTape a)) hi hp'
    (by simpa using hc1)
  have htotal := seqTM_hoareTime _ _ hfirst (emitPred_transition hi hp' ys) hsecond
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := htotal inp w o ⟨rfl,rfl,ho⟩
  refine ⟨d,t,?_,hr,hh,hdi,?_,hdo⟩
  · have h0 := hheads 0
    have h1 := hheads 1
    simp only [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)] at ht
    omega
  · rw [hdw]
    funext j; fin_cases j <;> simp [bank,h2,h3]

def machine : TM 4 := seqTM first restore

/-- Repeatable physical count comparison with literal-presence guard. -/
theorem compare_hoare (a b : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    machine.HoareTime (EmitPred inp (bank a b raw) ys)
      (EmitPred inp (bank a b raw) (ys ++ [decide (a=b) && !raw.isEmpty]))
      (3*max a b+20) := by
  have hb : first.HoareTime (EmitPred inp (bank a b raw) ys)
      (fun i w o => clearedPost a b raw (ys ++ [decide (a=b) && !raw.isEmpty]) inp i w o ∧
        ∀ j, (w j).head ≤ max a b+5) (max a b+4) := by
    intro i w o h
    obtain ⟨d,t,ht,hr,hh,hpost⟩ := guarded_scan a b raw ys inp hi i w o h
    have hhead := (head_le_start_add_of_reachesIn first hr).2.2
    refine ⟨d,t,ht,hr,hh,hpost,?_⟩
    intro j
    have hj : (w j).head = 1 := by rw [h.2.1]; fin_cases j <;> rfl
    have hk := hhead j
    change (d.work j).head ≤ (w j).head+t at hk
    omega
  have hs : ∀ i w o,
      (clearedPost a b raw (ys ++ [decide (a=b) && !raw.isEmpty]) inp i w o ∧
        ∀ j, (w j).head ≤ max a b+5) →
      (clearedPost a b raw (ys ++ [decide (a=b) && !raw.isEmpty]) inp
        (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) ∧
        ∀ j, (transitionTape (w j)).head ≤ max a b+5) := by
    intro i w o h
    have hp := cleared_parked _ _ _ _ _ h.1
    obtain ⟨hei,hew,heo⟩ := phaseTransition_eq_self_of_reads_ne_start
      (h.1.1 ▸ hi.read_ne_start) (fun j => (hp j).read_ne_start)
      h.1.2.2.2.2.2.2.2.parked.read_ne_start
    constructor
    · simpa only [hei,hew,heo] using h.1
    · intro j
      rw [congrFun hew j]
      exact h.2 j
  have h := seqTM_hoareTime _ _ hb hs (restore_hoare a b raw _ inp hi)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaClauseCompare
