module

public import proofs.UnconstrainedPACDetection.FormulaLookupRouting
public import proofs.UnconstrainedPACDetection.FormulaTargetRouting

@[expose] public section

namespace UnconstrainedPACDetection.FormulaComparisonPrepare
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def literal (src : List Bool) (i : Nat) : List Bool :=
  FormulaLookupMatching.marked (FormulaLookupScan.run none i src).raw

def initialWork (i v : Nat) : Fin 6 → Tape :=
  ![word (List.replicate i true),word [],word [],word [],word [],regTape v]

theorem initial_parked (i v : Nat) : ∀ j, Parked (initialWork i v j) := by
  intro j
  fin_cases j
  all_goals first | exact word_parked _ | exact parked_regTape _

def middle (src : List Bool) (i v : Nat) (emitted : List Bool) :
    Complexity.TM.TapePred 6 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  OutAcc (List.replicate (FormulaLookupScan.run none i src).clauses true) (work 1) ∧
  work 2 = word (literal src i) ∧ work 3 = word [] ∧ work 4 = word [] ∧
  work 5 = regTape v ∧ OutAcc emitted out

def lookup : TM 6 := placeWorkTM 0 3 FormulaLookupRouting.prepared

theorem lookup_hoare (src : List Bool) (i v : Nat) (emitted : List Bool) :
    lookup.HoareTime (EmitPred (word src) (initialWork i v) emitted)
      (middle src i v emitted) (4*src.length+19) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hd,hh,hdi,hq,hc,hl,hout⟩ := FormulaLookupRouting.ready_hoare src i emitted
    (word src) (FormulaLookupRouting.initialWork i) out ⟨rfl,rfl,ho⟩
  have hr := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaLookupRouting.prepared
    0 3 (initialWork i v) hd (by intro j _; exact (initial_parked i v j).read_ne_start)
  refine ⟨placeWorkCfg FormulaLookupRouting.prepared 0 3 (initialWork i v) d,
    t,ht,?_,hh,hdi,hq,hc,hl,rfl,rfl,rfl,hout⟩
  unfold lookup
  convert hr using 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; fin_cases j <;> rfl
  · rfl

theorem middle_parked (src : List Bool) (i v : Nat) (emitted : List Bool)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : middle src i v emitted inp work out) : ∀ j, Parked (work j) := by
  obtain ⟨_,hq,hc,hl,ht,he,hv,_⟩ := h
  intro j
  fin_cases j
  · change Parked (work 0); rw [hq]; exact word_parked _
  · exact hc.parked
  · change Parked (work 2); rw [hl]; exact word_parked _
  · change Parked (work 3); rw [ht]; exact word_parked _
  · change Parked (work 4); rw [he]; exact word_parked _
  · change Parked (work 5); rw [hv]; exact parked_regTape _

def ready (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool) :
    Complexity.TM.TapePred 6 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  OutAcc (List.replicate (FormulaLookupScan.run none i src).clauses true) (work 1) ∧
  work 2 = word (literal src i) ∧
  work 3 = word (FormulaLookupMatching.marked (FormulaLookupMatching.target v b)) ∧
  work 4 = word [] ∧ work 5 = regTape v ∧ OutAcc emitted out

theorem target_hoare (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool) :
    (FormulaTargetRouting.prepared b).HoareTime (middle src i v emitted)
      (ready src i v b emitted) (5*v+12) := by
  intro inp work out h
  have hp := middle_parked src i v emitted h
  obtain ⟨rfl,hq,hc,hl,ht,he,hv,ho⟩ := h
  obtain ⟨d,t,hb,hd,hh,hdi,hw,hdt,hout⟩ := FormulaTargetRouting.ready_hoare
    v b (word src) work emitted (word_parked src) hp hv ht _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,hb,hd,hh,hdi,?_,?_,?_,hdt,?_,?_,hout⟩
  · rw [hw 0 (by decide)]; exact hq
  · rw [hw 1 (by decide)]; exact hc
  · rw [hw 2 (by decide)]; exact hl
  · rw [hw 4 (by decide)]; exact he
  · rw [hw 5 (by decide)]; exact hv

def machine (b : Bool) : TM 6 := seqTM lookup (FormulaTargetRouting.prepared b)

/-- Both comparison words are prepared by one actual six-work-tape machine. -/
theorem ready_hoare (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool) :
    (machine b).HoareTime (EmitPred (word src) (initialWork i v) emitted)
      (ready src i v b emitted) (4*src.length+5*v+32) := by
  have hs : ∀ inp work out, middle src i v emitted inp work out →
      middle src i v emitted (transitionInput inp) (fun j => transitionTape (work j))
        (transitionTape out) := by
    intro inp work out h
    have hp := middle_parked src i v emitted h
    have hi := h.1
    have ho := h.2.2.2.2.2.2.2
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start)
      ho.parked.read_ne_start
    simpa only [hin,hw,hout] using h
  have h := seqTM_hoareTime _ _ (lookup_hoare src i v emitted) hs (target_hoare src i v b emitted)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaComparisonPrepare
