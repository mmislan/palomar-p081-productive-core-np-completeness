module

public import proofs.UnconstrainedPACDetection.FormulaBlockingCleanup
public import proofs.UnconstrainedPACDetection.VerifierActivationEmit

@[expose] public section

namespace UnconstrainedPACDetection.FormulaBlockingRound
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def cleaned (b : Bool) : TM 6 :=
  seqTM (FormulaBlockingMachine.machine b) FormulaBlockingCleanup.machine

theorem cleaned_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (b : Bool) (emitted : List Bool) :
    (cleaned b).HoareTime
      (EmitPred (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val) emitted)
      (FormulaBlockingCleanup.ready φ.encode i.val v.val (FormulaWiring.blocked φ i v b) emitted)
      (24*φ.encode.length+26*v.val+184) := by
  have hs : ∀ inp work out,
      (FormulaBlockingMachine.post φ.encode i.val v.val b (FormulaWiring.blocked φ i v b) emitted inp work out ∧
        ∀ j, (work j).head ≤ 5*φ.encode.length+6*v.val+37) →
      (FormulaBlockingMachine.post φ.encode i.val v.val b (FormulaWiring.blocked φ i v b) emitted
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) ∧
        ∀ j, (transitionTape (work j)).head ≤ 5*φ.encode.length+6*v.val+37) := by
    intro inp work out h
    have hp := FormulaBlockingCleanup.post_safe _ _ _ _ _ _ h.1
    obtain ⟨hi,_,_,_,_,_,_,_,_,ho⟩ := h.1
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hi ▸ (word_parked φ.encode).read_ne_start) (fun j => (hp j).1) ho.parked.read_ne_start
    constructor
    · simpa only [hin,hw,hout] using h.1
    · intro j
      rw [show transitionTape (work j) = work j from congrFun hw j]
      exact h.2 j
  have h := seqTM_hoareTime _ _ (FormulaBlockingMachine.bounded_hoare φ i v b emitted)
    hs (FormulaBlockingCleanup.cleanup_hoare φ.encode i.val v.val b _ emitted)
  exact h.mono_bound (by omega)

theorem ready_parked (src : List Bool) (i v : Nat) (z : Bool) (emitted : List Bool)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : FormulaBlockingCleanup.ready src i v z emitted inp work out) : ∀ j, Parked (work j) := by
  obtain ⟨_,hq,h1,h2,h3,hz,hv,_⟩ := h
  intro j
  fin_cases j
  · change Parked (work 0); rw [hq]; exact word_parked _
  · change Parked (work 1); rw [h1]; exact word_parked _
  · change Parked (work 2); rw [h2]; exact word_parked _
  · change Parked (work 3); rw [h3]; exact word_parked _
  · exact hz.parked
  · change Parked (work 5); rw [hv]; exact parked_regTape _

def deliver : TM 6 := placeWorkTM 4 1 VerifierActivationEmit.machine

theorem deliver_hoare (src : List Bool) (i v : Nat) (z : Bool) (emitted : List Bool) :
    deliver.HoareTime (FormulaBlockingCleanup.ready src i v z emitted)
      (EmitPred (word src) (FormulaComparisonPrepare.initialWork i v) (emitted ++ [z])) 2 := by
  intro inp work out h
  have hp := ready_parked src i v z emitted h
  obtain ⟨rfl,hq,h1,h2,h3,hz,hv,ho⟩ := h
  have hprefix : (work 4).HasBinaryPrefix [z] :=
    ⟨hz.1,hz.2.2.1,fun j hj => hz.2.2.2 (j+1) (by simp at hj; simp; omega)⟩
  have hbit : work 4 = VerifierVerdictAnd.one Γ.start z := by
    rw [VerifierVerdictAnd.prefix_eq _ _ hprefix,hz.2.1]
  have hr := VerifierActivationEmit.run (word src) out (word_parked src).read_ne_start
    ho.parked.read_ne_start Γ.start z
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal VerifierActivationEmit.machine
    4 1 work hr (by intro j _; exact (hp j).read_ne_start)
  let d : Cfg 1 (Fin 3) := ⟨2,word src,fun _ => VerifierVerdictAnd.empty Γ.start,
    out.writeAndMove (Γ.ofBool z) .right⟩
  refine ⟨placeWorkCfg VerifierActivationEmit.machine 4 1 work d,2,le_rfl,?_,rfl,rfl,?_,
    outAcc_append_bit ho z⟩
  unfold deliver
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,hbit]
    · rfl
    rfl
  · funext j
    fin_cases j <;> simp [d,placeWorkCfg,placeWorkInMiddle,
      FormulaComparisonPrepare.initialWork,hq,h1,h2,h3,hv]
    rfl

def machine (b : Bool) : TM 6 := seqTM (cleaned b) deliver

/-- A repeatable occurrence query: append its blocking bit and restore every work tape. -/
theorem round_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (b : Bool) (emitted : List Bool) :
    (machine b).HoareTime
      (EmitPred (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val) emitted)
      (EmitPred (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val)
        (emitted ++ [FormulaWiring.blocked φ i v b]))
      (24*φ.encode.length+26*v.val+187) := by
  have hs : ∀ inp work out,
      FormulaBlockingCleanup.ready φ.encode i.val v.val (FormulaWiring.blocked φ i v b) emitted inp work out →
      FormulaBlockingCleanup.ready φ.encode i.val v.val (FormulaWiring.blocked φ i v b) emitted
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    have hp := ready_parked _ _ _ _ _ h
    have hi := h.1
    have ho := h.2.2.2.2.2.2.2
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hi ▸ (word_parked φ.encode).read_ne_start) (fun j => (hp j).read_ne_start) ho.parked.read_ne_start
    simpa only [hin,hw,hout] using h
  have h := seqTM_hoareTime _ _ (cleaned_hoare φ i v b emitted) hs
    (deliver_hoare φ.encode i.val v.val _ emitted)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaBlockingRound
