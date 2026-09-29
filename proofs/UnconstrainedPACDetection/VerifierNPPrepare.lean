module

public import proofs.UnconstrainedPACDetection.VerifierNPCountRouting
public import proofs.UnconstrainedPACDetection.VerifierNPBound
public import proofs.UnconstrainedPACDetection.VerifierCountPrepare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPPrepare
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def countedWork (N : Nat) : Fin 33 → Tape :=
  Function.update (fun _ => word []) 30 (regTape (N+1))

def preparedWork (N : Nat) : Fin 33 → Tape := VerifierNPBound.finalWork (countedWork N) N

theorem counted_parked (N : Nat) : ∀ j, Parked (countedWork N j) := by
  intro j
  by_cases hj : j = 30
  · subst j; simpa [countedWork] using parked_regTape (N+1)
  · simpa [countedWork,hj] using word_parked []

theorem prepared_parked (N : Nat) : ∀ j, Parked (preparedWork N j) := by
  intro j
  by_cases h31 : j = 31
  · subst j; simpa [preparedWork,VerifierNPBound.finalWork] using parked_regTape (VerifierNPBound.cap N)
  by_cases h32 : j = 32
  · subst j; simpa [preparedWork,VerifierNPBound.finalWork] using parked_regTape (VerifierNPBound.cap N)
  · simpa only [preparedWork,VerifierNPBound.finalWork,Function.update_of_ne h31,
      Function.update_of_ne h32] using counted_parked N j

theorem restore_input (src : List Bool) (inp : Tape) (work : Fin 33 → Tape)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hc : inp.cells = (word src).cells) (hb : inp.head ≤ src.length+4) :
    (rewindInputTM (n := 33)).HoareTime (EmitPred inp work [])
      (EmitPred (word src) work []) (src.length+6) := by
  let P : Complexity.TM.TapePred 33 := fun a ws out => a.cells = (word src).cells ∧
    ws = work ∧ OutAcc [] out
  have h := rewindInputTM_hoareTime_frame (src.length+4) (P := P) (by
    rintro a ws out a' ws' out' ⟨ha,hws,ho⟩ hc' _ hw' ho'
    exact ⟨hc'.trans ha,hw'.trans hws,ho' ▸ ho⟩)
  apply h.consequence
  · rintro a ws out ⟨ha,hws,ho⟩
    subst a; subst ws
    refine ⟨?_,hi.2,hb,ho.parked.read_ne_start,ho.parked.1,
      fun j => ⟨(hw j).read_ne_start,(hw j).1⟩,hc,rfl,ho⟩
    rw [hc]; rfl
  · rintro a ws out ⟨hh,hcells,hws,ho⟩
    exact ⟨Tape.ext hh hcells,hws,ho⟩
  · omega

def machine : TM 33 := seqTM (rewindWorkTM (30 : Fin 33))
  (seqTM VerifierNPBound.machine (rewindInputTM (n := 33)))

def arithmeticTime (N : Nat) : Nat := 4*(layerBudget (VerifierNPBound.cap N)+1)+1

theorem prepare_hoare (src : List Bool) : machine.HoareTime (VerifierNPCountRouting.after src)
    (EmitPred (word src) (preparedWork src.length) []) (2*src.length+12+arithmeticTime src.length) := by
  intro inp work out h
  obtain ⟨hc,hi,hb,hcount,hframe,hout⟩ := h
  have hp : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j = 30
    · subst j; exact hcount.parked
    · rw [hframe j hj]; exact word_parked []
  have hu : word (List.replicate (src.length+1) true) = regTape (src.length+1) :=
    VerifierCountPrepare.unary_eq_reg _
  have hzero : word [] = regTape 0 := VerifierCountPrepare.unary_eq_reg 0
  have hrest := VerifierPairRestore.restore_word (30 : Fin 33)
    (List.replicate (src.length+1) true) [] inp work hi hp hcount
  rw [hu,List.length_replicate] at hrest
  have hwork : Function.update work 30 (regTape (src.length+1)) = countedWork src.length := by
    funext j
    by_cases hj : j = 30
    · subst j; simp [countedWork]
    · simp only [countedWork,Function.update_of_ne hj]; exact hframe j hj
  rw [hwork] at hrest
  have hbound := VerifierNPBound.counter_hoare src.length inp (countedWork src.length)
    hi (counted_parked _) (by simp [countedWork])
    (by simpa [countedWork] using hzero) (by simpa [countedWork] using hzero)
  have hrewind := restore_input src inp (preparedWork src.length) hi (prepared_parked _) hc hb
  have htail := seqTM_hoareTime _ _ hbound
    (emitPred_transition hi (prepared_parked src.length) []) hrewind
  have htotal := seqTM_hoareTime _ _ hrest
    (emitPred_transition hi (counted_parked src.length) []) htail
  exact (htotal.mono_bound (by unfold arithmeticTime; omega)) inp work out ⟨rfl,rfl,hout⟩

theorem count_after_stable (src : List Bool) : ∀ inp work out,
    VerifierNPCountRouting.after src inp work out →
    VerifierNPCountRouting.after src (transitionInput inp) (fun j => transitionTape (work j))
      (transitionTape out) := by
  intro inp work out h
  have hh := h
  obtain ⟨_,hi,_,hcount,hframe,hout⟩ := hh
  have hp : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j = 30
    · subst j; exact hcount.parked
    · rw [hframe j hj]; exact word_parked []
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (hp j).read_ne_start) hout.parked.read_ne_start
  simpa only [hi',hw',ho'] using h

def setup : TM 33 := seqTM VerifierNPCountRouting.machine machine

theorem setup_hoare (src : List Bool) : setup.HoareTime (VerifierNPCountRouting.initial src)
    (EmitPred (word src) (preparedWork src.length) []) (3*src.length+16+arithmeticTime src.length) := by
  have h := seqTM_hoareTime _ _ (VerifierNPCountRouting.count_hoare src)
    (count_after_stable src) (prepare_hoare src)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierNPPrepare
