module

public import proofs.UnconstrainedPACDetection.VerifierPreparedLayout

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPreparedCertificate
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierPreparedLayout (join)

def frame (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (k : ℕ) : Fin 14 → Tape :=
  VerifierEntityLoopBody.frame s w k (regTape s.entities)

theorem frame_parked (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (k : ℕ) :
    ∀ j, Parked (frame s w k j) :=
  VerifierEntityLoopBody.frame_parked s w k _ (parked_regTape _)

def activationBound (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : ℕ :=
  50*(s.encode.length+2*w.encode.length+1)^2

def pre (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Complexity.TM.TapePred 18 :=
  fun inp work out => inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
    inp.cells = (wordTape s.encode).cells ∧ inp.head ≤ s.encode.length+1 ∧
    work = join (frame s w 2) (VerifierActivationProduce.frame s w (wordTape [])) ∧ out = wordTape []

def stage (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Complexity.TM.TapePred 18 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ inp.cells = (wordTape s.encode).cells ∧
    inp.head ≤ s.encode.length+1+activationBound s w ∧
    ∃ a, (∀ j, Parked (a j)) ∧ work = join (frame s w 2) a ∧
      out = one .start (VerifierActivationNonempty.result s w)

def prepared (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (b : Bool) : Complexity.TM.TapePred 18 :=
  fun inp work out => VerifierEntityLoopBody.sourcePred s inp ∧
    ∃ a, (∀ j, Parked (a j)) ∧ work = join (frame s w k) a ∧ OutAcc [b] out

theorem activation_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    VerifierPreparedLayout.activation.HoareTime (pre s w) (stage s w) (activationBound s w) := by
  rintro inp work out ⟨hi,hc,hh,hwork,hout⟩
  obtain ⟨d,t,ht,hd,hhalt,a,ha,hdw,hdi,hdo⟩ := VerifierPreparedLayout.activation_hoare s hs w hm hw
    (frame s w 2) (frame_parked s w 2) inp work out ⟨hi,hwork,hout⟩
  have hdc := input_cells_eq_of_reachesIn hd
  have hdh := (head_le_start_add_of_reachesIn _ hd).1
  refine ⟨d,t,ht,hd,hhalt,hdi,hdc.trans hc,?_,a,ha,hdw,hdo⟩
  change t ≤ activationBound s w at ht
  change d.input.head ≤ inp.head+t at hdh
  omega

theorem stage_stable (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    ∀ inp work out, stage s w inp work out →
      stage s w (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out h
  have horig := h
  obtain ⟨hi,_,_,a,ha,hwork,hout⟩ := h
  have hf : ∀ j, (work j).read ≠ .start := by
    rw [hwork]; exact fun j => (VerifierPreparedLayout.join_parked _ _ (frame_parked s w 2) ha j).read_ne_start
  have ho : out.read ≠ .start := by rw [hout]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hf ho
  simpa only [hi',hw',ho'] using horig

theorem rewind_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    (rewindInputTM (n := 18)).HoareTime (stage s w)
      (prepared s w 2 (VerifierActivationNonempty.result s w))
      (s.encode.length+activationBound s w+3) := by
  rintro inp work out ⟨_,hc,hh,a,ha,hwork,hout⟩
  let P : Complexity.TM.TapePred 18 := fun i ws o =>
    i.cells = (wordTape s.encode).cells ∧ ws = work ∧ o = out
  have hr := rewindInputTM_hoareTime_frame (n := 18) (s.encode.length+1+activationBound s w)
    (P := P) (by
      rintro i ws o i' ws' o' ⟨hic,hws,ho⟩ hi' _ hws' ho'
      exact ⟨hi'.trans hic,hws'.trans hws,ho'.trans ho⟩)
  have hm := (Tape.StartInvariant.init_ofBool s.encode).move .right
  have hp : ∀ j, Parked (work j) := by
    rw [hwork]; exact VerifierPreparedLayout.join_parked _ _ (frame_parked s w 2) ha
  obtain ⟨d,t,ht,hd,hhalt,hdh,hdc,hdw,hdo⟩ := hr inp work out
    ⟨by rw [hc]; exact hm.1,by intro j hj; rw [hc]; exact hm.2 j hj,hh,
      by rw [hout]; change Γ.blank ≠ Γ.start; decide,
      by rw [hout]; change 1 ≤ 2; decide,
      fun j => ⟨(hp j).read_ne_start,(hp j).1⟩,hc,rfl,rfl⟩
  have hdi : d.input = wordTape s.encode := Tape.ext hdh hdc
  refine ⟨d,t,by omega,hd,hhalt,?_,a,ha,hdw.trans hwork,?_⟩
  · rw [hdi]
    exact ⟨(Tape.init_move_right_hasBinaryString _).hasBinarySuffix,rfl⟩
  · rw [hdo,hout]
    exact VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl

@[reducible] def productivity : TM 18 := placeWorkTM 0 4 VerifierEntityOuterLoop.machine

theorem productivity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) (b : Bool) :
    productivity.HoareTime (prepared s w 2 b)
      (prepared s w (2+s.entities) (VerifierEntityOuterLoop.accumulator s hn w b s.entities))
      (20000*(s.encode.length+3*w.encode.length+2)^4) := by
  rintro inp work out ⟨hi,a,ha,hwork,hout⟩
  subst work
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierEntityOuterBudget.loop_hoare s hs hn w hw hm b
    inp (frame s w 2) out ⟨hi,rfl,hout⟩
  let base := join (frame s w 2) a
  have hb := VerifierPreparedLayout.join_parked _ _ (frame_parked s w 2) ha
  have hr := placeWorkTM_reachesIn_placeWorkCfg_stable_internal VerifierEntityOuterLoop.machine
    0 4 base hd (by intro j _; exact (hb j).read_ne_start)
  refine ⟨placeWorkCfg VerifierEntityOuterLoop.machine 0 4 base d,t,ht,?_,hh,hdi,a,ha,?_,hdo⟩
  · convert hr using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,join,base,hdw,frame]

theorem prepared_stable (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (b : Bool) : ∀ inp work out, prepared s w k b inp work out →
      prepared s w k b (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out h
  have horig := h
  obtain ⟨hi,a,ha,hwork,hout⟩ := h
  have hf : ∀ j, (work j).read ≠ .start := by
    rw [hwork]; exact fun j => (VerifierPreparedLayout.join_parked _ _ (frame_parked s w k) ha j).read_ne_start
  have ho : out.read ≠ .start := by
    have he : out = one .start b := hout.eq
      (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl)
    rw [he]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.1.read_ne_start hf ho
  simpa only [hi',hw',ho'] using horig

@[reducible] def machine : TM 18 := seqTM VerifierPreparedLayout.activation
  (seqTM (rewindInputTM (n := 18)) productivity)

theorem check_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    machine.HoareTime (pre s w)
      (prepared s w (2+s.entities)
        (VerifierEntityOuterLoop.accumulator s hn w (VerifierActivationNonempty.result s w) s.entities))
      (22000*(s.encode.length+3*w.encode.length+2)^4) := by
  have second := seqTM_hoareTime _ _ (rewind_hoare s w)
    (prepared_stable s w 2 _) (productivity_hoare s hs hn w hm hw _)
  have h := seqTM_hoareTime _ _ (activation_hoare s hs w hm hw) (stage_stable s w) second
  apply h.mono_bound
  let X := s.encode.length+2*w.encode.length+1
  let K := s.encode.length+3*w.encode.length+2
  have hx : X ≤ K := by dsimp [X,K]; omega
  have hk : 2 ≤ K := by dsimp [K]; omega
  have hs' : s.encode.length ≤ K := by dsimp [K]; omega
  have hsq : X^2 ≤ K^2 := Nat.pow_le_pow_left hx 2
  have hfour : K^2 ≤ K^4 := by nlinarith [sq_nonneg (K^2-1 : ℤ)]
  have hlin : K ≤ K^2 := by nlinarith
  change 50*X^2+1+(s.encode.length+50*X^2+3+1+20000*K^4) ≤ 22000*K^4
  nlinarith

theorem acceptance_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) :
    VerifierEntityOuterLoop.accumulator s hn w (VerifierActivationNonempty.result s w) s.entities = true ↔
      s.toSource.IntegerFlowChecks (w.entities s.entities) (w.values s.reactions) :=
  VerifierActivationNonempty.certificate_iff s hn w hm

end UnconstrainedPACDetection.VerifierPreparedCertificate
