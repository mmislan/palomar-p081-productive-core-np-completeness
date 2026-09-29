module

public import proofs.UnconstrainedPACDetection.FormulaHeaderPreparation
public import proofs.UnconstrainedPACDetection.FormulaNumberField
public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation

@[expose] public section

namespace UnconstrainedPACDetection.FormulaEntityHeader
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def value (src : List Bool) : Nat := FormulaHeaderRegisters.value
  (FormulaHeaderPreparation.occurrences src) (FormulaHeaderPreparation.maximum src+1)

@[reducible] def inner : TM 5 := seqTM FormulaHeaderPreparation.placed FormulaHeaderPreparation.finish

theorem inner_hoare (src : List Bool) : inner.HoareTime
    (EmitPred (word src) FormulaHeaderPreparation.emptyBank [])
    (FormulaHeaderPreparation.frame src (FormulaHeaderPreparation.maximum src+1) (value src))
    (FormulaHeaderPreparation.timeBound src) := by
  have hm := FormulaMaximumRestore.value_bound src
  have hv : FormulaHeaderPreparation.maximum src+1 ≤ 3*src.length+2 := by
    simpa [FormulaHeaderPreparation.maximum] using Nat.add_le_add_right hm 1
  have hf := seqTM_hoareTime _ _
    (FormulaHeaderPreparation.increment_hoare src (FormulaHeaderPreparation.maximum src))
    (FormulaHeaderPreparation.stable src (FormulaHeaderPreparation.maximum src+1) 0)
    (FormulaHeaderPreparation.arithmetic_hoare src (FormulaHeaderPreparation.maximum src+1) hv)
  have h := seqTM_hoareTime _ _ (FormulaHeaderPreparation.placed_hoare src)
    (FormulaHeaderPreparation.stable src (FormulaHeaderPreparation.maximum src) 0) hf
  apply h.mono_bound
  unfold FormulaHeaderPreparation.timeBound FormulaHeaderPreparation.maximum
  omega

def data (src : List Bool) (w : Fin 7 → Tape) : Prop :=
  w 0 = word (FormulaTokenCount.countBits true src) ∧
  w 1 = regTape (FormulaHeaderPreparation.occurrences src) ∧
  w 2 = regTape (FormulaHeaderPreparation.maximum src+1) ∧
  OutAcc (FormulaMaximum.maximumBits src) (w 3) ∧ w 4 = regTape (value src)

def ready (src : List Bool) : Complexity.TM.TapePred 7 := fun i w o =>
  i = word src ∧ data src w ∧ w 5 = word [] ∧ w 6 = word [] ∧ OutAcc [] o

theorem ready_parked (src : List Bool) {i w o} (h : ready src i w o) :
    ∀ j, Parked (w j) := by
  obtain ⟨_,⟨h0,h1,h2,h3,h4⟩,h5,h6,_⟩ := h
  intro j
  fin_cases j
  · change Parked (w 0); rw [h0]; exact word_parked _
  · change Parked (w 1); rw [h1]; exact parked_regTape _
  · change Parked (w 2); rw [h2]; exact parked_regTape _
  · exact h3.parked
  · change Parked (w 4); rw [h4]; exact parked_regTape _
  · change Parked (w 5); rw [h5]; exact word_parked _
  · change Parked (w 6); rw [h6]; exact word_parked _

def empty : Fin 7 → Tape := fun _ => regTape 0
@[reducible] def placed : TM 7 := placeWorkTM 0 2 inner

theorem placed_hoare (src : List Bool) : placed.HoareTime
    (EmitPred (word src) empty []) (ready src) (FormulaHeaderPreparation.timeBound src) := by
  rintro i w o ⟨hin,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,h0,h1,h2,h3,h4,hout⟩ := inner_hoare src
    (word src) FormulaHeaderPreparation.emptyBank o ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal inner 0 2 empty hr
    (by intro j _; exact (parked_regTape 0).read_ne_start)
  refine ⟨placeWorkCfg _ 0 2 empty d,t,ht,?_,hh,hdi,⟨h0,h1,h2,h3,h4⟩,?_,?_,hout⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;>
        simp [placeWorkCfg,placeWorkInMiddle,empty,FormulaHeaderPreparation.emptyBank]
    · rfl
  · change regTape 0 = word []
    exact FormulaParameters.empty_reg.symm
  · change regTape 0 = word []
    exact FormulaParameters.empty_reg.symm

def initial (src : List Bool) : Complexity.TM.TapePred 7 := fun i w o =>
  i = Tape.init (src.map Γ.ofBool) ∧ (∀ j, w j = Tape.init []) ∧ o = Tape.init []

@[reducible] def prepare : TM 7 := seqTM bumpTM placed

theorem prepare_hoare (src : List Bool) : prepare.HoareTime
    (initial src) (ready src) (FormulaHeaderPreparation.timeBound src+2) := by
  have hb : (bumpTM (n := 7)).HoareTime (initial src) (EmitPred (word src) empty []) 1 := by
    apply (bumpTM_hoareTime src).consequence
    · intro i w o h; exact h
    · rintro i w o ⟨hi,hw,ho⟩
      exact ⟨hi,funext (fun j => (hw j).eq_regT),ho⟩
    · omega
  have h := seqTM_hoareTime _ _ hb
    (emitPred_transition (word_parked src) (fun _ => parked_regTape 0) []) (placed_hoare src)
  exact h.mono_bound (by omega)

def swap : Equiv.Perm (Fin 7) := Equiv.swap 4 6
@[reducible] def numberPlaced : TM 7 := placeWorkTM 4 0 FormulaNumberField.machine
@[reducible] def emit : TM 7 := VerifierWorkPermutation.machine numberPlaced swap

def afterWork (w : Fin 7 → Tape) (v : Nat) : Fin 7 → Tape :=
  Function.update (Function.update w 5 (word [true])) 6 (word v.bits)

theorem emit_hoare (v : Nat) (inp : Tape) (w : Fin 7 → Tape) (ys : List Bool)
    (hi : Parked inp) (hp : ∀ j, Parked (w j))
    (h4 : w 4 = regTape v) (h5 : w 5 = word []) (h6 : w 6 = word []) :
    emit.HoareTime (EmitPred inp w ys)
      (EmitPred inp (afterWork w v) (ys ++ BinaryFields.encodeField v.bits))
      (24*(v+1)^2+8) := by
  rintro i ws o ⟨hin,hw,ho⟩
  subst i; subst ws
  let base : Fin 7 → Tape := fun j => w (swap j)
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaNumberField.field_bounded v inp hi ys
    inp (VerifierCountPrepare.initial v) o ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    FormulaNumberField.machine 4 0 base hr
    (by intro j _; exact (hp (swap j)).read_ne_start)
  have hrouted := VerifierWorkPermutation.run_commute numberPlaced swap hs
  refine ⟨VerifierWorkPermutation.wrap numberPlaced swap (placeWorkCfg _ 4 0 base d),
    t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hrouted using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;>
        simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
          base,swap,Equiv.swap_apply_def,VerifierCountPrepare.initial,
          VerifierCountPrepare.unary_eq_reg,h4,h5,h6]
      all_goals rfl
    · rfl
  · funext j
    fin_cases j <;>
      simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        base,swap,Equiv.swap_apply_def,FormulaNumberField.bank,hdw,afterWork,h4]

def finished (src : List Bool) : Complexity.TM.TapePred 7 := fun i w o =>
  i = word src ∧ data src w ∧ w 5 = word [true] ∧
    w 6 = word (value src).bits ∧ OutAcc (BinaryFields.encodeField (value src).bits) o

theorem finish_hoare (src : List Bool) : emit.HoareTime (ready src) (finished src)
    (24*(value src+1)^2+8) := by
  intro i w o h
  have hp := ready_parked src h
  obtain ⟨hin,hd,h5,h6,ho⟩ := h
  subst i
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := emit_hoare (value src) (word src) w []
    (word_parked src) hp hd.2.2.2.2 h5 h6 (word src) w o ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,hdi,?_,?_,?_,?_⟩
  · rw [hdw]
    simpa [data,afterWork] using hd
  · rw [hdw]; simp [afterWork]
  · rw [hdw]; simp [afterWork]
  · simpa using hdo

@[reducible] def machine : TM 7 := seqTM prepare emit
def bound (src : List Bool) : Nat :=
  FormulaHeaderPreparation.timeBound src+24*(FormulaHeaderPreparation.cap src+1)^2+11

theorem ordinary_hoare (src : List Bool) : machine.HoareTime
    (initial src) (finished src) (bound src) := by
  have hs : ∀ i w o, ready src i w o → ready src (transitionInput i)
      (fun j => transitionTape (w j)) (transitionTape o) := by
    intro i w o h
    obtain ⟨he,hw,ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (h.1 ▸ (word_parked src).read_ne_start)
      (fun j => (ready_parked src h j).read_ne_start) h.2.2.2.2.parked.read_ne_start
    simpa only [he,hw,ho] using h
  have hv : value src ≤ FormulaHeaderPreparation.cap src := by
    apply FormulaHeaderRegisters.value_bound src.length _ _
      (FormulaHeaderPreparation.occurrences_bound src)
    have hm := FormulaMaximumRestore.value_bound src
    simpa [FormulaHeaderPreparation.maximum] using Nat.add_le_add_right hm 1
  have h := seqTM_hoareTime _ _ (prepare_hoare src) hs (finish_hoare src)
  exact h.mono_bound (by unfold bound; nlinarith)

/-- The first canonical source field is now emitted from ordinary formula input. -/
theorem decoded_header (φ : SAT.CNF) :
    machine.HoareTime (initial φ.encode)
      (fun i _w o => i = word φ.encode ∧
        OutAcc (BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits) o)
      (bound φ.encode) := by
  have h := ordinary_hoare φ.encode
  have he : value φ.encode = (FormulaPACEncoding.table φ).entities := by
    obtain ⟨_,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
    have hc := congrArg List.length ho
    simp only [FormulaTokenCount.countBits,List.length_replicate] at hc
    have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
    simpa only [value,FormulaHeaderPreparation.maximum,FormulaHeaderPreparation.occurrences,
      FormulaMaximumFrame.value,FormulaWiring.varCount,hm,hc] using
      FormulaHeaderRegisters.formula_value φ
  apply h.consequence
  · intro i w o hi; exact hi
  · rintro i w o ⟨hi,_,_,_,ho⟩
    exact ⟨hi,by simpa only [he] using ho⟩
  · omega

end UnconstrainedPACDetection.FormulaEntityHeader
