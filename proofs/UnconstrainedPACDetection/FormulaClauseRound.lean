module

public import proofs.UnconstrainedPACDetection.FormulaClauseCompare
public import proofs.UnconstrainedPACDetection.FormulaReactionFinish

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseRound
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bank (i c target : Nat) (raw : List Bool) : Fin 5 → Tape :=
  ![regTape i,regTape c,word raw,regTape target,word []]

theorem parked (i c target : Nat) (raw : List Bool) : ∀ j, Parked (bank i c target raw j) := by
  intro j; fin_cases j
  · exact parked_regTape _
  · exact parked_regTape _
  · exact word_parked _
  · exact parked_regTape _
  · exact word_parked _

def lookup : TM 5 := placeWorkTM 0 2 FormulaClauseLookup.machine

theorem lookup_hoare (src : List Bool) (i target : Nat) (ys : List Bool) :
    lookup.HoareTime (EmitPred (word src) (bank i 0 target []) ys)
      (EmitPred (word src) (bank i (FormulaClauseLookup.result src i).clauses target
        (FormulaClauseLookup.result src i).raw) ys) (5*src.length+21) := by
  rintro inp w out ⟨hin,hw,ho⟩
  subst inp; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaClauseLookup.lookup_hoare src i ys
    (word src) (FormulaClauseLookup.bank i 0 []) out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaClauseLookup.machine
    0 2 (bank i 0 target []) hr (by intro j _; exact (parked i 0 target [] j).read_ne_start)
  refine ⟨placeWorkCfg _ 0 2 (bank i 0 target []) d,t,ht,?_,hh,hdi,?_,hdo⟩
  · unfold lookup
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j; fin_cases j <;>
      simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,bank,FormulaClauseLookup.bank,hdw]

def offset (exit : Bool) : TM 5 := if exit then incRegTM 1 else skipTM

theorem offset_hoare (exit : Bool) (i c target : Nat) (raw ys : List Bool)
    (inp : Tape) (hi : Parked inp) :
    (offset exit).HoareTime (EmitPred inp (bank i c target raw) ys)
      (EmitPred inp (bank i (c+if exit then 1 else 0) target raw) ys) (2*c+5) := by
  cases exit
  · exact (skipTM_hoareTime inp (bank i c target raw) ys hi (parked i c target raw)).mono_bound (by omega)
  · have h := incRegTM_hoareTime (1 : Fin 5) c inp (bank i c target raw) ys hi
      (fun j _ => parked i c target raw j) rfl
    have he : Function.update (bank i c target raw) 1 (regTape (c+1)) =
        bank i (c+1) target raw := by
      funext j; fin_cases j <;> simp [bank]
    rw [he] at h
    exact h.mono_bound (by omega)

def permutation : Equiv.Perm (Fin 5) := (Equiv.swap 2 3).trans (Equiv.swap 2 4)
def placed : TM 5 := placeWorkTM 1 0 FormulaClauseCompare.machine
def compare : TM 5 := VerifierWorkPermutation.machine placed permutation

theorem compare_hoare (i c target : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    compare.HoareTime (EmitPred inp (bank i c target raw) ys)
      (EmitPred inp (bank i c target raw) (ys ++ [decide (c=target) && !raw.isEmpty]))
      (3*max c target+20) := by
  rintro inp' w out ⟨hin,hw,ho⟩
  subst inp'; subst w
  let base : Fin 5 → Tape := fun j => bank i c target raw (permutation j)
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaClauseCompare.compare_hoare c target raw ys inp hi
    inp (FormulaClauseCompare.bank c target raw) out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaClauseCompare.machine
    1 0 base hr (by intro j _; exact (parked i c target raw (permutation j)).read_ne_start)
  have routed := VerifierWorkPermutation.run_commute placed permutation hs
  refine ⟨VerifierWorkPermutation.wrap placed permutation (placeWorkCfg _ 1 0 base d),
    t,ht,?_,hh,hdi,?_,hdo⟩
  · unfold compare
    convert routed using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;>
        simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
          base,permutation,Equiv.trans_apply,Equiv.swap_apply_def,bank,FormulaClauseCompare.bank]
    · rfl
  · funext j; fin_cases j <;>
      simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        base,permutation,Equiv.trans_apply,Equiv.swap_apply_def,bank,FormulaClauseCompare.bank,hdw]

def clean : TM 5 := seqTM (clearRegTM 1) (VerifierTapeCleanup.machine 2)

theorem clean_hoare (i c target : Nat) (raw ys : List Bool) (inp : Tape) (hi : Parked inp) :
    clean.HoareTime (EmitPred inp (bank i c target raw) ys)
      (EmitPred inp (bank i 0 target []) ys) (2*c+2*raw.length+14) := by
  have hfirst := clearRegTM_hoareTime (1 : Fin 5) c inp (bank i c target raw) ys hi
    (fun j _ => parked i c target raw j) rfl
  have he : Function.update (bank i c target raw) 1 (regTape 0) = bank i 0 target raw := by
    funext j; fin_cases j <;> simp [bank]
  rw [he] at hfirst
  have hsecond := FormulaReactionFinish.cleanup_emit (2 : Fin 5) raw ys inp
    (bank i 0 target raw) hi (parked i 0 target raw) rfl
  have h := seqTM_hoareTime _ _ hfirst (emitPred_transition hi (parked i 0 target raw) ys) hsecond
  have he' : Function.update (bank i 0 target raw) 2 (word []) = bank i 0 target [] := by
    funext j; fin_cases j <;> simp [bank]
  rw [he'] at h
  exact h.mono_bound (by change 2*c+4+1+(1+2*raw.length+8) ≤ _; omega)

def finish (exit : Bool) : TM 5 := seqTM (offset exit) (seqTM compare clean)
def machine (exit : Bool) : TM 5 := seqTM lookup (finish exit)
def verdict (src : List Bool) (i target : Nat) (exit : Bool) : Bool :=
  decide ((FormulaClauseLookup.result src i).clauses+(if exit then 1 else 0)=target) &&
    !(FormulaClauseLookup.result src i).raw.isEmpty

theorem finish_hoare (exit : Bool) (i c target : Nat) (raw ys : List Bool)
    (inp : Tape) (hi : Parked inp) :
    (finish exit).HoareTime (EmitPred inp (bank i c target raw) ys)
      (EmitPred inp (bank i 0 target [])
        (ys ++ [decide (c+(if exit then 1 else 0)=target) && !raw.isEmpty]))
      (4*c+2*raw.length+3*max (c+1) target+43) := by
  have ho := offset_hoare exit i c target raw ys inp hi
  have hc := compare_hoare i (c+if exit then 1 else 0) target raw ys inp hi
  have he := clean_hoare i (c+if exit then 1 else 0) target raw
    (ys ++ [decide (c+(if exit then 1 else 0)=target) && !raw.isEmpty]) inp hi
  have hce := seqTM_hoareTime _ _ hc (emitPred_transition hi (parked _ _ _ _) _) he
  have h := seqTM_hoareTime _ _ ho (emitPred_transition hi (parked _ _ _ _) _) hce
  have hd : (if exit then 1 else 0 : Nat) ≤ 1 := by cases exit <;> decide
  have hm : max (c+if exit then 1 else 0) target ≤ max (c+1) target :=
    max_le_max (by omega) le_rfl
  exact h.mono_bound (by omega)

theorem operation_hoare (src : List Bool) (i target : Nat) (exit : Bool) (ys : List Bool) :
    (machine exit).HoareTime (EmitPred (word src) (bank i 0 target []) ys)
      (EmitPred (word src) (bank i 0 target []) (ys ++ [verdict src i target exit]))
      (20*src.length+6*target+100) := by
  have h := seqTM_hoareTime _ _ (lookup_hoare src i target ys)
    (emitPred_transition (word_parked src) (parked _ _ _ _) ys)
    (finish_hoare exit i (FormulaClauseLookup.result src i).clauses target
      (FormulaClauseLookup.result src i).raw ys (word src) (word_parked src))
  have hc := FormulaBlockingCleanup.count_bound src i
  have hl := FormulaLookupRouting.raw_length_bound src i
  have hm : max ((FormulaClauseLookup.result src i).clauses+1) target ≤
      src.length+2+target := by dsimp [FormulaClauseLookup.result]; apply max_le <;> omega
  exact h.mono_bound (by dsimp [FormulaClauseLookup.result] at *; omega)

theorem decoded_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (target : Nat) (exit : Bool) (ys : List Bool) :
    (machine exit).HoareTime (EmitPred (word φ.encode) (bank i.val 0 target []) ys)
      (EmitPred (word φ.encode) (bank i.val 0 target [])
        (ys ++ [FormulaClauseLookup.clauseMatch (FormulaClauseLookup.result φ.encode i.val) target exit]))
      (20*φ.encode.length+6*target+100) := by
  have he : verdict φ.encode i.val target exit =
      FormulaClauseLookup.clauseMatch (FormulaClauseLookup.result φ.encode i.val) target exit := by
    rw [FormulaClauseLookup.guarded_match]
    apply Bool.eq_iff_iff.mpr
    simp only [verdict,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨fun ⟨he,hp⟩ => ⟨hp,he.symm⟩,fun ⟨hp,he⟩ => ⟨he.symm,hp⟩⟩
  simpa only [he] using operation_hoare φ.encode i.val target exit ys

end UnconstrainedPACDetection.FormulaClauseRound
