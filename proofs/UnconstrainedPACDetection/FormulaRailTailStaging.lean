module

public import proofs.UnconstrainedPACDetection.FormulaRailTailBlock

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailStaging
open Complexity Complexity.TM
open FormulaWiring (levels varCount)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaRailHeadVariables (extend extend_parked)
open FormulaVariableTailBound (cap)

def core (s : Bool) : TM 17 := seqTM (FormulaRailBaseRegisters.machine s)
  (seqTM (copyIntoTM 11 10) (seqTM (clearRegTM 0) (seqTM (clearRegTM 6) (copyIntoTM 5 14))))

theorem core_hoare (i v j r a b f L V M : Nat) (s : Bool) (inp : Tape)
    (hi : Parked inp) (ys : List Bool) (hiM : i ≤ M) (hv : v ≤ M) (hj : j ≤ M)
    (ha : a ≤ M) (hb : b ≤ M) (hf : f ≤ M) (hL : L ≤ M) (hV : V ≤ M)
    (hbase : FormulaRailBase.value L V v s ≤ M) :
    (core s).HoareTime (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank 0 v 0 r (FormulaRailBase.value L V v s)
        (FormulaRailBase.value L V v s) v L V) ys) (44*(opBudget M+1)) := by
  let A := FormulaRailBase.value L V v s
  have h0 := FormulaRailBaseRegisters.arithmetic_hoare L V v b M s inp
    (bank i v j r a b f L V) ys hi (parked _ _ _ _ _ _ _ _ _) rfl rfl rfl rfl hL hV hv hb hbase
  have he0 : FormulaRailBaseRegisters.bank (bank i v j r a b f L V) A = bank i v j r a A f L V := by
    funext t; fin_cases t <;> simp [FormulaRailBaseRegisters.bank,bank]
  change _ = _ at he0
  rw [he0] at h0
  have h1 := (copyIntoTM_hoareTime (11 : Fin 17) 10 (by decide) A a inp
    (bank i v j r a A f L V) ys hi (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget hbase ha)
  have he1 : Function.update (bank i v j r a A f L V) 10 (regTape A) = bank i v j r A A f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (clearRegTM_hoareTime (0 : Fin 17) i inp (bank i v j r A A f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hiM)
  have he2 : Function.update (bank i v j r A A f L V) 0 (regTape 0) = bank 0 v j r A A f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (clearRegTM_hoareTime (6 : Fin 17) j inp (bank 0 v j r A A f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hj)
  have he3 : Function.update (bank 0 v j r A A f L V) 6 (regTape 0) = bank 0 v 0 r A A f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h4 := (copyIntoTM_hoareTime (5 : Fin 17) 14 (by decide) v f inp (bank 0 v 0 r A A f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hv hf)
  have he4 : Function.update (bank 0 v 0 r A A f L V) 14 (regTape v) = bank 0 v 0 r A A v L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h34
  have h1234 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h234
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h1234).mono_bound (by omega)

def machine (s : Bool) : TM 18 := seqTM (placeWorkTM 0 1 (core s)) (copyIntoTM 15 17)

theorem hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s : Bool) (i j r a b f g : Nat) (ys : List Bool)
    (hi : i ≤ cap φ) (hj : j ≤ cap φ) (ha : a ≤ cap φ) (hb : b ≤ cap φ)
    (hf : f ≤ cap φ) (hg : g ≤ cap φ) :
    (machine s).HoareTime
      (EmitPred (word φ.encode) (extend (bank i v.val j r a b f (levels φ) (varCount φ)) (regTape g)) ys)
      (EmitPred (word φ.encode) (FormulaRailTailLoop.bank 0 v.val r
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s)
        (levels φ) (varCount φ) (regTape (levels φ))) ys) (45*(opBudget (cap φ)+1)) := by
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hv := v.isLt
  have hLc : levels φ ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have hvc : v.val ≤ cap φ := by omega
  have h0 := core_hoare i v.val j r a b f (levels φ) (varCount φ) (cap φ) s
    (word φ.encode) (word_parked _) ys hi hvc hj ha hb hf hLc hVc (FormulaVariableTailBound.base_bound φ v s)
  have h0' := FormulaRailHeadVariables.lift_hoare _ _ _ _ (regTape g) _ _ _
    (parked _ _ _ _ _ _ _ _ _) (parked_regTape _) h0
  let A := FormulaRailBase.value (levels φ) (varCount φ) v.val s
  let w := extend (bank 0 v.val 0 r A A v.val (levels φ) (varCount φ)) (regTape g)
  have h1 := (copyIntoTM_hoareTime (15 : Fin 18) 17 (by decide) (levels φ) g
    (word φ.encode) w ys (word_parked _)
    (fun t _ => extend_parked _ _ (parked _ _ _ _ _ _ _ _ _) (parked_regTape _) t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget hLc hg)
  have he : Function.update w 17 (regTape (levels φ)) = FormulaRailTailLoop.bank 0 v.val r A
      (levels φ) (varCount φ) (regTape (levels φ)) := by
    funext t; fin_cases t <;> simp [w,FormulaRailTailLoop.bank,extend,bank]
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0'
    (emitPred_transition (word_parked _) (extend_parked _ _ (parked _ _ _ _ _ _ _ _ _) (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailStaging
