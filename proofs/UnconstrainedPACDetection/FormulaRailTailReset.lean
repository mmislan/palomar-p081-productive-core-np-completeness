module

public import proofs.UnconstrainedPACDetection.FormulaRailTailStaging

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailReset
open Complexity Complexity.TM
open FormulaRailHeadPrepare (bank parked)

def machine : TM 17 := seqTM (clearRegTM 0) (seqTM (clearRegTM 6)
  (seqTM (clearRegTM 10) (seqTM (clearRegTM 11) (clearRegTM 14))))

theorem hoare (i v j r a b f L V M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hiM : i ≤ M) (hj : j ≤ M) (ha : a ≤ M) (hb : b ≤ M) (hf : f ≤ M) :
    machine.HoareTime (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank 0 v 0 r 0 0 0 L V) ys) (5*opBudget M+4) := by
  have h0 := (clearRegTM_hoareTime (0 : Fin 17) i inp (bank i v j r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hiM)
  have he0 : Function.update (bank i v j r a b f L V) 0 (regTape 0) = bank 0 v j r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (clearRegTM_hoareTime (6 : Fin 17) j inp (bank 0 v j r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hj)
  have he1 : Function.update (bank 0 v j r a b f L V) 6 (regTape 0) = bank 0 v 0 r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (clearRegTM_hoareTime (10 : Fin 17) a inp (bank 0 v 0 r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget ha)
  have he2 : Function.update (bank 0 v 0 r a b f L V) 10 (regTape 0) = bank 0 v 0 r 0 b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (clearRegTM_hoareTime (11 : Fin 17) b inp (bank 0 v 0 r 0 b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hb)
  have he3 : Function.update (bank 0 v 0 r 0 b f L V) 11 (regTape 0) = bank 0 v 0 r 0 0 f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h4 := (clearRegTM_hoareTime (14 : Fin 17) f inp (bank 0 v 0 r 0 0 f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hf)
  have he4 : Function.update (bank 0 v 0 r 0 0 f L V) 14 (regTape 0) = bank 0 v 0 r 0 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h34
  have h1234 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h234
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h1234).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailReset
