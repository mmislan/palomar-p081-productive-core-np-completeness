module

public import proofs.UnconstrainedPACDetection.FormulaRailTailCandidates

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailSuccessorPrepare
open Complexity Complexity.TM
open FormulaRailHeadPrepare (bank parked)

def machine : TM 17 := seqTM (incRegTM 6)
  (seqTM (copyIntoTM 10 11) (seqTM (incRegTM 11) (copyIntoTM 5 14)))

theorem hoare (i v r a b f L V M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hiM : i ≤ M) (hv : v ≤ M) (ha : a ≤ M) (hb : b ≤ M) (hf : f ≤ M) :
    machine.HoareTime (EmitPred inp (bank i v i r a b f L V) ys)
      (EmitPred inp (bank i v (i+1) r a (a+1) v L V) ys) (4*opBudget M+3) := by
  have h0 := (incRegTM_hoareTime (6 : Fin 17) i inp (bank i v i r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget hiM)
  have he0 : Function.update (bank i v i r a b f L V) 6 (regTape (i+1)) = bank i v (i+1) r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (copyIntoTM_hoareTime (10 : Fin 17) 11 (by decide) a b inp
    (bank i v (i+1) r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget ha hb)
  have he1 : Function.update (bank i v (i+1) r a b f L V) 11 (regTape a) = bank i v (i+1) r a a f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (incRegTM_hoareTime (11 : Fin 17) a inp (bank i v (i+1) r a a f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget ha)
  have he2 : Function.update (bank i v (i+1) r a a f L V) 11 (regTape (a+1)) =
      bank i v (i+1) r a (a+1) f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (copyIntoTM_hoareTime (5 : Fin 17) 14 (by decide) v f inp
    (bank i v (i+1) r a (a+1) f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hv hf)
  have he3 : Function.update (bank i v (i+1) r a (a+1) f L V) 14 (regTape v) =
      bank i v (i+1) r a (a+1) v L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailSuccessorPrepare
