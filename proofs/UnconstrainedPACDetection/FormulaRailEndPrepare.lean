module

public import proofs.UnconstrainedPACDetection.FormulaUniqueHead

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailEndPrepare
open Complexity Complexity.TM
open FormulaRailHeadPrepare (bank parked)

def machine : TM 17 := seqTM (setConstTM 6 20)
  (seqTM (setConstTM 11 1) (seqTM (mulAddIntoTM 0 6 11)
    (seqTM (addIntoTM 5 11) (copyIntoTM 0 6))))

theorem hoare (i v j r a b f L V M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (h20 : 20 ≤ M) (hiM : i ≤ M) (hv : v ≤ M) (hj : j ≤ M) (hb : b ≤ M)
    (hbase : 20*i+v+1 ≤ M) :
    machine.HoareTime (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank i v i r a (20*i+v+1) f L V) ys) (5*opBudget M+4) := by
  have h0 := (setConstTM_hoareTime (6 : Fin 17) 20 j inp (bank i v j r a b f L V) ys hi
    (parked _ _ _ _ _ _ _ _ _) rfl).mono_bound (setConstTM_le_opBudget h20 hj)
  have he0 : Function.update (bank i v j r a b f L V) 6 (regTape 20) = bank i v 20 r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (setConstTM_hoareTime (11 : Fin 17) 1 b inp (bank i v 20 r a b f L V) ys hi
    (parked _ _ _ _ _ _ _ _ _) rfl).mono_bound (setConstTM_le_opBudget (by omega) hb)
  have he1 : Function.update (bank i v 20 r a b f L V) 11 (regTape 1) = bank i v 20 r a 1 f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (mulAddIntoTM_hoareTime (0 : Fin 17) 6 11 (by decide) (by decide) (by decide)
    i 20 1 inp (bank i v 20 r a 1 f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl rfl).mono_bound
    (mulAddIntoTM_le_opBudget hiM h20 (by omega : 1+i*20 ≤ M))
  have he2 : Function.update (bank i v 20 r a 1 f L V) 11 (regTape (1+i*20)) =
      bank i v 20 r a (20*i+1) f L V := by
    have he : 1+i*20 = 20*i+1 := by omega
    rw [he]
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (addIntoTM_hoareTime (5 : Fin 17) 11 (by decide) v (20*i+1) inp
    (bank i v 20 r a (20*i+1) f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound
    (addIntoTM_le_opBudget hv (by omega : 20*i+1+v ≤ M))
  have he3 : Function.update (bank i v 20 r a (20*i+1) f L V) 11 (regTape (20*i+1+v)) =
      bank i v 20 r a (20*i+v+1) f L V := by
    have he : 20*i+1+v = 20*i+v+1 := by omega
    rw [he]
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h4 := (copyIntoTM_hoareTime (0 : Fin 17) 6 (by decide) i 20 inp
    (bank i v 20 r a (20*i+v+1) f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hiM h20)
  have he4 : Function.update (bank i v 20 r a (20*i+v+1) f L V) 6 (regTape i) =
      bank i v i r a (20*i+v+1) f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h34
  have h1234 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h234
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h1234).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailEndPrepare
