module

public import proofs.IrrRAFEnumeration.CompletionBasePreparation

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- A source in the immutable eleven-register dimension/address bank. -/
def bankSource (q : Fin 11) : Fin 23 := ⟨12+q.val,by omega⟩
def scratchReg (q : Fin 12) : Fin 23 := ⟨q.val,by omega⟩

def baseLoadValue (v : Fin 23 → Nat) (s : Fin 12 → Option (Fin 11)) (q : Fin 12) : Nat :=
  match s q with
  | none => 0
  | some j => v (bankSource j)

def baseLoadStage (v : Fin 23 → Nat) (s : Fin 12 → Option (Fin 11)) (k : Nat)
    (q : Fin 23) : Nat :=
  if h : q.val < 12 ∧ q.val < k then baseLoadValue v s ⟨q.val,h.1⟩ else v q

def baseLoadOp (s : Fin 12 → Option (Fin 11)) (q : Fin 12) : BaseRegOp :=
  match s q with
  | none => .set (scratchReg q) 0
  | some j => .copy (bankSource j) (scratchReg q)

def baseLoadTM (s : Fin 12 → Option (Fin 11)) : TM 23 :=
  bigSeqTM ((List.finRange 12).map (fun q => (baseLoadOp s q).machine))

theorem baseLoadStage_bound (v : Fin 23 → Nat) (s : Fin 12 → Option (Fin 11))
    (k M : Nat) (hv : ∀ i, v i ≤ M) (q : Fin 23) : baseLoadStage v s k q ≤ M := by
  unfold baseLoadStage
  split
  · unfold baseLoadValue
    split
    · exact Nat.zero_le _
    · exact hv _
  · exact hv _

theorem baseLoadOp_valid (s : Fin 12 → Option (Fin 11)) (q : Fin 12) :
    (baseLoadOp s q).valid := by
  unfold baseLoadOp
  split
  · trivial
  · simp only [BaseRegOp.valid]
    intro h
    have hh := congrArg Fin.val h
    simp only [bankSource,scratchReg] at hh
    omega

theorem baseLoadStage_step (v : Fin 23 → Nat) (s : Fin 12 → Option (Fin 11))
    (q : Fin 12) :
    (baseLoadOp s q).eval (baseLoadStage v s q.val) = baseLoadStage v s (q.val+1) := by
  funext i
  by_cases hi : i = scratchReg q
  · subst i
    cases hs : s q <;>
      simp [baseLoadOp,hs,BaseRegOp.eval,baseLoadStage,baseLoadValue,scratchReg,bankSource]
  · have hn : i.val ≠ q.val := by
      intro he
      apply hi
      exact Fin.ext he
    cases hs : s q <;>
      simp only [baseLoadOp,hs,BaseRegOp.eval,Function.update_of_ne hi]
    all_goals
      unfold baseLoadStage
      have he : (i.val < 12 ∧ i.val < q.val) ↔ (i.val < 12 ∧ i.val < q.val+1) := by omega
      simp only [he]

theorem baseLoadTM_correct (v : Fin 23 → Nat) (s : Fin 12 → Option (Fin 11))
    (M : Nat) (hv : ∀ i, v i ≤ M) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (baseLoadTM s).HoareTime (EmitPred inp (baseRegWork v) ys)
      (EmitPred inp (baseRegWork (baseLoadStage v s 12)) ys)
      (12*(opBudget M+1)+1) := by
  have h := bigSeqTM_hoareTime
    ((List.finRange 12).map (fun q => (baseLoadOp s q).machine)) inp
    (fun k => baseRegWork (baseLoadStage v s k)) (fun _ => ys) (opBudget M)
    hp (fun _ _ => parked_regTape _) (by
      intro k hk
      have hk12 : k < 12 := by simpa using hk
      simp only [List.getElem_map,List.getElem_finRange,Fin.cast_mk]
      rw [← baseLoadStage_step v s ⟨k,hk12⟩]
      apply BaseRegOp.correct
      · exact baseLoadStage_bound v s k M hv
      · change ∀ i, (baseLoadOp s ⟨k,hk12⟩).eval (baseLoadStage v s k) i ≤ M
        rw [baseLoadStage_step v s ⟨k,hk12⟩]
        exact baseLoadStage_bound v s (k+1) M hv
      · exact baseLoadOp_valid s _
      · exact hp)
  have hz : baseLoadStage v s 0 = v := by
    funext i
    simp [baseLoadStage]
  simpa only [baseLoadTM,List.length_map,List.length_finRange,hz] using h

/-- Reload tables for nonempty, food, firing, support, final inputs, final catalysts. -/
def baseLoadSources (phase : Fin 6) : Fin 12 → Option (Fin 11) :=
  match phase.val with
  | 0 => ![some 1,none,none,none,none,none,none,none,none,none,none,none]
  | 1 => ![some 0,some 6,some 1,none,none,none,none,none,none,none,none,none]
  | 2 => ![some 0,some 7,some 1,none,some 4,some 1,some 1,none,some 7,some 0,none,none]
  | 3 => ![some 1,some 8,some 4,none,some 10,some 2,some 1,some 0,some 8,some 4,some 8,some 0]
  | 4 => ![some 0,some 7,some 5,none,none,some 1,some 5,none,none,none,none,none]
  | _ => ![some 0,some 9,some 5,none,none,some 1,some 5,none,none,none,none,none]

end IrrRAFEnumeration.CompletionQuery
