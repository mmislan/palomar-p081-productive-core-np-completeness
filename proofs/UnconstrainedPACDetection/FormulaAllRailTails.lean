module

public import proofs.UnconstrainedPACDetection.FormulaRailTailReentrant

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllRailTails
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open VerifierPairRestore (word word_parked)

def frame (v r L V C : Nat) (fuel : Tape) : Fin 21 → Tape :=
  FormulaChangingFrame.extend (FormulaSwitchVariableHeads.extend
    (FormulaRailClauseHeads.extend (FormulaRailTailReentrant.frame v r L V) C)) fuel

theorem parked (v r L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame v r L V C fuel t) :=
  FormulaChangingFrame.parked _ _ (FormulaSwitchVariableHeads.extend_parked _
    (FormulaRailClauseHeads.extend_parked _ _ (FormulaRailTailReentrant.frame_parked _ _ _ _))) hf

def body (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM (placeWorkTM 0 3 (FormulaRailTailReentrant.signs right plan)) (incRegTM 5)

theorem body_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (frame (v.val+1) (index r) (levels φ) (varCount φ) φ.length fuel)
        (ys ++ FormulaRailTailReentrant.bits φ v right r))
      (2*FormulaRailTailReentrant.budget φ+2*v.val+6) := by
  have hs := FormulaRailTailReentrant.signs_hoare φ v right r ys
  have h0 := FormulaPairExecution.place_hoare _ 0 3 _ _
    (frame v.val (index r) (levels φ) (varCount φ) φ.length fuel) _ _ _
    (parked _ _ _ _ _ _ hf) (by intro t; fin_cases t <;> rfl) hs
  have h1 := incRegTM_hoareTime (5 : Fin 21) v.val (word φ.encode)
    (frame v.val (index r) (levels φ) (varCount φ) φ.length fuel)
    (ys ++ FormulaRailTailReentrant.bits φ v right r) (word_parked _)
    (fun t _ => parked _ _ _ _ _ _ hf t) rfl
  have he : Function.update (frame v.val (index r) (levels φ) (varCount φ) φ.length fuel)
      5 (regTape (v.val+1)) = frame (v.val+1) (index r) (levels φ) (varCount φ) φ.length fuel := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank]
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ hf) _) h1).mono_bound (by omega)

def fields (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k < varCount φ then FormulaRailTailReentrant.bits φ ⟨k,hk⟩ right r else []

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (fields φ right r)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 := forRegTM (body right plan) 20

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) (levels φ) (varCount φ) φ.length (regTape (varCount φ))) ys)
      (EmitPred (word φ.encode) (frame (varCount φ) (index r) (levels φ) (varCount φ) φ.length (regTape (varCount φ)))
        (ys ++ bits φ right r (varCount φ)))
      (varCount φ*(2*FormulaRailTailReentrant.budget φ+2*varCount φ+8)+(varCount φ+2)) := by
  let V := varCount φ
  let w := fun k => frame k (index r) (levels φ) V φ.length (regTape V)
  let zs := fun k => ys ++ bits φ right r k
  have h := forRegTM_hoareTime (body right (choose right (tag r) none none)) (20 : Fin 21) V
    (word φ.encode) w zs (2*FormulaRailTailReentrant.budget φ+2*V+6) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells V⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 20 fuel = frame z (index r) (levels φ) V φ.length fuel := by
        funext t; fin_cases t <;> simp [w,frame,FormulaChangingFrame.extend]
      have hb := body_hoare φ ⟨k,hk⟩ right r fuel hf (zs k)
      have heq : fields φ right r k = FormulaRailTailReentrant.bits φ ⟨k,hk⟩ right r := by
        unfold fields; rw [dite_eq_left hk]
      have hy : zs (k+1) = zs k ++ FormulaRailTailReentrant.bits φ ⟨k,hk⟩ right r := by
        simp [zs,bits,List.range_succ,List.flatMap_append,heq,List.append_assoc]
      rw [he,he,hy]
      exact hb.mono_bound (by omega))
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,V,Nat.add_assoc] using h

def prepare : TM 21 := seqTM (clearRegTM 5) (copyIntoTM 16 20)

theorem prepare_hoare (v r L V C f : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    prepare.HoareTime (EmitPred inp (frame v r L V C (regTape f)) ys)
      (EmitPred inp (frame 0 r L V C (regTape V)) ys) (2*v+2*f+2*V^2+7*V+12) := by
  have h0 := clearRegTM_hoareTime (5 : Fin 21) v inp (frame v r L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ (parked_regTape _) t) rfl
  have he0 : Function.update (frame v r L V C (regTape f)) 5 (regTape 0) = frame 0 r L V C (regTape f) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := copyIntoTM_hoareTime (16 : Fin 21) 20 (by decide) V f inp (frame 0 r L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ (parked_regTape _) t) rfl rfl
  have he1 : Function.update (frame 0 r L V C (regTape f)) 20 (regTape V) = frame 0 r L V C (regTape V) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition hi (parked _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by nlinarith)

def prepared (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 := seqTM prepare (machine right plan)

theorem prepared_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (v f : Nat) (ys : List Bool) :
    (prepared right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame v (index r) (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (frame (varCount φ) (index r) (levels φ) (varCount φ) φ.length (regTape (varCount φ)))
        (ys ++ bits φ right r (varCount φ)))
      (2*v+2*f+2*(varCount φ)^2+7*varCount φ+13+
        varCount φ*(2*FormulaRailTailReentrant.budget φ+2*varCount φ+8)+(varCount φ+2)) := by
  have h0 := prepare_hoare v (index r) (levels φ) (varCount φ) φ.length f (word φ.encode) (word_parked _) ys
  have h1 := canonical_hoare φ right r ys
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaAllRailTails
