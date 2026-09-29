module

public import proofs.IrrRAFEnumeration.CompletionFiringFamily
public import proofs.IrrRAFEnumeration.CompletionStrideScan

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

theorem strideLiterals_eq_filter (sign : Bool) (stride : Nat) (inp : Tape)
    (pos index count : Nat) (bits : Fin count → Bool)
    (hbits : ∀ i, inp.cells (pos+i.val*stride) = Γ.ofBool (bits i)) :
    strideLiterals sign stride inp pos index count =
      ((List.finRange count).filter bits).map (fun i => (⟨sign,index+i.val⟩ : SAT.Lit)) := by
  rw [strideLiterals_eq_flatMap]
  have he : (List.range count).flatMap (fun i => selectedLiteral sign inp (pos+i*stride) (index+i)) =
      (List.finRange count).flatMap (fun i => if bits i then [⟨sign,index+i.val⟩] else []) := by
    change ((List.range count).map _).flatten = ((List.finRange count).map _).flatten
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hic : i < count := by simpa using hi
      have hb := hbits ⟨i,hic⟩
      simp only [List.getElem_map,List.getElem_range,List.getElem_finRange]
      unfold selectedLiteral
      rw [hb]
      cases hbit : bits ⟨i,hic⟩ <;> simp [Γ.ofBool,hbit]
  rw [he]
  have hf (xs : List (Fin count)) :
      xs.flatMap (fun i => if bits i then [⟨sign,index+i.val⟩] else []) =
        (xs.filter bits).map (fun i => (⟨sign,index+i.val⟩ : SAT.Lit)) := by
    induction xs with
    | nil => rfl
    | cons i xs ih => cases h : bits i <;> simp [h,ih]
  exact hf _

def outputStart (d r x : Nat) := d+r+3+d+d+x

theorem original_output_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (x : Fin d) (j : Fin r) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (outputStart d r x.val+j.val*(3*d)) = Γ.ofBool (decide (x ∈ Q.outputs j)) := by
  have h := original_incidence_cell Q C (.inr (j,1,x))
  have ha : d+r+3+(slotCode d r (.inr (j,1,x))).val =
      outputStart d r x.val+j.val*(3*d) := by
    simp [outputStart,slotCode,finSumFinEquiv,finProdFinEquiv]
    ring
  have hi : incidence Q C (Equiv.refl _) (Equiv.refl _) (.inr (j,1,x)) =
      decide (x ∈ Q.outputs j) := by rfl
  rw [ha,hi] at h
  exact h

theorem output_strideLiterals {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i x : Fin d) :
    strideLiterals true (3*d) (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
      (outputStart d r x.val) (firingBase d r i.val) r =
      PositiveCompletionCNF.positive (PositiveCompletionCNF.members
        (fun j => x ∈ Q.outputs j) (PositiveCompletionCNF.fireVar d i)) := by
  have h := strideLiterals_eq_filter true (3*d)
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (outputStart d r x.val) (firingBase d r i.val) r (fun j => decide (x ∈ Q.outputs j))
    (original_output_cell (decC := decC) Q C x)
  unfold PositiveCompletionCNF.positive PositiveCompletionCNF.members
    PositiveCompletionCNF.fireVar firingBase
  rw [List.map_map]
  have hf : r+(d+1)*d+i.val*r = firingBase d r i.val := by
    unfold firingBase
    ring
  rw [hf]
  exact h

def supportClause {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i x : Fin d) : SAT.Clause :=
  PositiveCompletionCNF.implies (PositiveCompletionCNF.rowVar r ⟨i.val+1,by omega⟩ x)
    (PositiveCompletionCNF.rowVar r ⟨i.val,by omega⟩ x ::
      PositiveCompletionCNF.members (fun j => x ∈ Q.outputs j) (PositiveCompletionCNF.fireVar d i))

def supportWork (count stride pos fire antecedent previous : Nat) : Fin 7 → Tape :=
  frameWork (m := 2) (strideWork stride (regTape count) pos fire 0)
    (fun k => if k = 5 then regTape antecedent else regTape previous)

theorem supportWork_parked (count stride pos fire antecedent previous : Nat) :
    ∀ k, Parked (supportWork count stride pos fire antecedent previous k) := by
  intro k
  fin_cases k <;> simp only [supportWork,frameWork,strideWork] <;> exact parked_regTape _

def supportClauseTM : TM 7 :=
  seqTM (emitLitTM false 5) (seqTM (emitLitTM true 6) ((strideClauseTM true).liftTM 2))

def supportClauseBudget (d r i x : Nat) :=
  3*(r+(i+1)*d+x)+3*(r+i*d+x)+
    r*(strideStepBudget (3*d) (outputStart d r x+r*(3*d)) (firingBase d r i+r)+2)+r+26

theorem supportClauseTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i x : Fin d) (ys : List Bool) :
    supportClauseTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportWork r (3*d) (outputStart d r x.val) (firingBase d r i.val)
          (r+(i.val+1)*d+x.val) (r+i.val*d+x.val)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportWork r (3*d) (outputStart d r x.val+r*(3*d)) (firingBase d r i.val+r)
          (r+(i.val+1)*d+x.val) (r+i.val*d+x.val))
        (ys++SAT.CNF.encode [supportClause Q i x]))
      (supportClauseBudget d r i.val x.val) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := outputStart d r x.val
  let f := firingBase d r i.val
  let a := r+(i.val+1)*d+x.val
  let v := r+i.val*d+x.val
  let w := supportWork r (3*d) p f a v
  change supportClauseTM.HoareTime
    (EmitPred inp (supportWork r (3*d) p f a v) ys)
    (EmitPred inp (supportWork r (3*d) (p+r*(3*d)) (f+r) a v)
      (ys++SAT.CNF.encode [supportClause Q i x]))
    (supportClauseBudget d r i.val x.val)
  let zs := ys++([false,false]++List.replicate (2*a) true++[false,true])
  let ts := zs++([true,true]++List.replicate (2*v) true++[false,true])
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ k, Parked (w k) := supportWork_parked _ _ _ _ _ _
  have h1 := emitLitTM_hoareTime false (5 : Fin 7) a inp w ys hp (fun k _ => hw k)
    (by simpa [w,supportWork,frameWork] using reg_regT a)
  have h2 := emitLitTM_hoareTime true (6 : Fin 7) v inp w zs hp (fun k _ => hw k)
    (by simpa [w,supportWork,frameWork] using reg_regT v)
  have hs := strideClauseTM_correct true (3*d) inp p f r ts hp rfl rfl
  let extra : Fin 7 → Tape := fun k => if k = 5 then regTape a else regTape v
  have he : ∀ k, 5 ≤ k.val → Parked (extra k) := by
    intro k _
    by_cases hk : k = 5 <;> simp only [extra,hk,↓reduceIte] <;> exact parked_regTape _
  have h3 := liftTM_frame_correct (strideClauseTM true) 2 extra he inp inp
    (strideWork (3*d) (regTape r) p f 0) (strideWork (3*d) (regTape r) (p+r*(3*d)) (f+r) 0)
    ts (ts++SAT.CNF.encode [strideLiterals true (3*d) inp p f r])
    (r*(strideStepBudget (3*d) (p+r*(3*d)) (f+r)+2)+r+6) hs
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw ts) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h23
  have ho : ts++SAT.CNF.encode [strideLiterals true (3*d) inp p f r] =
      ys++SAT.CNF.encode [supportClause Q i x] := by
    dsimp [inp,p,f]
    rw [output_strideLiterals (decC := decC)]
    simp [ts,zs,supportClause,PositiveCompletionCNF.implies,PositiveCompletionCNF.positive,
      PositiveCompletionCNF.rowVar,a,v,SAT.CNF.encode_cons,SAT.Clause.encode_cons',List.append_assoc]
  rw [ho] at h
  have h' := h.mono_bound (by omega :
    (3*a+9)+1+((3*v+9)+1+(r*(strideStepBudget (3*d) (p+r*(3*d)) (f+r)+2)+r+6)) ≤
      3*a+3*v+r*(strideStepBudget (3*d) (p+r*(3*d)) (f+r)+2)+r+26)
  unfold EmitPred at h' ⊢
  dsimp only [supportClauseTM,supportClauseBudget,supportWork,extra,w,p,f,a,v] at h' ⊢
  simpa only [Fin.isValue, ↓reduceIte] using h'

end IrrRAFEnumeration.CompletionQuery
