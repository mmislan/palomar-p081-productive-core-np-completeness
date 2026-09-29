module

public import proofs.IrrRAFEnumeration.CompletionQueryAddresses
public import proofs.IrrRAFEnumeration.CompletionSelectedScan

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

theorem selectedLiterals_eq_filter (sign : Bool) (inp : Tape) (pos index count : Nat)
    (bits : Fin count → Bool)
    (hbits : ∀ i, inp.cells (pos+i.val) = Γ.ofBool (bits i)) :
    selectedLiterals sign inp pos index count =
      ((List.finRange count).filter bits).map (fun i => (⟨sign,index+i.val⟩ : SAT.Lit)) := by
  rw [selectedLiterals_eq_flatMap]
  have he : (List.range count).flatMap (fun i => selectedLiteral sign inp (pos+i) (index+i)) =
      (List.finRange count).flatMap (fun i =>
        if bits i then [⟨sign,index+i.val⟩] else []) := by
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

/-- Addresses refer directly to the original two-header CRS encoding. -/
theorem original_incidence_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (s : Slot d r) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (d+r+3+(slotCode d r s).val) =
      Γ.ofBool (incidence Q C (Equiv.refl _) (Equiv.refl _) s) := by
  have h := block_cell (List.replicate d true ++ [false] ++
      List.replicate r true ++ [false]) []
    (fun i => incidence Q C (Equiv.refl _) (Equiv.refl _) ((slotCode d r).symm i))
    (slotCode d r s)
  have he : (List.replicate d true ++ [false] ++
      List.replicate r true ++ [false]).length+(slotCode d r s).val+1 =
      d+r+3+(slotCode d r s).val := by simp; omega
  rw [he] at h
  unfold inputBits
  rw [List.append_nil] at h
  rw [Equiv.symm_apply_apply] at h
  exact h

def catalystStart (d r j : Nat) := d+r+3+d+3*d*j+2*d

theorem original_catalyst_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) (x : Fin d) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (catalystStart d r j.val+x.val) = Γ.ofBool (decide (C x j)) := by
  have h := original_incidence_cell Q C (.inr (j,2,x))
  have ha : d+r+3+(slotCode d r (.inr (j,2,x))).val =
      catalystStart d r j.val+x.val := by
    simp [catalystStart, slotCode, finSumFinEquiv, finProdFinEquiv]
    ring
  have hi : incidence Q C (Equiv.refl _) (Equiv.refl _) (.inr (j,2,x)) =
      decide (C x j) := by rfl
  rw [ha, hi] at h
  exact h

theorem catalyst_selectedLiterals {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) :
    selectedLiterals true (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
      (catalystStart d r j.val) (r+d*d) d =
      PositiveCompletionCNF.positive (PositiveCompletionCNF.members
        (fun x => C x j) (PositiveCompletionCNF.rowVar r ⟨d,by omega⟩)) := by
  have h := selectedLiterals_eq_filter true
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (catalystStart d r j.val) (r+d*d) d (fun x => decide (C x j))
    (original_catalyst_cell Q C j)
  unfold PositiveCompletionCNF.positive PositiveCompletionCNF.members
    PositiveCompletionCNF.rowVar
  rw [List.map_map]
  convert h using 1
  have hp :
      (fun x : Fin d => decide ((fun y => C y j) x)) =
      (fun x : Fin d => decide (C x j)) := by
    funext x
    exact decide_eq_decide.mpr Iff.rfl
  rw [hp]
  apply congrArg (fun f : Fin d → SAT.Lit =>
    List.map f ((List.finRange d).filter (fun x => decide (C x j))))
  funext x
  rfl

def catalystWork (count pos index antecedent : Nat) : Fin 5 → Tape :=
  frameWork (m := 1) (maskWork (regTape count) pos index 0) (fun _ => regTape antecedent)

theorem catalystWork_parked (count pos index antecedent : Nat) :
    ∀ i, Parked (catalystWork count pos index antecedent i) := by
  intro i
  fin_cases i <;> simp only [catalystWork,frameWork,maskWork] <;> exact parked_regTape _

/-- The negative selected-reaction literal is followed by one disjunction of
final-row catalysts. A reaction with no catalyst is therefore forbidden. -/
def catalystClauseTM : TM 5 :=
  seqTM (emitLitTM false 4) ((selectedClauseTM true).liftTM 1)

theorem catalystClauseTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r) (ys : List Bool) :
    catalystClauseTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystWork d (catalystStart d r j.val) (r+d*d) j.val) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystWork d (catalystStart d r j.val+d) (r+d*d+d) j.val)
        (ys++SAT.CNF.encode [PositiveCompletionCNF.implies
          (PositiveCompletionCNF.selectVar j) (PositiveCompletionCNF.members
            (fun x => C x j) (PositiveCompletionCNF.rowVar r ⟨d,by omega⟩))]))
      (3*j.val+d*(5*catalystStart d r j.val+5*(r+d*d)+10*d+53)+d+16) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let pos := catalystStart d r j.val
  let index := r+d*d
  let zs := ys++([false,false]++List.replicate (2*j.val) true++[false,true])
  have hp : Parked inp := parkedInput_parked _
  have hw := catalystWork_parked d pos index j.val
  have h1 := emitLitTM_hoareTime false (4 : Fin 5) j.val inp
    (catalystWork d pos index j.val) ys hp (fun i _ => hw i)
    (by simpa [catalystWork,frameWork] using reg_regT j.val)
  have hs := selectedClauseTM_correct true inp pos index d zs hp rfl rfl
  have h2 := liftTM_frame_correct (selectedClauseTM true) 1 (fun _ => regTape j.val)
    (fun _ _ => parked_regTape _) inp inp
    (maskWork (regTape d) pos index 0) (maskWork (regTape d) (pos+d) (index+d) 0)
    zs (zs++SAT.CNF.encode [selectedLiterals true inp pos index d])
    (d*(5*pos+5*index+10*d+53)+d+6) hs
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h2
  have he : zs++SAT.CNF.encode [selectedLiterals true inp pos index d] =
      ys++SAT.CNF.encode [PositiveCompletionCNF.implies
        (PositiveCompletionCNF.selectVar j) (PositiveCompletionCNF.members
          (fun x => C x j) (PositiveCompletionCNF.rowVar r ⟨d,by omega⟩))] := by
    dsimp [inp,pos,index]
    rw [catalyst_selectedLiterals]
    simp [zs,PositiveCompletionCNF.implies,PositiveCompletionCNF.selectVar,
      SAT.CNF.encode_cons,SAT.Clause.encode_cons',List.append_assoc]
  rw [he] at h
  have h' := h.mono_bound (by omega :
    (3*j.val+9)+1+(d*(5*pos+5*index+10*d+53)+d+6) ≤
      3*j.val+d*(5*pos+5*index+10*d+53)+d+16)
  unfold EmitPred at h' ⊢
  dsimp only [catalystClauseTM, catalystWork, inp, pos, index] at h' ⊢
  exact h'

end IrrRAFEnumeration.CompletionQuery
